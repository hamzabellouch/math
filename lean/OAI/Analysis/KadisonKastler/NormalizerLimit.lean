import OAI.Analysis.KadisonKastler.WeakCPDescent
import OAI.Analysis.KadisonKastler.ConjugateFactor

namespace OAI

/-! # Recovering a normalizer from weak limits of conjugations

The smoothing argument supplies exact normalizers close to moving linear
maps. Only the latter maps need to converge. A weak limit of the actual
conjugations is UCP and has range in the original algebra; the complete
error bound then gives a nearby exact normalizer.
-/

namespace KadisonKastler

open Filter
open scoped CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*}

local instance normalizerLimitFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance normalizerLimitFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

section MovingLimit

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {l : Filter ι} [l.NeBot]

/-- A complete bound survives when both compared maps vary and converge
only on individual weak operator coefficients. -/
theorem complete_bound_of_two_weak_limits
    (F R : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
    (hF : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x))))
    (hR : ∀ a x y, Tendsto (fun i => inner ℂ y (R i a x)) l
      (𝓝 (inner ℂ y (ρ a x))))
    {e : ℝ} (he : 0 ≤ e) (hclose : ∀ i, CompletelyBoundedBy (F i - R i) e) :
    CompletelyBoundedBy (S - ρ) e := by
  have ht : ∀ a x y, Tendsto (fun i => inner ℂ y ((F i - R i) a x)) l
      (𝓝 (inner ℂ y ((S - ρ) a x))) := by
    intro a x y
    simpa only [LinearMap.sub_apply, sub_apply, inner_sub_right] using
      (hF a x y).sub (hR a x y)
  have hb := complete_bound_of_pointwise_weak_limit (fun i => F i - R i)
    (S - ρ) 0 ht he (fun i => by simpa only [sub_zero] using hclose i)
  simpa only [sub_zero] using hb

end MovingLimit

/-- The modular smoothing limit step. The comparison maps may be neither
positive nor multiplicative. The exact conjugations supply positivity and
range membership, while the comparison maps supply the limit representation. -/
theorem exists_normalizer_of_weak_comparison
    (P : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W P))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W P)) H)
    (ω : Ultrafilter ι) (V : ι → unitary (H →L[ℂ] H))
    (hV : ∀ i, Conjugates (V i) P P)
    (R : ι → Algebra P →ₗ[ℂ] (H →L[ℂ] H))
    (hR : ∀ a x y, Tendsto (fun i => inner ℂ y (R i a x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (unitaryConj W a x))))
    {e g : ℝ} (he : 0 ≤ e) (hesmall : e < 1 / 1000)
    (hge : g + e < 1) (hgap : kkDistance (unitaryConjugateAlgebra W P) P < g)
    (hclose : ∀ i, CompletelyBoundedBy
      ((unitaryConjugationLinear (V i)).comp (algebraInclusion P).toAlgHom.toLinearMap -
        R i) e) :
    ∃ n : unitary (H →L[ℂ] H), Conjugates n P P ∧
      ‖(n : H →L[ℂ] H) - (W : H →L[ℂ] H)‖ ≤ 128 * e := by
  let Q := unitaryConjugateAlgebra W P
  let j : Algebra Q →⋆ₐ[ℂ] Algebra P := (unitaryConjugateEquiv W P).symm.toStarAlgHom
  let ρ (i : ι) : Algebra Q →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (V i)).toStarAlgHom.comp
      ((algebraInclusion P).comp j)
  let F (i : ι) : Algebra Q →CP (H →L[ℂ] H) :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (ρ i)
  obtain ⟨S, hS, ht⟩ := exists_unitalCP_weak_ultralimit ω F (fun i => map_one (ρ i))
  have hmem (x : Algebra Q) : S x ∈ P := by
    apply Generator.Tracial.weak_operator_limit_mem (l := (ω : Filter ι)) P (fun i =>
      (⟨F i x, (hV i).subset ⟨j x, (j x).property, rfl⟩⟩ : Algebra P)) (S x)
    exact ht x
  let L : Algebra Q →ₗ[ℂ] Algebra P :=
    S.toLinearMap.codRestrict P.toStarSubalgebra.toSubmodule hmem
  let φ : Algebra Q →CP Algebra P :=
    completelyPositive_of_embedding (algebraInclusion P) Subtype.val_injective S L
      (fun _ => rfl)
  have hφ : φ 1 = 1 := Subtype.ext hS
  have hj (x : Algebra Q) : unitaryConj W (j x) = (x : H →L[ℂ] H) := by
    have h := congrArg Subtype.val ((unitaryConjugateEquiv W P).apply_symm_apply x)
    exact h
  have hR' : ∀ a x y, Tendsto (fun i => inner ℂ y ((R i).comp j.toAlgHom.toLinearMap a x))
      (ω : Filter ι) (𝓝 (inner ℂ y ((algebraInclusion Q) a x))) := by
    intro a x y
    change Tendsto (fun i => inner ℂ y (R i (j a) x)) (ω : Filter ι)
      (𝓝 (inner ℂ y ((a : H →L[ℂ] H) x)))
    rw [← hj a]
    exact hR (j a) x y
  have hcl (i : ι) : CompletelyBoundedBy
      ((F i).toLinearMap - (R i).comp j.toAlgHom.toLinearMap) e := by
    have hb := completelyBoundedBy_comp_completeIsometry _ j.toAlgHom.toLinearMap
      (hclose i) (injective_starAlgHom_completelyIsometric j
        (unitaryConjugateEquiv W P).symm.injective)
    exact hb
  have hbound := complete_bound_of_two_weak_limits (fun i => (F i).toLinearMap)
    (fun i => (R i).comp j.toAlgHom.toLinearMap) S.toLinearMap
    (algebraInclusion Q).toAlgHom.toLinearMap ht hR' he hcl
  obtain ⟨q, hq, hqn⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant
    φ hφ he hesmall hge hbound hgap
  refine ⟨q * W, (conjugates_unitaryConjugateAlgebra W P).trans hq, ?_⟩
  have hd : ((q * W : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - W =
      ((q : H →L[ℂ] H) - 1) * W := by
    simp only [Submonoid.coe_mul, sub_mul, one_mul]
  rw [hd, CStarRing.norm_mul_coe_unitary]
  exact hqn

end

end KadisonKastler

end OAI
