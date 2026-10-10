import OAI.Analysis.KadisonKastler.WeakCPLimits
import OAI.Analysis.KadisonKastler.UCPDescent

namespace OAI

/-! # From finite coefficient approximations to an original-space unitary

The unitary family may vary freely with the finite tests. Its pointwise
weak ultralimit is UCP, retains the complete bound, and has range in the
neighboring von Neumann algebra. This is the limit step in Section 9.
-/

namespace KadisonKastler

open Filter
open scoped CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {M N : VonNeumannAlgebra H}

local instance limitFactorOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance limitFactorStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _

/-- Conjugations with a uniform displacement bound have the corresponding
uniform complete bound on every concrete subalgebra. -/
theorem complete_conjugation_restriction (u : unitary (H →L[ℂ] H)) :
    CompletelyBoundedBy
      ((unitaryConjugationLinear u).comp (algebraInclusion M).toAlgHom.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) (2 * ‖(u : H →L[ℂ] H) - 1‖) := by
  have h := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion M).toAlgHom.toLinearMap (complete_unitaryConjugation_sub_id u)
    (injective_starAlgHom_completelyIsometric (algebraInclusion M) Subtype.val_injective)
  exact h

/-- An arbitrarily varying family of nearby conjugations suffices, provided
each fixed coefficient is asymptotically approximated by the neighbor. -/
theorem concrete_unitary_of_weak_conjugations
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (ω : Ultrafilter ι) (U : ι → unitary (H →L[ℂ] H))
    {a g : ℝ} (ha : 0 ≤ a) (hU : ∀ i, ‖(U i : H →L[ℂ] H) - 1‖ ≤ a)
    (b : ι → Algebra M → Algebra N)
    (hb : ∀ x : Algebra M, ∀ ξ η : H,
      Tendsto (fun i => inner ℂ η
        (((b i x : H →L[ℂ] H) -
          (U i : H →L[ℂ] H) * (x : H →L[ℂ] H) * star (U i : H →L[ℂ] H)) ξ))
        (ω : Filter ι) (𝓝 0))
    (hsmall : 2 * a < 1 / 1000) (hge : g + 2 * a < 1)
    (hgap : kkDistance M N < g) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * a := by
  let ρ (i : ι) : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U i)).toStarAlgHom.comp
      (algebraInclusion M)
  let F (i : ι) : Algebra M →CP (H →L[ℂ] H) :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (ρ i)
  obtain ⟨S, hS, ht⟩ := exists_unitalCP_weak_ultralimit ω F (fun i => map_one (ρ i))
  have hmem (x : Algebra M) : S x ∈ N := by
    apply weak_limit_mem_of_weak_approximants N (fun i => F i x) (S x) (fun i => b i x)
      (ht x)
    exact hb x
  let L : Algebra M →ₗ[ℂ] Algebra N :=
    S.toLinearMap.codRestrict N.toStarSubalgebra.toSubmodule hmem
  let φ : Algebra M →CP Algebra N :=
    completelyPositive_of_embedding (algebraInclusion N) Subtype.val_injective S L
      (fun _ => rfl)
  have hφ : φ 1 = 1 := Subtype.ext hS
  have hF (i : ι) : CompletelyBoundedBy
      ((F i).toLinearMap - (algebraInclusion M).toAlgHom.toLinearMap) (2 * a) := by
    intro p q X
    exact (complete_conjugation_restriction (M := M) (U i) p q X).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hU i) (by norm_num))
        (norm_nonneg X))
  have hclose := complete_bound_of_pointwise_weak_limit (fun i => (F i).toLinearMap)
    S.toLinearMap (algebraInclusion M).toAlgHom.toLinearMap ht (by positivity) hF
  obtain ⟨u, hu, hnorm⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant φ hφ
    (by positivity) hsmall hge hclose hgap
  exact ⟨u, hu, by linarith⟩

end

end KadisonKastler

end OAI
