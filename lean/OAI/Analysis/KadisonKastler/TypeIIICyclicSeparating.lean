import OAI.Analysis.KadisonKastler.CyclicOrbitRestriction
import OAI.Analysis.KadisonKastler.TypeIIISeparatingVector
import OAI.Analysis.KadisonKastler.TypeIIIMatrixCorner
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction
import OAI.Analysis.KadisonKastler.FactorSpatialSplit

namespace OAI

/-! # Cyclic separating vectors in the original type III representation

The cyclic restriction of a separating vector has an infinite commutant
corner: its modular conjugation carries a proper isometry into that
corner. Projection comparison then moves the cyclic subspace onto the
original Hilbert space, while preserving separation and the vector norm.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem ModularConjugationData.isometry_surjective_of_commutant_finite
    {M : VonNeumannAlgebra H} {ξ : H} (d : ModularConjugationData M ξ)
    (hf : ∀ w : Algebra M.commutant, star w * w = 1 → w * star w = 1)
    (v : Algebra M) (hv : star v * v = 1) : v * star v = 1 := by
  let J := d.conjugation
  let w : Algebra M.commutant := ⟨conjugationOperator J v.val,d.right_mem le_rfl v⟩
  have hw : star w * w = 1 := by
    apply Subtype.ext
    change star (conjugationOperator J v.val) * conjugationOperator J v.val = 1
    rw [← conjugationOperator_star J d.involutive,
      ← conjugationOperator_mul J d.involutive]
    rw [show star v.val * v.val = 1 from congrArg Subtype.val hv,
      conjugationOperator_one J d.involutive]
  have hww := congrArg Subtype.val (hf w hw)
  change conjugationOperator J v.val * star (conjugationOperator J v.val) = 1 at hww
  rw [← conjugationOperator_star J d.involutive,
    ← conjugationOperator_mul J d.involutive] at hww
  have he := congrArg (conjugationOperator J) hww
  rw [conjugationOperator_twice J d.involutive,
    conjugationOperator_one J d.involutive] at he
  exact Subtype.ext he

theorem cyclicOrbitProjection_not_finite [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (ξ : H) (hs : Function.Injective (algebraVectorMap M ξ))
    (v : Algebra M) (hv : star v * v = 1) (hproper : v * star v ≠ 1) :
    ¬ FiniteProjectionIn M.commutant
      ⟨(cyclicOrbitSpace M ξ).starProjection,cyclicOrbitProjection_mem M ξ⟩ := by
  intro hf
  obtain ⟨d,_⟩ := (publishedModularSpectralResolution (cyclicOrbitSpace M ξ)
    (cyclicOrbitAlgebra M ξ) (cyclicOrbitVector M ξ)
    (cyclicOrbitAlgebra_cyclic M ξ) (cyclicOrbitAlgebra_separating M ξ hs)).some
  have hfinite : ∀ w : Algebra (cyclicOrbitAlgebra M ξ).commutant,
      star w * w = 1 → w * star w = 1 := by
    rw [cyclicOrbitAlgebra_commutant]
    exact finite_representedCorner_of_finite_projection M.commutant
      (cyclicOrbitProjection_mem M ξ) hf
  let e := cyclicOrbitEquiv M ξ hs
  have hstar : e (star v) = star (e v) := e.map_star' v
  have hmul (a b : Algebra M) : e (a * b) = e a * e b := e.map_mul' a b
  have hone : e 1 = 1 := map_one e
  have hev : star (e v) * e v = 1 := by
    have he := congrArg e hv
    rwa [hmul,hstar,hone] at he
  have he := d.isometry_surjective_of_commutant_finite hfinite (e v) hev
  apply hproper
  have he' : e (v * star v) = e 1 := by
    rw [hmul,hstar,hone]
    exact he
  exact e.injective he'

theorem TypeIIIFactor.exists_cyclic_separating_unit_vector
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {M : VonNeumannAlgebra H} (hM : TypeIIIFactor M) :
    ∃ Ω : H, ‖Ω‖ = 1 ∧ DenseRange (algebraVectorMap M Ω) ∧
      Function.Injective (algebraVectorMap M Ω) := by
  obtain ⟨ξ,hξ,hs⟩ := hM.exists_separating_unit_vector
  obtain ⟨v,hv,hproper⟩ := hM.exists_proper_isometry
  let q : AlgebraProjection M.commutant :=
    ⟨⟨(cyclicOrbitSpace M ξ).starProjection,cyclicOrbitProjection_mem M ξ⟩,
      ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
        Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩
  have hq : ¬ FiniteProjectionIn M.commutant q.val :=
    cyclicOrbitProjection_not_finite M ξ hs v hv hproper
  have he := projection_equivalent_one_of_not_finite
    (scalarCenter_commutant M hM.factor) q hq
  obtain ⟨u,hu,hut⟩ := AlgebraProjection.equivalent_symm he
  let w : Algebra M.commutant := u.val
  have hw : star w * w = 1 := u.initial.trans (congrArg Subtype.val hu)
  have hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val := by
    have ht : w * star w = q.val := congrArg Subtype.val hut
    have ht' := congrArg Subtype.val ht
    change w.val * star w.val = (cyclicOrbitSpace M ξ).starProjection at ht'
    simpa only [vectorSupportProjection,VonNeumannAlgebra.commutant_commutant,
      cyclicOrbitSpace] using ht'
  have hp : (vectorSupportProjection M ξ).val = 1 := by
    apply hs
    change (vectorSupportProjection M ξ).val.val ξ = (1 : H →L[ℂ] H) ξ
    exact (vectorSupportProjection_apply M ξ).trans (one_apply_eq_self ξ).symm
  have hp' : (1 : H →L[ℂ] H) * star 1 = (vectorSupportProjection M ξ).val.val := by
    simp only [star_one,mul_one,hp,OneMemClass.coe_one]
  let Ω := star ((1 : Algebra M).val * w.val) ξ
  have hcyc : DenseRange (algebraVectorMap M Ω) :=
    support_transfer_cyclic M ξ 1 w hw hwq (by simp)
  have hsep : Function.Injective (algebraVectorMap M Ω) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply support_transfer_separating M ξ 1 w (by simp) hp'
      (by rw [hwq,vectorSupportProjection_apply]) (a-b)
    change a.val Ω - b.val Ω = 0
    exact sub_eq_zero.mpr hab
  have hn := support_transfer_norm M ξ 1 w (by simp) hw hp' hwq
  exact ⟨Ω,hn.trans hξ,hcyc,hsep⟩

end

end KadisonKastler

end OAI
