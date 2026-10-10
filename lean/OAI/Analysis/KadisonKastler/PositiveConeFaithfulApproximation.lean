import OAI.Analysis.KadisonKastler.PositiveConeProjectionSupport
import OAI.Analysis.KadisonKastler.StandardTypeIIIVector

namespace OAI

/-! # Faithful positive perturbations in the original Hilbert space

Adding a positive vector to a separating positive vector preserves
separation. A small positive multiple of the reference vector therefore
approximates any cone vector by cyclic separating cone vectors.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveApproximationRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hξ hpos in
theorem positiveCone_separating_add {η ζ : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hs : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M (η+ζ)) := by
  let q := vectorSupportProjection M (η+ζ)
  let p : AlgebraProjection M := ⟨1 - q.val,q.property.one_sub⟩
  have hp : p.val.val (η+ζ) = 0 := by
    change (η+ζ) - q.val.val (η+ζ) = 0
    rw [vectorSupportProjection_apply,sub_self]
  have hpη := (positiveCone_projection_kills_summands J hJ hright ξ hξ hpos hη hζ p hp).1
  have hp0 : p.val = 0 := hs (hpη.trans (map_zero (algebraVectorMap M η)).symm)
  have hq1 : q.val = 1 := by
    change 1 - q.val = 0 at hp0
    exact (sub_eq_zero.mp hp0).symm
  intro a b hab
  have hzero : (a-b).val (η+ζ) = 0 := by
    change a.val (η+ζ) - b.val (η+ζ) = 0
    exact sub_eq_zero.mpr hab
  have hm := mul_vectorSupport_eq_zero M (η+ζ) (a-b) hzero
  change (a-b).val * q.val.val = 0 at hm
  rw [hq1,OneMemClass.coe_one,mul_one] at hm
  exact sub_eq_zero.mp (Subtype.ext hm)

include hJ in
/-- For a conjugation exchanging the two algebras, a fixed separating
vector is cyclic on the same representation. -/
theorem cyclic_of_separating_of_conjugation_fixed
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    {η : H} (hη : J η = η) (hs : Function.Injective (algebraVectorMap M η)) :
    DenseRange (algebraVectorMap M η) := by
  have hsep' (b : Algebra M.commutant) (hb : b.val η = 0) : b = 0 := by
    let a : Algebra M := ⟨conjugationOperator J b.val,hleft b⟩
    have ha : a.val η = 0 := by
      change J (b.val (J η)) = 0
      rw [hη,hb,map_zero]
    have ha0 : a = 0 := hs (ha.trans (map_zero (algebraVectorMap M η)).symm)
    apply Subtype.ext
    have he := congrArg (fun c : Algebra M => conjugationOperator J c.val) ha0
    change conjugationOperator J (conjugationOperator J b.val) = conjugationOperator J 0 at he
    rw [conjugationOperator_twice J hJ] at he
    have hz : conjugationOperator J (0 : H →L[ℂ] H) = 0 := by
      ext x
      exact map_zero J
    rwa [hz] at he
  have hd := Generator.commutant_orbit_dense M.commutant η hsep'
  change Dense (Set.range (fun a : Algebra M.commutant.commutant => a.val η)) at hd
  rw [VonNeumannAlgebra.commutant_commutant] at hd
  exact hd

include hJ hright hξ hpos in
theorem exists_positiveCone_cyclic_separating_near
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (hs : Function.Injective (algebraVectorMap M ξ)) (hunit : ‖ξ‖ = 1)
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ : H, ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      DenseRange (algebraVectorMap M ζ) ∧ ‖ζ-η‖ < ε := by
  let r : ℝ := ε/2
  have hr : 0 < r := half_pos hε
  have hrξ : r • ξ ∈ modularPositiveCone (M := M) J ξ :=
    (modularPositiveCone J ξ).smul_mem hr (reference_mem_modularPositiveCone J hJ ξ)
  have hs' : Function.Injective (algebraVectorMap M (r • ξ)) := by
    intro a b hab
    apply hs
    change a.val ξ = b.val ξ
    have he : r • (a.val ξ) = r • (b.val ξ) := by
      change a.val (r • ξ) = b.val (r • ξ) at hab
      simpa only [ContinuousLinearMap.map_smul_of_tower] using hab
    exact (smul_right_injective H hr.ne') he
  let ζ := r • ξ + η
  have hζ : ζ ∈ modularPositiveCone (M := M) J ξ :=
    (modularPositiveCone J ξ).add_mem hrξ hη
  have hsep := positiveCone_separating_add J hJ hright ξ hξ hpos hrξ hη hs'
  refine ⟨ζ,hζ,hsep,cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hζ) hsep,?_⟩
  change ‖r • ξ + η - η‖ < ε
  rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hunit,mul_one]
  exact half_lt_self hε

end

end KadisonKastler

end OAI
