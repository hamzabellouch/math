import OAI.Analysis.KadisonKastler.TomitaGraphClosability
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Constructing a commutant operator from a bounded right vector

A bound on the map `a Ω ↦ a ξ` gives its continuous extension. Density
makes the extension commute with the represented algebra and unique.
This is the bounded-vector bridge for the modular commutant argument.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)

/-- Extension of right multiplication, whenever its algebra-vector bound holds. -/
def rightVectorOperator : H →L[ℂ] H :=
  (algebraVectorMap M ξ).extendOfNorm (algebraVectorMap M Ω)

variable (hcyc : DenseRange (algebraVectorMap M Ω))
  {C : ℝ} (hC : 0 ≤ C)
  (hbound : ∀ a : Algebra M, ‖a.val ξ‖ ≤ C * ‖a.val Ω‖)

include hcyc hbound in
@[simp] theorem rightVectorOperator_apply (a : Algebra M) :
    rightVectorOperator M Ω ξ (a.val Ω) = a.val ξ :=
  LinearMap.extendOfNorm_eq hcyc ⟨C, hbound⟩ a

include hcyc hC hbound in
theorem rightVectorOperator_norm_le : ‖rightVectorOperator M Ω ξ‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le hcyc hC hbound

include hcyc hbound in
theorem rightVectorOperator_vector : rightVectorOperator M Ω ξ Ω = ξ := by
  simpa only [OneMemClass.coe_one, one_apply_eq_self] using
    rightVectorOperator_apply M Ω ξ hcyc hbound (1 : Algebra M)

include hcyc hbound in
theorem rightVectorOperator_mem_commutant : rightVectorOperator M Ω ξ ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  apply ContinuousLinearMap.ext
  intro η
  let T := rightVectorOperator M Ω ξ
  apply hcyc.induction_on (p := fun η => (x * T) η = (T * x) η) η
  · exact isClosed_eq (x * T).continuous (T * x).continuous
  · intro a
    change x (rightVectorOperator M Ω ξ (a.val Ω)) =
      rightVectorOperator M Ω ξ ((x * a.val) Ω)
    rw [rightVectorOperator_apply M Ω ξ hcyc hbound a]
    exact (rightVectorOperator_apply M Ω ξ hcyc hbound (⟨x, hx⟩ * a)).symm

include hcyc in
/-- A commutant operator is determined by its value at a cyclic vector. -/
theorem commutant_operator_eq_of_vector {S T : H →L[ℂ] H}
    (hS : S ∈ M.commutant) (hT : T ∈ M.commutant) (he : S Ω = T Ω) : S = T := by
  apply ContinuousLinearMap.ext
  intro η
  apply hcyc.induction_on (p := fun η => S η = T η) η
  · exact isClosed_eq S.continuous T.continuous
  · intro a
    have hSa := congrArg (fun A : H →L[ℂ] H => A Ω)
      (VonNeumannAlgebra.mem_commutant_iff.mp hS a.val a.property)
    have hTa := congrArg (fun A : H →L[ℂ] H => A Ω)
      (VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property)
    change a.val (S Ω) = S (a.val Ω) at hSa
    change a.val (T Ω) = T (a.val Ω) at hTa
    exact hSa.symm.trans ((congrArg a.val he).trans hTa)

include hcyc hC in
/-- The right-vector estimate is equivalent to an actual bounded operator in the commutant. -/
theorem exists_commutant_operator_iff_vector_bound :
    (∃ T : H →L[ℂ] H, T ∈ M.commutant ∧ ‖T‖ ≤ C ∧ T Ω = ξ) ↔
      ∀ a : Algebra M, ‖a.val ξ‖ ≤ C * ‖a.val Ω‖ := by
  constructor
  · rintro ⟨T, hT, hnorm, hvec⟩ a
    have hc := congrArg (fun A : H →L[ℂ] H => A Ω)
      (VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property)
    change a.val (T Ω) = T (a.val Ω) at hc
    rw [hvec] at hc
    rw [hc]
    exact T.le_of_opNorm_le hnorm _
  · intro hb
    exact ⟨rightVectorOperator M Ω ξ,
      rightVectorOperator_mem_commutant M Ω ξ hcyc hb,
      rightVectorOperator_norm_le M Ω ξ hcyc hC hb,
      rightVectorOperator_vector M Ω ξ hcyc hb⟩

end

end KadisonKastler

end OAI
