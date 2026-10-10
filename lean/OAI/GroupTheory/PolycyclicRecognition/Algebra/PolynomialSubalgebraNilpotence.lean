import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraFiltration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialIdealCongruence
import Mathlib.GroupTheory.Nilpotent

namespace OAI

/-! # Group nilpotence of the concrete BCH subgroups

The intrinsic Lie lower central series is a sequence of actual subgroups.
The finite-difference formula puts every group commutator one step deeper.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialLieIdealSubgroup (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K) : Subgroup K where
  carrier := J
  one_mem' := by
    have h : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [h]
    exact J.zero_mem
  inv_mem' := by
    intro x hx
    have h : x⁻¹ = -x := Subtype.ext (P.inv_eq_neg x)
    rw [h]
    exact J.neg_mem hx
  mul_mem' := by
    intro x y hx hy
    let a : J := ⟨x, hx⟩
    let b : J := ⟨y, hy⟩
    let z : J := finiteDynkinPolynomial P.coefficients ![a, b]
    have hz : (z : K) = x * y := by
      have hh := finiteDynkinPolynomial_map J.toLieSubalgebra.incl P.coefficients ![a, b]
      change (z : K) = _ at hh
      rw [polynomialSubalgebra_mul_eq]
      convert hh using 1
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact z.property

instance polynomialLieIdealSubgroup_normal (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K) :
    (polynomialLieIdealSubgroup K J).Normal where
  conj_mem x hx v := polynomialSubalgebra_conjugate_mem K J x hx v

theorem polynomialSubalgebra_commutator_mem (K : LieSubalgebra ℝ L)
    (v x : K) (k : ℕ) (hx : x ∈ lowerCentralSeries ℝ K K k) :
    v * x * v⁻¹ * x⁻¹ ∈ lowerCentralSeries ℝ K K (k + 1) := by
  have hd := polynomialSubalgebra_inner_difference K v k x hx
  have hp := polynomialSubalgebra_mul_difference K (k + 1) (v * x * v⁻¹) x⁻¹ x x⁻¹ hd (by simp)
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  simp only [mul_inv_cancel, hone, sub_zero, sub_self, add_zero] at hp
  have hh := (lowerCentralSeries ℝ K K (k + 1)).add_mem
    ((antitone_lowerCentralSeries ℝ K K (Nat.le_succ (k + 1))) hp) hd
  change v * x * v⁻¹ * x⁻¹ ∈ (lowerCentralSeries ℝ K K (k + 1)).toSubmodule
  simpa only [sub_add_cancel] using hh

theorem group_lowerCentral_le_lie (K : LieSubalgebra ℝ L) (k : ℕ) :
    (⊤ : Subgroup K).lowerCentralSeries k ≤
      polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k) := by
  induction k with
  | zero =>
    intro x _
    change x ∈ lowerCentralSeries ℝ K K 0
    simp
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro v _ x hx
    change v * x * v⁻¹ * x⁻¹ ∈ lowerCentralSeries ℝ K K (k + 1)
    exact polynomialSubalgebra_commutator_mem K v x k (ih hx)

theorem polynomialSubalgebra_group_nilpotent (K : LieSubalgebra ℝ L)
    [LieRing.IsNilpotent K] : Group.IsNilpotent K := by
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ K K).mp
    (inferInstance : LieModule.IsNilpotent K K)
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨c, eq_bot_iff.mpr ?_⟩
  intro x hx
  have hh := group_lowerCentral_le_lie K c hx
  change x ∈ lowerCentralSeries ℝ K K c at hh
  rw [hc] at hh
  have hx0 : x = 0 := hh
  change x = 1
  exact hx0.trans (Subtype.ext P.one_eq_zero).symm

end PolycyclicRecognition

end

end OAI
