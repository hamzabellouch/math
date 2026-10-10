import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def jointAbsTest (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) : ℝ := by
  classical
  exact ∑ u : ι → (ZMod M)ˣ, if ∀ i, (u i : ZMod M)=a i then ‖F u‖ else 0

theorem jointAbsTest_nonneg (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) :
    0≤jointAbsTest F a := by
  classical
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem jointUnitTest_norm_le (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) :
    ‖jointUnitTest F a‖≤jointAbsTest F a := by
  classical
  unfold jointUnitTest jointAbsTest
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u _
  split_ifs <;> simp

theorem jointAbsTest_cast (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) :
    (jointAbsTest F a:ℂ)=jointUnitTest (fun u => (‖F u‖:ℂ)) a := by
  classical
  simp only [jointAbsTest,jointUnitTest,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp

def tupleWeight (N : ι → ℕ) (lo hi Z : ι → ℝ) (p : PrimeCellTuple N lo hi) : ℝ :=
  ∏ i, (Z i*((p i).val:ℝ))⁻¹

def jointAbsMass (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) : ℝ :=
  ∑ p : PrimeCellTuple N lo hi, tupleWeight N lo hi Z p*jointAbsTest F (fun i => ((p i).val:ZMod M))

omit [DecidableEq ι] in
theorem tupleWeight_nonneg [_decidableEqIndex : DecidableEq ι]
    (N : ι → ℕ) (lo hi Z : ι → ℝ) (hZ : ∀ i,0≤Z i)
    (p : PrimeCellTuple N lo hi) : 0≤tupleWeight N lo hi Z p :=
  Finset.prod_nonneg fun i _ => inv_nonneg.mpr (mul_nonneg (hZ i) (Nat.cast_nonneg _))

theorem jointAbsMass_cast (N : ι → ℕ) (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) :
    (jointAbsMass N M lo hi Z F:ℂ)=jointComplexTestSum N M lo hi Z (fun u => (‖F u‖:ℂ)) := by
  simp only [jointAbsMass,jointComplexTestSum,Complex.ofReal_sum,Complex.ofReal_mul,
    tupleWeight,Complex.ofReal_prod,jointAbsTest_cast]

theorem coefficient_norm_mass_le (N : ι → ℕ) (lo hi Z : ι → ℝ) (hZ : ∀ i,0≤Z i)
    (F : (ι → (ZMod M)ˣ) → ℂ) :
    (∑ p : PrimeCellTuple N lo hi,
      ‖(tupleWeight N lo hi Z p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M))‖) ≤
      jointAbsMass N M lo hi Z F := by
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tupleWeight_nonneg N lo hi Z hZ p)]
  exact mul_le_mul_of_nonneg_left (jointUnitTest_norm_le F _) (tupleWeight_nonneg N lo hi Z hZ p)

theorem jointAbsMass_le_of_error (N : ι → ℕ) (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) (main error : ℝ)
    (he : ‖jointComplexTestSum N M lo hi Z (fun u => (‖F u‖:ℂ))-
      (main:ℂ)*∑ u : ι → (ZMod M)ˣ,(‖F u‖:ℂ)‖ ≤ error*∑ u : ι → (ZMod M)ˣ,‖F u‖) :
    jointAbsMass N M lo hi Z F ≤ (main+error)*∑ u : ι → (ZMod M)ˣ,‖F u‖ := by
  rw [← jointAbsMass_cast,← Complex.ofReal_sum,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at he
  have hh := (le_abs_self _).trans he
  linarith

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
