import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Jacobsthal.Harmonic.FourierL1

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def nonzeroFrequencies (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.filter (· ≠ 0)

noncomputable def intervalLength (P : ProgressionInterval) : ℝ := P.right-P.left

noncomputable def l1Norm (N : ℕ) [NeZero N] (P : ProgressionInterval) : ℝ :=
  ∑ h ∈ nonzeroFrequencies N, ‖P.weight N h‖

noncomputable def gcdL1Norm (N : ℕ) [NeZero N] (P : ProgressionInterval) : ℝ :=
  ∑ h ∈ nonzeroFrequencies N, ‖P.weight N h‖*Real.sqrt (Nat.gcd h.val N)

theorem l1Norm_nonneg (N : ℕ) [NeZero N] (P : ProgressionInterval) : 0 ≤ l1Norm N P := by
  unfold l1Norm
  positivity

theorem gcdL1Norm_nonneg (N : ℕ) [NeZero N] (P : ProgressionInterval) : 0 ≤ gcdL1Norm N P := by
  unfold gcdL1Norm
  positivity

theorem l1Norm_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    l1Norm N P ≤ (2*ErdosHyperbola.harmonicConstant)*(N : ℝ)*Real.log (2*(N : ℝ)) :=
  ErdosHyperbola.intervalWeight_l1 N P.left P.right P.leftClosed P.rightClosed P.step P.residue P.step_pos hP

theorem gcdL1Norm_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    gcdL1Norm N P ≤ (2*ErdosHyperbola.harmonicConstant)*(N : ℝ)*(N.divisors.card : ℝ)*
      Real.log (2*(N : ℝ)) :=
  ErdosHyperbola.intervalWeight_gcd_l1 N P.left P.right P.leftClosed P.rightClosed P.step P.residue P.step_pos hP

theorem intervalLength_nonneg (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    0 ≤ intervalLength P := sub_nonneg.mpr hP

theorem weight_zero_eq_count (N : ℕ) [NeZero N] (P : ProgressionInterval) :
    P.weight N 0 = (P.points.card : ℂ) :=
  ErdosHyperbolaFourier.intervalWeight_zero N P.left P.right P.leftClosed P.rightClosed P.step P.residue

theorem interval_count_error (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    |(P.points.card : ℝ)-intervalLength P/(P.step : ℝ)| ≤ 1 :=
  ErdosHyperbolaFourier.progressionPoints_count_error P.left P.right hP P.leftClosed P.rightClosed
    P.step P.residue P.step_pos

theorem interval_average_le_length (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    intervalLength P/(P.step : ℝ) ≤ intervalLength P := by
  have hs : (0 : ℝ) < P.step := by exact_mod_cast P.step_pos
  have hs1 : (1 : ℝ) ≤ P.step := by exact_mod_cast P.step_pos
  apply (div_le_iff₀ hs).mpr
  exact le_mul_of_one_le_right (intervalLength_nonneg P hP) hs1

theorem interval_count_le_length_add_one (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    (P.points.card : ℝ) ≤ intervalLength P+1 := by
  have h := (abs_le.mp (interval_count_error P hP)).2
  have hu := interval_average_le_length P hP
  linarith

theorem norm_weight_zero_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    ‖P.weight N 0‖ ≤ intervalLength P+1 := by
  rw [weight_zero_eq_count]
  simpa using interval_count_le_length_add_one P hP

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem unit_mul_eq_iff {R : Type*} [CommRing R] (u : Rˣ) (x y : R) :
    (u : R)*x = y ↔ x = (↑u⁻¹ : R)*y := by
  constructor
  · intro h
    have hh := congrArg (fun z : R => (↑u⁻¹ : R)*z) h
    rw [Units.inv_mul_cancel_left] at hh
    exact hh
  · intro h
    rw [h, Units.mul_inv_cancel_left]

noncomputable def inverseResidue (T l : ℕ) (hlT : l.Coprime T) (r : ℤ) : ℤ :=
  (((↑(ZMod.unitOfCoprime l hlT)⁻¹ : ZMod T)*(r : ZMod T)).val : ℕ)

theorem inverseResidue_cast (T l : ℕ) [NeZero T] (hlT : l.Coprime T) (r : ℤ) :
    (inverseResidue T l hlT r : ZMod T) =
      (↑(ZMod.unitOfCoprime l hlT)⁻¹ : ZMod T)*(r : ZMod T) := by
  simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem residue_dilation_iff (T l : ℕ) [NeZero T] (hlT : l.Coprime T) (r v : ℤ) :
    Int.ModEq (T : ℤ) v (inverseResidue T l hlT r) ↔ Int.ModEq (T : ℤ) ((l : ℤ)*v) r := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff, inverseResidue_cast,
    Int.cast_mul, Int.cast_natCast, ← ZMod.coe_unitOfCoprime l hlT]
  exact (unit_mul_eq_iff (ZMod.unitOfCoprime l hlT) (v : ZMod T) (r : ZMod T)).symm

noncomputable def pulledInterval (P : ProgressionInterval) (l : ℕ) (hlT : l.Coprime P.step) :
    ProgressionInterval where
  left := P.left/(l : ℝ)
  right := P.right/(l : ℝ)
  leftClosed := P.leftClosed
  rightClosed := P.rightClosed
  step := P.step
  residue := inverseResidue P.step l hlT P.residue
  step_pos := P.step_pos

theorem pulledInterval_length (P : ProgressionInterval) (l : ℕ) (hlT : l.Coprime P.step) :
    intervalLength (pulledInterval P l hlT) = intervalLength P/(l : ℝ) := by
  unfold intervalLength pulledInterval
  ring

theorem pulledInterval_ordered (P : ProgressionInterval) (hP : P.left ≤ P.right)
    (l : ℕ) (hl : 0 < l) (hlT : l.Coprime P.step) :
    (pulledInterval P l hlT).left ≤ (pulledInterval P l hlT).right :=
  div_le_div_of_nonneg_right hP (by exact_mod_cast hl.le)

theorem mem_pulledInterval_iff (P : ProgressionInterval) (l : ℕ) (hl : 0 < l)
    (hlT : l.Coprime P.step) (v : ℤ) :
    v ∈ (pulledInterval P l hlT).points ↔ ((l : ℤ)*v) ∈ P.points := by
  let : NeZero P.step := ⟨P.step_pos.ne'⟩
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  rw [mem_interval_points, mem_interval_points]
  dsimp only [pulledInterval]
  rw [residue_dilation_iff]
  by_cases hlc : P.leftClosed = true <;> by_cases hrc : P.rightClosed = true <;>
    simp [hlc, hrc, Int.cast_mul, Int.cast_natCast, div_le_iff₀ hlR, div_lt_iff₀ hlR,
      le_div_iff₀ hlR, lt_div_iff₀ hlR, mul_comm]

def dilatePair (l : ℕ) (xy : ℤ × ℤ) : ℤ × ℤ := ((l : ℤ)*xy.1,xy.2)

theorem dilatePair_injective (l : ℕ) (hl : 0 < l) : Function.Injective (dilatePair l) := by
  rintro ⟨x,y⟩ ⟨z,w⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext
  · exact mul_left_cancel₀ (by exact_mod_cast hl.ne' : (l : ℤ) ≠ 0) hx
  · exact hy

end ErdosHyperbolaError

end

end Erdos970

end OAI
