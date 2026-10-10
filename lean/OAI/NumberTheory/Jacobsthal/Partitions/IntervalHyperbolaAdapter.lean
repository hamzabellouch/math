import OAI.NumberTheory.Jacobsthal.Estimates.RealProgressionPoints
import OAI.NumberTheory.Jacobsthal.Harmonic.HyperbolaFourier

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

theorem norm_characterProgression_le (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) (hs : step ≠ 0) :
    ‖characterProgression N start step J‖ ≤ (N : ℝ)/(cyclicDistance N step : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hd : (0 : ℝ) < cyclicDistance N step := by
    exact_mod_cast cyclicDistance_pos N step hs
  have hm := (mul_le_mul_of_nonneg_left (standard_character_chord_lower N step)
    (norm_nonneg (characterProgression N start step J))).trans
      (norm_characterProgression_mul_chord N start step J)
  have hm' : ‖characterProgression N start step J‖ * (4*(cyclicDistance N step : ℝ)) ≤
      2*(N : ℝ) := by
    apply (div_le_iff₀ hN).mp
    convert hm using 1; ring
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem characterProgression_modulus_one (start step : ZMod 1) (J : ℕ) :
    characterProgression 1 start step J = J := by
  have hs : start = 0 := Subsingleton.elim _ _
  have ht : step = 0 := Subsingleton.elim _ _
  rw [hs, ht, characterProgression_zero_step]
  simp

end ErdosHyperbolaFourier

end

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

noncomputable def intervalWeight (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) : ℂ :=
  ∑ z ∈ progressionPoints x y lc rc T a, ZMod.stdAddChar (-h*(z : ZMod N))

theorem intervalWeight_eq_progression (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    intervalWeight N h x y lc rc T a =
      characterProgression N (-h*(progressionPoint a T (lowerIndex x T a lc) : ZMod N))
        (-h*(T : ZMod N)) (upperIndex y T a rc-lowerIndex x T a lc).toNat := by
  unfold intervalWeight progressionPoints
  rw [Finset.sum_image]
  · rw [Int.Ico_eq_finset_map, Finset.sum_map]
    unfold characterProgression
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change -h * (((a+(T : ℤ)*(lowerIndex x T a lc+(i : ℤ)) : ℤ)) : ZMod N) =
      -h * (((a+(T : ℤ)*lowerIndex x T a lc : ℤ)) : ZMod N) +
        (i : ZMod N)*(-h*(T : ZMod N))
    push_cast
    ring
  · intro i _ j _ hij
    exact progressionPoint_injective a T hT hij

theorem intervalWeight_zero (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) :
    intervalWeight N 0 x y lc rc T a = (progressionPoints x y lc rc T a).card := by
  simp [intervalWeight]

theorem intervalWeight_zero_error (N : ℕ) [NeZero N] (x y : ℝ) (hxy : x ≤ y)
    (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    ‖intervalWeight N 0 x y lc rc T a - (((y-x)/(T : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [intervalWeight_zero]
  have h := progressionPoints_count_error x y hxy lc rc T a hT
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

theorem norm_intervalWeight_le (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T)
    (hs : -h*(T : ZMod N) ≠ 0) :
    ‖intervalWeight N h x y lc rc T a‖ ≤ (N : ℝ)/(cyclicDistance N (-h*(T : ZMod N)) : ℝ) := by
  rw [intervalWeight_eq_progression N h x y lc rc T a hT]
  exact norm_characterProgression_le N _ _ _ hs

theorem norm_intervalWeight_le_of_coprime (N : ℕ) [NeZero N] (h : ZMod N) (hh : h ≠ 0)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    ‖intervalWeight N h x y lc rc T a‖ ≤ (N : ℝ)/(cyclicDistance N (-h*(T : ZMod N)) : ℝ) := by
  have hunit : IsUnit (T : ZMod N) := (ZMod.isUnit_iff_coprime T N).mpr hTN
  apply norm_intervalWeight_le N h x y lc rc T a hT
  intro hs
  exact hh (neg_eq_zero.mp (hunit.mul_left_eq_zero.mp hs))

end ErdosHyperbolaFourier

end

section

namespace ErdosHyperbolaFourier

theorem progressionPoints_eq_literal_filter (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) :
    progressionPoints x y lc rc T a =
      (Finset.Icc ⌈x⌉ ⌊y⌋).filter (fun z : ℤ =>
        (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
        (if rc then (z : ℝ) ≤ y else (z : ℝ) < y) ∧ Int.ModEq (T : ℤ) z a) := by
  ext z
  rw [mem_progressionPoints_iff x y lc rc T a z hT, Finset.mem_filter, Finset.mem_Icc,
    Int.ceil_le, Int.le_floor]
  have hlo : (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) → x ≤ (z : ℝ) := by
    cases lc with
    | false => exact fun h => h.le
    | true => exact id
  have hhi : (if rc then (z : ℝ) ≤ y else (z : ℝ) < y) → (z : ℝ) ≤ y := by
    cases rc with
    | false => exact fun h => h.le
    | true => exact id
  constructor
  · intro h
    exact ⟨⟨hlo h.1, hhi h.2.1⟩, h⟩
  · exact fun h => h.2

theorem progressionPoints_open_singleton_empty (x : ℝ) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    progressionPoints x x false false T a = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  obtain ⟨hlo, hhi, _⟩ := (mem_progressionPoints_iff x x false false T a z hT).mp hz
  exact (lt_asymm hlo hhi)

theorem literal_filter_zero_weight (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) :
    intervalWeight N 0 x y lc rc T a =
      (((Finset.Icc ⌈x⌉ ⌊y⌋).filter (fun z : ℤ =>
        (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
        (if rc then (z : ℝ) ≤ y else (z : ℝ) < y) ∧ Int.ModEq (T : ℤ) z a)).card : ℂ) := by
  rw [intervalWeight_zero, progressionPoints_eq_literal_filter x y lc rc T a hT]

end ErdosHyperbolaFourier

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

structure ProgressionInterval where
  left : ℝ
  right : ℝ
  leftClosed : Bool
  rightClosed : Bool
  step : ℕ
  residue : ℤ
  step_pos : 0 < step

noncomputable def ProgressionInterval.points (P : ProgressionInterval) : Finset ℤ :=
  ErdosHyperbolaFourier.progressionPoints P.left P.right P.leftClosed P.rightClosed P.step P.residue

noncomputable def ProgressionInterval.weight (P : ProgressionInterval) (N : ℕ) [NeZero N]
    (h : ZMod N) : ℂ :=
  ErdosHyperbolaFourier.intervalWeight N h P.left P.right P.leftClosed P.rightClosed P.step P.residue

theorem mem_interval_points (P : ProgressionInterval) (x : ℤ) :
    x ∈ P.points ↔
      (if P.leftClosed then P.left ≤ (x : ℝ) else P.left < (x : ℝ)) ∧
      (if P.rightClosed then (x : ℝ) ≤ P.right else (x : ℝ) < P.right) ∧
      Int.ModEq (P.step : ℤ) x P.residue :=
  ErdosHyperbolaFourier.mem_progressionPoints_iff P.left P.right P.leftClosed P.rightClosed
    P.step P.residue x P.step_pos

theorem integerWeight_interval (N : ℕ) [NeZero N] (P : ProgressionInterval) (h : ZMod N) :
    integerWeight N P.points h = P.weight N h := rfl

theorem interval_count_eq_fourier (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval) :
    ((hyperbolaPairs N T a c P.points Q.points).card : ℂ) =
      (∑ h : ZMod N, ∑ k : ZMod N,
        P.weight N h * Q.weight N k * restrictedSum N T hT a c h k)/(N : ℂ)^2 := by
  simpa only [integerWeight_interval] using count_eq_fourier N T hT a c P.points Q.points

end ErdosHyperbolaIdentities

end

end Erdos970

end OAI
