import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductIntervalLower
import OAI.NumberTheory.JointDickman.Counting.CoefficientDyadicBoxes

namespace OAI

/-! # A positive rectangle inside the coefficient size-and-ratio support -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def amplificationLowerC (B : ℕ) : Finset ℕ :=
  Ioc ⌊Real.exp (B : ℝ)⌋₊ ⌊Real.exp ((3 / 2 : ℝ) * B)⌋₊

noncomputable def amplificationLowerA (T c : ℕ) : Finset ℕ :=
  Ioc (T * c) ⌊(3 / 2 : ℝ) * T * c⌋₊

theorem amplificationLowerC_bounds {B c : ℕ} (hc : c ∈ amplificationLowerC B) :
    Real.exp (B : ℝ) < c ∧ (c : ℝ) ≤ Real.exp ((3 / 2 : ℝ) * B) := by
  have h := mem_Ioc.mp hc
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h.1,
    (Nat.le_floor_iff (Real.exp_pos _).le).mp h.2⟩

theorem amplificationLowerPair_mem {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationLowerC B) (ha : a ∈ amplificationLowerA T c) :
    (a, c) ∈ amplificationCoefficientPairs B T := by
  obtain ⟨hcl, hcu⟩ := amplificationLowerC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have ha' := mem_Ioc.mp ha
  have hau : (a : ℝ) ≤ (3 / 2 : ℝ) * T * c :=
    (Nat.le_floor_iff (by positivity)).mp ha'.2
  apply (mem_amplificationCoefficientPairs hB).mpr
  refine ⟨hcl.le, hcu.trans (Real.exp_le_exp.mpr ?_), ha'.1.le, ?_⟩
  · have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    linarith only [this]
  · have hprod : (0 : ℝ) < (T : ℝ) * c := mul_pos hT0 hc0
    have hh : (a : ℝ) < (2 * T * c : ℕ) := by push_cast; nlinarith only [hau, hprod]
    exact_mod_cast hh

theorem amplificationWindow_log_bounds {B T c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hTsize : (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B))
    (hc : c ∈ amplificationLowerC B) :
    1 ≤ Real.log ((T : ℝ) * c) / B ∧
      Real.log ((3 / 2 : ℝ) * T * c) / B ≤ 3 := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨hcl, hcu⟩ := amplificationLowerC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hTC : (0 : ℝ) < (T : ℝ) * c := mul_pos (by linarith only [hT1]) hc0
  constructor
  · apply (le_div_iff₀ hB0).mpr
    have hmul : (c : ℝ) ≤ (T : ℝ) * c := by
      nlinarith only [mul_le_mul_of_nonneg_right hT1 hc0.le]
    have hh := Real.log_le_log (Real.exp_pos (B : ℝ))
      (hcl.le.trans hmul)
    simpa only [Real.log_exp, one_mul] using hh
  · have hTu : (T : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * B) :=
      hTsize.trans (Real.exp_le_exp.mpr (by linarith only [hB0]))
    have hTCu : (T : ℝ) * c ≤ Real.exp (2 * (B : ℝ)) := by
      calc
        _ ≤ Real.exp ((1 / 2 : ℝ) * B) * Real.exp ((3 / 2 : ℝ) * B) :=
          mul_le_mul hTu hcu hc0.le (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hconst : (3 / 2 : ℝ) ≤ Real.exp (B : ℝ) := by
      have hh := Real.add_one_le_exp (B : ℝ)
      linarith only [hh, hB1]
    have hhi : (3 / 2 : ℝ) * T * c ≤ Real.exp (3 * (B : ℝ)) := by
      calc
        _ = (3 / 2 : ℝ) * ((T : ℝ) * c) := by ring
        _ ≤ Real.exp (B : ℝ) * Real.exp (2 * B) :=
          mul_le_mul hconst hTCu hTC.le (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    apply (div_le_iff₀ hB0).mpr
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (3 / 2 : ℝ) * T * c) hhi
    simpa only [Real.log_exp] using hh

theorem amplification_window_mass_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ T c : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) → c ∈ amplificationLowerC B →
      d / B ≤ ∑ a ∈ amplificationLowerA T c, primeProductMass (auxiliaryPrimes B) (1 / 2) a := by
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨d, hd, hbound⟩ := half_primeProduct_short_interval_lower hSD hM hMP hlog
  refine ⟨d, hd, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T c hT hTsize hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨hlo, hhi⟩ := amplificationWindow_log_bounds hB hT hTsize hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans (amplificationLowerC_bounds hc).1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 : (0 : ℝ) < (T : ℝ) * c := mul_pos hT0 hc0
  have hlogs : Real.log ((3 / 2 : ℝ) * T * c) / B - Real.log ((T : ℝ) * c) / B =
      Real.log (3 / 2 : ℝ) / B := by
    rw [mul_assoc (3 / 2 : ℝ), Real.log_mul (by norm_num) hTC0.ne']
    ring
  have hwidth : 0 ≤ Real.log ((3 / 2 : ℝ) * T * c) / B - Real.log ((T : ℝ) * c) / B := by
    rw [hlogs]
    exact div_nonneg hlog.le hB0.le
  have he1 : Real.exp ((B : ℝ) * (Real.log ((T : ℝ) * c) / B)) = (T : ℝ) * c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log hTC0]
  have he2 : Real.exp ((B : ℝ) * (Real.log ((3 / 2 : ℝ) * T * c) / B)) = (3 / 2 : ℝ) * T * c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log (by positivity)]
  have hh := hb (Real.log ((T : ℝ) * c) / B) (Real.log ((3 / 2 : ℝ) * T * c) / B)
    hlo (sub_nonneg.mp hwidth) hhi hlogs.ge
  rw [he1, he2, ← Nat.cast_mul T c, Nat.floor_natCast] at hh
  exact hh

end JointDickman

end OAI
