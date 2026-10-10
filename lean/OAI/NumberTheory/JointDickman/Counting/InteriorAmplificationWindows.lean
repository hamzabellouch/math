import OAI.NumberTheory.JointDickman.Counting.AmplificationWindows

namespace OAI

/-! # Positive coefficient windows strictly inside the smooth cutoff support -/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def amplificationInteriorC (B : ℕ) : Finset ℕ :=
  Ioc ⌊Real.exp ((5 / 4 : ℝ) * B)⌋₊ ⌊Real.exp ((3 / 2 : ℝ) * B)⌋₊

noncomputable def amplificationInteriorA (T c : ℕ) : Finset ℕ :=
  Ioc ⌊(5 / 4 : ℝ) * T * c⌋₊ ⌊(3 / 2 : ℝ) * T * c⌋₊

theorem amplificationInteriorC_bounds {B c : ℕ} (hc : c ∈ amplificationInteriorC B) :
    Real.exp ((5 / 4 : ℝ) * B) < c ∧ (c : ℝ) ≤ Real.exp ((3 / 2 : ℝ) * B) := by
  have h := mem_Ioc.mp hc
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h.1,
    (Nat.le_floor_iff (Real.exp_pos _).le).mp h.2⟩

theorem amplificationInteriorC_subset (B : ℕ) : amplificationInteriorC B ⊆ amplificationLowerC B := by
  intro c hc
  obtain ⟨hlo,hhi⟩ := amplificationInteriorC_bounds hc
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (Real.exp_pos _).le).mpr
    exact (Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) B; linarith)).trans_lt hlo
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr hhi

theorem amplificationInteriorA_subset (T c : ℕ) : amplificationInteriorA T c ⊆ amplificationLowerA T c := by
  intro a ha
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp ha
  apply mem_Ioc.mpr
  refine ⟨?_, hhi⟩
  have hfloor : T*c ≤ ⌊(5 / 4 : ℝ)*T*c⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    push_cast
    have ht : (0 : ℝ) ≤ (T : ℝ)*c := by positivity
    nlinarith
  exact hfloor.trans_lt hlo

theorem amplificationInteriorPair_mem {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationInteriorC B) (ha : a ∈ amplificationInteriorA T c) :
    (a,c) ∈ amplificationCoefficientPairs B T :=
  amplificationLowerPair_mem hB hT (amplificationInteriorC_subset B hc) (amplificationInteriorA_subset T c ha)

theorem amplification_interior_row_mass_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ T c : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ)*B) → c ∈ amplificationInteriorC B →
      d / B ≤ ∑ a ∈ amplificationInteriorA T c, primeProductMass (auxiliaryPrimes B) (1 / 2) a := by
  have hlog : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨d,hd,hbound⟩ := half_primeProduct_short_interval_lower hSD hM hMP hlog
  refine ⟨d,hd,?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T c hT hTsize hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans (amplificationInteriorC_bounds hc).1
  have hTC0 : (0 : ℝ) < (T : ℝ)*c := mul_pos hT0 hc0
  obtain ⟨hlo,hhi⟩ := amplificationWindow_log_bounds hB hT hTsize (amplificationInteriorC_subset B hc)
  have hlo' : 1 ≤ Real.log ((5 / 4 : ℝ)*T*c) / B := hlo.trans
    (div_le_div_of_nonneg_right (Real.log_le_log hTC0 (by nlinarith)) hB0.le)
  have hlogs : Real.log ((3 / 2 : ℝ)*T*c) / B - Real.log ((5 / 4 : ℝ)*T*c) / B =
      Real.log (6 / 5 : ℝ) / B := by
    rw [mul_assoc (3 / 2 : ℝ), mul_assoc (5 / 4 : ℝ),
      Real.log_mul (by norm_num) hTC0.ne', Real.log_mul (by norm_num) hTC0.ne']
    have hl : Real.log (6 / 5 : ℝ) = Real.log (3 / 2 : ℝ) - Real.log (5 / 4 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    rw [hl]
    ring
  have hwidth : Real.log ((5 / 4 : ℝ)*T*c) / B ≤ Real.log ((3 / 2 : ℝ)*T*c) / B := by
    have := div_nonneg hlog.le hB0.le
    linarith only [hlogs, this]
  have he1 : Real.exp ((B : ℝ)*(Real.log ((5 / 4 : ℝ)*T*c) / B)) = (5 / 4 : ℝ)*T*c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log (by positivity)]
  have he2 : Real.exp ((B : ℝ)*(Real.log ((3 / 2 : ℝ)*T*c) / B)) = (3 / 2 : ℝ)*T*c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log (by positivity)]
  have hh := hb _ _ hlo' hwidth hhi hlogs.ge
  rw [he1,he2] at hh
  exact hh

end JointDickman

end OAI
