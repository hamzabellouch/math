import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Model

namespace OAI

/-! SheetFlows profiles. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

open Filter
open scoped Topology

def plateau (h d : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition (2 * (s + h + d) / d) *
    Real.smoothTransition (2 * (h + d - s) / d)

theorem plateau_contDiff (h d : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateau h d) := by
  unfold plateau
  fun_prop

theorem plateau_nonneg (h d s : ℝ) : 0 ≤ plateau h d s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateau_le_one (h d s : ℝ) : plateau h d s ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem plateau_even (h d : ℝ) : Function.Even (plateau h d) := by
  intro s
  have h₁ : -s + h + d = h + d - s := by ring
  have h₂ : h + d - -s = s + h + d := by ring
  simp only [plateau, h₁, h₂, mul_comm]

theorem plateau_one {h d s : ℝ} (hd : 0 < d) (hs : |s| ≤ h + d / 2) :
    plateau h d s = 1 := by
  rcases abs_le.mp hs with ⟨hl, hu⟩
  have h₁ : 1 ≤ 2 * (s + h + d) / d := (le_div_iff₀ hd).mpr (by linarith)
  have h₂ : 1 ≤ 2 * (h + d - s) / d := (le_div_iff₀ hd).mpr (by linarith)
  simp only [plateau, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂, mul_one]

theorem plateau_zero {h d s : ℝ} (hd : 0 < d) (hs : h + d ≤ |s|) :
    plateau h d s = 0 := by
  rcases le_abs.mp hs with hl | hr
  · have : 2 * (h + d - s) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]
  · have : 2 * (s + h + d) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]

theorem plateau_compactSupport {h d : ℝ} (hd : 0 < d) :
    HasCompactSupport (plateau h d) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(h+d)) (b := h+d))
  intro s hs
  apply plateau_zero hd
  apply le_of_not_gt
  intro h
  exact hs (abs_le.mp h.le)

def linearProfile (h d : ℝ) (s : ℝ) : ℝ := s * plateau h d s

theorem linearProfile_contDiff (h d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (linearProfile h d) :=
  contDiff_id.mul (plateau_contDiff h d)

theorem linearProfile_odd (h d : ℝ) : Function.Odd (linearProfile h d) := by
  intro s
  dsimp [linearProfile]
  rw [plateau_even h d s]
  ring

theorem linearProfile_eq {h d s : ℝ} (hd : 0 < d) (hs : |s| ≤ h + d / 2) :
    linearProfile h d s = s := by simp [linearProfile, plateau_one hd hs]

theorem linearProfile_zero {h d s : ℝ} (hd : 0 < d) (hs : h + d ≤ |s|) :
    linearProfile h d s = 0 := by simp [linearProfile, plateau_zero hd hs]

theorem linearProfile_integral_zero (h d : ℝ) :
    (∫ s : ℝ, linearProfile h d s) = 0 := by
  have he := integral_neg_eq_self (linearProfile h d) (volume : Measure ℝ)
  have ho : (fun s => linearProfile h d (-s)) = fun s => -linearProfile h d s :=
    funext (linearProfile_odd h d)
  rw [ho, integral_neg] at he
  linarith

def periodize (T : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℤ, g (x - T * k)

theorem periodize_periodic (T : ℝ) (g : ℝ → ℝ) :
    Function.Periodic (periodize T g) T := by
  intro x
  unfold periodize
  calc
    (∑' k : ℤ, g (x + T - T * k)) =
        ∑' k : ℤ, g (x - T * ((Equiv.subRight (1 : ℤ)) k : ℤ)) := by
      congr 1
      funext k
      congr 1
      simp only [Equiv.subRight_apply, Int.cast_sub, Int.cast_one]
      ring
    _ = ∑' k : ℤ, g (x - T * k) :=
      (Equiv.subRight (1 : ℤ)).tsum_eq (fun k : ℤ => g (x - T * k))

theorem periodize_locally_finite {T a b : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x < a ∨ b < x → g x = 0) (x : ℝ) :
    ∃ K : Finset ℤ, ∀ᶠ y in 𝓝 x,
      periodize T g y = ∑ k ∈ K, g (y - T * k) := by
  let L : ℤ := ⌊(x - 1 - b) / T⌋
  let U : ℤ := ⌈(x + 1 - a) / T⌉
  refine ⟨Finset.Icc L U, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < 1 by norm_num)] with y hy
  apply tsum_eq_sum
  intro k hk
  have hy' : |y - x| < 1 := by simpa [Real.dist_eq] using hy
  rcases abs_lt.mp hy' with ⟨hy₀, hy₁⟩
  have hL : (L : ℝ) * T ≤ x - 1 - b :=
    (le_div_iff₀ hT).mp (Int.floor_le ((x - 1 - b) / T))
  have hU : x + 1 - a ≤ (U : ℝ) * T :=
    (div_le_iff₀ hT).mp (Int.le_ceil ((x + 1 - a) / T))
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · have hk' : (k : ℝ) < (L : ℝ) := by exact_mod_cast hk
    apply hg
    right
    have he := mul_lt_mul_of_pos_right hk' hT
    linarith
  · have hk' : (U : ℝ) < (k : ℝ) := by exact_mod_cast hk
    apply hg
    left
    have he := mul_lt_mul_of_pos_right hk' hT
    linarith

theorem periodize_contDiff {T a b : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x < a ∨ b < x → g x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize T g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨K, hK⟩ := periodize_locally_finite hT g hg x
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k ∈ K, g (y - T * k)) :=
    ContDiff.sum (fun k _ => hsm.comp (contDiff_id.sub contDiff_const))
  exact h.contDiffAt.congr_of_eventuallyEq hK

theorem periodize_on_chart {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x ≤ 0 ∨ T ≤ x → g x = 0) {x : ℝ} (hx : x ∈ Set.Icc 0 T) :
    periodize T g x = g x := by
  unfold periodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      apply hg
      right
      have he := mul_le_mul_of_nonneg_left hk' hT.le
      linarith [hx.1]
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      apply hg
      left
      have he := mul_le_mul_of_nonneg_left hk' hT.le
      linarith [hx.2]

theorem periodize_integral_eq {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x ≤ 0 ∨ T ≤ x → g x = 0) :
    (∫ x in Set.Ico 0 T, periodize T g x) = ∫ x : ℝ, g x := by
  calc
    (∫ x in Set.Ico 0 T, periodize T g x) = ∫ x in Set.Ico 0 T, g x := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      exact periodize_on_chart hT g hg ⟨hx.1, hx.2.le⟩
    _ = ∫ x : ℝ, g x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      apply hg
      by_cases hl : x < 0
      · exact Or.inl hl.le
      · exact Or.inr (le_of_not_gt (fun hu => hx ⟨le_of_not_gt hl, hu⟩))

theorem shifted_profile_zero_outside {T r c : ℝ} (g : ℝ → ℝ)
    (hg : ∀ x, r ≤ |x| → g x = 0) (hl : r ≤ c) (hu : c + r ≤ T) :
    ∀ x, x ≤ 0 ∨ T ≤ x → g (x - c) = 0 := by
  intro x hx
  apply hg
  rcases hx with hx | hx
  · exact le_abs.mpr (Or.inr (by linarith))
  · exact le_abs.mpr (Or.inl (by linarith))

def Cprofile (h d c : ℝ) : ℝ → ℝ :=
  periodize 10 (fun s => plateau h d (s - c))

def Dprofile (h d c : ℝ) : ℝ → ℝ :=
  periodize 10 (fun s => linearProfile h d (s - c))

theorem Cprofile_periodic (h d c : ℝ) : Function.Periodic (Cprofile h d c) 10 :=
  periodize_periodic _ _

theorem Dprofile_periodic (h d c : ℝ) : Function.Periodic (Dprofile h d c) 10 :=
  periodize_periodic _ _

theorem Cprofile_contDiff (h c : ℝ) {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ (⊤ : ℕ∞) (Cprofile h d c) := by
  apply periodize_contDiff (a := c - (h+d)) (b := c + (h+d)) (by norm_num)
  · intro x hx
    apply plateau_zero hd
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl (by linarith))
  · exact (plateau_contDiff h d).comp (contDiff_id.sub contDiff_const)

theorem Dprofile_contDiff (h c : ℝ) {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ (⊤ : ℕ∞) (Dprofile h d c) := by
  apply periodize_contDiff (a := c - (h+d)) (b := c + (h+d)) (by norm_num)
  · intro x hx
    apply linearProfile_zero hd
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl (by linarith))
  · exact (linearProfile_contDiff h d).comp (contDiff_id.sub contDiff_const)

theorem Cprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Cprofile h d c s = plateau h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu) hs

theorem Dprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Dprofile h d c s = linearProfile h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => linearProfile_zero hd) hl hu) hs

theorem Cprofile_one {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : |s - c| ≤ h + d / 2) : Cprofile h d c s = 1 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_one hd hsc

theorem Dprofile_linear {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : |s - c| ≤ h + d / 2) : Dprofile h d c s = s - c := by
  rw [Dprofile_on_chart hd hl hu hs]
  exact linearProfile_eq hd hsc

theorem Cprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Cprofile h d c s = 0 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_zero hd hsc

theorem Dprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Dprofile h d c s = 0 := by
  rw [Dprofile_on_chart hd hl hu hs]
  exact linearProfile_zero hd hsc

theorem Cprofile_integral_eq {h d c : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Cprofile h d c s) = ∫ s : ℝ, plateau h d s := by
  rw [Cprofile, periodize_integral_eq (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu)]
  exact integral_sub_right_eq_self _ _

theorem Dprofile_integral_zero {h d c : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Dprofile h d c s) = 0 := by
  rw [Dprofile, periodize_integral_eq (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => linearProfile_zero hd) hl hu),
    integral_sub_right_eq_self]
  exact linearProfile_integral_zero h d

theorem Cprofile_corrected_integral_zero {h d c c' : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10)
    (hl' : h + d ≤ c') (hu' : c' + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Cprofile h d c s - Cprofile h d c' s) = 0 := by
  rw [integral_sub
    ((Cprofile_contDiff h c hd).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
    ((Cprofile_contDiff h c' hd).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self),
    Cprofile_integral_eq hd hl hu, Cprofile_integral_eq hd hl' hu', sub_self]

end Solenoidal
end
end

end OAI
