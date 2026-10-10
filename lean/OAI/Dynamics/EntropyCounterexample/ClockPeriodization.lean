import Mathlib

namespace OAI

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def periodize (P : ℝ) (f : ℝ × E → F) (x : ℝ × E) : F :=
  ∑' k : ℤ, f (x.1 - (k : ℝ) * P, x.2)

theorem contDiff_tsum_of_locallyFinite {ι : Type*} {f : ι → E → F} {n : ℕ∞ω}
    (hf : ∀ i, ContDiff ℝ n (f i))
    (hl : LocallyFinite (fun i => support (f i))) :
    ContDiff ℝ n (fun x => ∑' i, f i x) := by
  have heq : (fun x => ∑' i, f i x) = (fun x => ∑ᶠ i, f i x) := by
    funext x
    exact tsum_eq_finsum (hl.point_finite x)
  rw [heq]
  exact contMDiff_iff_contDiff.mp (contMDiff_finsum
    (fun i => contMDiff_iff_contDiff.mpr (hf i)) hl)

theorem locallyFinite_clockIntervals {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    LocallyFinite (fun k : ℤ => Icc ((k : ℝ) * P + a) ((k : ℝ) * P + b)) := by
  apply locallyFinite_Icc_of_tendsto
  · exact (tendsto_intCast_atTop_atTop.atTop_mul_const hP).atTop_add tendsto_const_nhds
  · exact ((tendsto_intCast_atBot_iff.mpr tendsto_id).atBot_mul_const hP).atBot_add
      tendsto_const_nhds

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem locallyFinite_translates {P a b : ℝ} (hP : 0 < P) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    LocallyFinite (fun k : ℤ => support (fun x : ℝ × E =>
      f (x.1 - (k : ℝ) * P, x.2))) := by
  refine ((locallyFinite_clockIntervals hP a b).preimage_continuous continuous_fst).subset ?_
  intro k x hx
  have h := hsupport (x.1 - (k : ℝ) * P, x.2) hx
  change (k : ℝ) * P + a ≤ x.1 ∧ x.1 ≤ (k : ℝ) * P + b
  constructor <;> linarith [h.1, h.2]

theorem contDiff_periodize {P a b : ℝ} {n : ℕ∞ω} (hP : 0 < P)
    {f : ℝ × E → F} (hf : ContDiff ℝ n f)
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiff ℝ n (periodize P f) := by
  apply contDiff_tsum_of_locallyFinite
  · intro k
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  · exact locallyFinite_translates hP hsupport

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem periodize_add_period (P : ℝ) (f : ℝ × E → F) (t : ℝ) (x : E) :
    periodize P f (t + P, x) = periodize P f (t, x) := by
  unfold periodize
  calc
    (∑' k : ℤ, f (t + P - (k : ℝ) * P, x)) =
        ∑' k : ℤ, f (t - ((k + -1 : ℤ) : ℝ) * P, x) := by
      apply tsum_congr
      intro k
      apply congrArg (fun r : ℝ => f (r, x))
      push_cast
      ring
    _ = ∑' k : ℤ, f (t - (k : ℝ) * P, x) :=
      (Equiv.addRight (-1 : ℤ)).tsum_eq (fun k : ℤ => f (t - (k : ℝ) * P, x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem periodize_eq_on_fundamental {P : ℝ} (hP : 0 < P) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 P)
    {t : ℝ} (ht : t ∈ Icc 0 P) (x : E) :
    periodize P f (t, x) = f (t, x) := by
  unfold periodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    by_contra hne
    have h := hsupport (t - (k : ℝ) * P, x) hne
    rcases lt_or_gt_of_ne hk with hkn | hkp
    · have hk1 : k ≤ -1 := by omega
      have hk1' : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
      nlinarith [h.2, ht.1]
    · have hk1 : 1 ≤ k := by omega
      have hk1' : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith [h.1, ht.2]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem translate_index_unique {P a b : ℝ} (hP : 0 < P) (hab : b - a ≤ P)
    {f : ℝ × E → F} (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Ioo a b)
    {x : ℝ × E} {k l : ℤ}
    (hk : f (x.1 - (k : ℝ) * P, x.2) ≠ 0)
    (hl : f (x.1 - (l : ℝ) * P, x.2) ≠ 0) : k = l := by
  have hk' := hsupport (x.1 - (k : ℝ) * P, x.2) hk
  have hl' := hsupport (x.1 - (l : ℝ) * P, x.2) hl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hij : k + 1 ≤ l := by omega
    have hij' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hij
    nlinarith [hk'.2, hl'.1]
  · have hij : l + 1 ≤ k := by omega
    have hij' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hij
    nlinarith [hl'.2, hk'.1]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem norm_periodize_le {P a b C : ℝ} (hP : 0 < P) (hab : b - a ≤ P)
    (hC : 0 ≤ C) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Ioo a b)
    (hbound : ∀ x, ‖f x‖ ≤ C) (x : ℝ × E) :
    ‖periodize P f x‖ ≤ C := by
  classical
  by_cases hex : ∃ k : ℤ, f (x.1 - (k : ℝ) * P, x.2) ≠ 0
  · obtain ⟨k, hk⟩ := hex
    have heq : periodize P f x = f (x.1 - (k : ℝ) * P, x.2) := by
      apply tsum_eq_single k
      intro l hl
      by_contra hne
      exact hl (translate_index_unique hP hab hsupport hne hk)
    rw [heq]
    exact hbound _
  · have hzero : ∀ k : ℤ, f (x.1 - (k : ℝ) * P, x.2) = 0 := by
      simpa using hex
    simpa only [periodize, hzero, tsum_zero, norm_zero] using hC

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem periodize_mem_Icc {P a b C : ℝ} (hP : 0 < P) (hab : b - a ≤ P)
    (hC : 0 ≤ C) {f : ℝ × E → ℝ}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Ioo a b)
    (hbound : ∀ x, f x ∈ Icc 0 C) (x : ℝ × E) :
    periodize P f x ∈ Icc 0 C := by
  constructor
  · exact tsum_nonneg (fun k => (hbound _).1)
  · apply le_trans (le_abs_self _)
    exact norm_periodize_le hP hab hC hsupport
      (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound y).1]
        using (hbound y).2) x

end Problem340.ClockPeriodization

end

end OAI
