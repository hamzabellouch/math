import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

private theorem rpow_add_le_tangent_add_rpow {q a t : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (a + t) ^ q ≤ a ^ q + q * a ^ (q - 1) * t + t ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let F : ℝ → ℝ := fun z =>
    (a + z) ^ q - a ^ q - q * a ^ (q - 1) * z - z ^ q
  have hderiv (z : ℝ) : HasDerivAt F
      (q * ((a + z) ^ (q - 1) - a ^ (q - 1) - z ^ (q - 1))) z := by
    have hplus : HasDerivAt (fun x : ℝ => (a + x) ^ q)
        (q * (a + z) ^ (q - 1)) z := by
      simpa only [one_mul] using
        ((hasDerivAt_id' z).const_add a).rpow_const (Or.inr hq.le)
    have hlinear : HasDerivAt (fun x : ℝ => q * a ^ (q - 1) * x)
        (q * a ^ (q - 1)) z := by
      exact hasDerivAt_const_mul (q * a ^ (q - 1))
    have hpower : HasDerivAt (fun x : ℝ => x ^ q) (q * z ^ (q - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inr hq.le)
    dsimp only [F]
    convert! ((hplus.sub_const (a ^ q)).sub hlinear).sub hpower using 1 ; ring
  have hdiff : Differentiable ℝ F := fun z => (hderiv z).differentiableAt
  have hanti : AntitoneOn F (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro z hz
    have hz0 : 0 ≤ z := interior_subset hz
    rw [(hderiv z).deriv]
    have hsub : (a + z) ^ (q - 1) ≤ a ^ (q - 1) + z ^ (q - 1) :=
      Real.rpow_add_le_add_rpow ha hz0 (by linarith) (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
  have hbound : F t ≤ F 0 := hanti (by simp) ht ht
  simp only [F, add_zero, mul_zero, Real.zero_rpow hq0.ne', sub_self] at hbound
  linarith only [hbound]

private theorem rpow_sub_le_tangent_add_rpow {q a t : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (ha : 0 ≤ a)
    (ht : 0 ≤ t) (hta : t ≤ a) :
    (a - t) ^ q ≤ a ^ q - q * a ^ (q - 1) * t + t ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let F : ℝ → ℝ := fun z =>
    (a - z) ^ q - a ^ q + q * a ^ (q - 1) * z - z ^ q
  have hderiv (z : ℝ) : HasDerivAt F
      (q * (a ^ (q - 1) - (a - z) ^ (q - 1) - z ^ (q - 1))) z := by
    have hminus : HasDerivAt (fun x : ℝ => (a - x) ^ q)
        (-(q * (a - z) ^ (q - 1))) z := by
      convert ((hasDerivAt_id z).const_sub a).rpow_const (Or.inr hq.le) using 1 <;> ring_nf <;> rfl
    have hlinear : HasDerivAt (fun x : ℝ => q * a ^ (q - 1) * x)
        (q * a ^ (q - 1)) z := by
      exact hasDerivAt_const_mul (q * a ^ (q - 1))
    have hpower : HasDerivAt (fun x : ℝ => x ^ q) (q * z ^ (q - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inr hq.le)
    dsimp only [F]
    convert! ((hminus.sub_const (a ^ q)).add hlinear).sub hpower using 1 ; ring
  have hdiff : Differentiable ℝ F := fun z => (hderiv z).differentiableAt
  have hanti : AntitoneOn F (Set.Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro z hz
    have hzmem : z ∈ Set.Icc 0 a := interior_subset hz
    rw [(hderiv z).deriv]
    have hsub : a ^ (q - 1) ≤ (a - z) ^ (q - 1) + z ^ (q - 1) := by
      simpa only [sub_add_cancel] using
        (Real.rpow_add_le_add_rpow (p := q - 1)
          (sub_nonneg.mpr hzmem.2) hzmem.1 (by linarith) (by linarith))
    exact mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
  have hbound : F t ≤ F 0 := hanti ⟨le_rfl, ha⟩ ⟨ht, hta⟩ ht
  simp only [F, sub_zero, mul_zero, Real.zero_rpow hq0.ne', sub_self, add_zero] at hbound
  linarith only [hbound]

theorem rpow_le_tangent_add_abs_rpow {q a b : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b ^ q ≤ a ^ q + q * a ^ (q - 1) * (b - a) + |b - a| ^ q := by
  by_cases ha0 : a = 0
  · subst a
    have hq0 : 0 < q := lt_trans zero_lt_one hq
    simp only [Real.zero_rpow hq0.ne', Real.zero_rpow (sub_pos.mpr hq).ne',
      mul_zero, zero_mul, zero_add, sub_zero, abs_of_nonneg hb, le_refl]
  rcases le_total a b with hab | hba
  · have hbound := rpow_add_le_tangent_add_rpow hq hq₂ ha (sub_nonneg.mpr hab)
    have hab_eq : a + (b - a) = b := by ring
    rw [hab_eq] at hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hbound
  · have hbound := rpow_sub_le_tangent_add_rpow hq hq₂ ha
      (sub_nonneg.mpr hba) (sub_le_self a hb)
    have hab_eq : a - (a - b) = b := by ring
    rw [hab_eq] at hbound
    rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    have hneg : -(b - a) = a - b := by ring
    rw [hneg]
    calc
      b ^ q ≤ a ^ q - q * a ^ (q - 1) * (a - b) + (a - b) ^ q := hbound
      _ = a ^ q + q * a ^ (q - 1) * (b - a) + (a - b) ^ q := by ring

theorem symmetric_rpow_le_of_sum_bound {q C a b u v : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (_hC : 0 ≤ C)
    (ha : 0 < a) (_hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hua : |u - a| ≤ b) (hva : |v - a| ≤ b)
    (hsum : u + v ≤ 2 * a + 2 * C * b ^ q * a ^ (1 - q)) :
    u ^ q + v ^ q ≤ 2 * a ^ q + 2 * (1 + q * C) * b ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hu_bound := rpow_le_tangent_add_abs_rpow hq hq₂ ha.le hu
  have hv_bound := rpow_le_tangent_add_abs_rpow hq hq₂ ha.le hv
  have hu_error : |u - a| ^ q ≤ b ^ q := Real.rpow_le_rpow (abs_nonneg _) hua hq0.le
  have hv_error : |v - a| ^ q ≤ b ^ q := Real.rpow_le_rpow (abs_nonneg _) hva hq0.le
  have hcoef : 0 ≤ q * a ^ (q - 1) := mul_nonneg hq0.le (Real.rpow_nonneg ha.le _)
  have hsum_bound : q * a ^ (q - 1) * (u + v - 2 * a) ≤
      q * a ^ (q - 1) * (2 * C * b ^ q * a ^ (1 - q)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hsum]) hcoef
  have hcancel : a ^ (q - 1) * a ^ (1 - q) = 1 := by
    rw [← Real.rpow_add ha]
    have hexponent : q - 1 + (1 - q) = 0 := by ring
    rw [hexponent, Real.rpow_zero]
  calc
    u ^ q + v ^ q ≤
        2 * a ^ q + q * a ^ (q - 1) * (u + v - 2 * a) + 2 * b ^ q := by
      linarith only [hu_bound, hv_bound, hu_error, hv_error]
    _ ≤ 2 * a ^ q +
        q * a ^ (q - 1) * (2 * C * b ^ q * a ^ (1 - q)) + 2 * b ^ q :=
      add_le_add (add_le_add le_rfl hsum_bound) le_rfl
    _ = 2 * a ^ q + 2 * (q * C) * b ^ q * (a ^ (q - 1) * a ^ (1 - q)) +
        2 * b ^ q := by ring
    _ = 2 * a ^ q + 2 * (1 + q * C) * b ^ q := by rw [hcancel]; ring

end MarkovSuperreflexivity

end OAI
