import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.NormalBudget

namespace OAI

section

open Set Filter Metric
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer

lemma rpow_abs_difference {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ C ≥ (0:ℝ), ∀ a b : ℝ,
      abs (|a+b|^p-|a|^p) ≤ ε*|a|^p+C*|b|^p := by
  have ht : Tendsto (fun t : ℝ => abs (|1+t|^p-1)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => abs (|1+t|^p-1)) := by
      have hp0 := hp.le
      fun_prop
    simpa using hc.tendsto 0
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds hε))
  let D := δ⁻¹+1
  let C := D^p+(δ⁻¹)^p
  have hC : 0 ≤ C := add_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨C,hC,fun a b => ?_⟩
  by_cases ha : a = 0
  · subst a
    simp only [zero_add,abs_zero,Real.zero_rpow hp.ne',sub_zero,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg b) p),mul_zero,zero_add]
    have hD : 1 ≤ D := by dsimp [D]; have := inv_nonneg.mpr hδ.le; linarith
    have hc1 : 1 ≤ C := by
      have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hD hp.le
      simp only [Real.one_rpow] at hh
      exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
    nlinarith [Real.rpow_nonneg (abs_nonneg b) p]
  have hap : 0 < |a| := abs_pos.mpr ha
  by_cases hs : |b/a| < δ
  · have hh : abs (|1+b/a|^p-1) < ε := hd (by simpa only [mem_ball,Real.dist_eq,sub_zero] using hs)
    have he : |a+b|^p = |a|^p*|1+b/a|^p := by
      rw [←Real.mul_rpow (abs_nonneg _) (abs_nonneg _),←abs_mul]
      congr 2
      field_simp
    rw [he,←mul_sub_one,abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact (mul_le_mul_of_nonneg_left hh.le (Real.rpow_nonneg (abs_nonneg _) _)).trans
      (by nlinarith [mul_nonneg hC (Real.rpow_nonneg (abs_nonneg b) p)])
  · have hratio : δ ≤ |b|/|a| := by simpa only [abs_div] using le_of_not_gt hs
    have hab : |a| ≤ δ⁻¹*|b| := by
      have hh := (le_div_iff₀ hap).mp hratio
      rw [mul_comm,←div_eq_mul_inv]
      exact (le_div_iff₀ hδ).mpr (by simpa [mul_comm] using hh)
    have hab' : |a+b| ≤ D*|b| := by
      have := abs_add_le a b
      dsimp [D]
      nlinarith
    have habp := Real.rpow_le_rpow (abs_nonneg _) hab hp.le
    have habp' := Real.rpow_le_rpow (abs_nonneg _) hab' hp.le
    rw [Real.mul_rpow (inv_nonneg.mpr hδ.le) (abs_nonneg _)] at habp
    rw [Real.mul_rpow (by dsimp [D]; positivity) (abs_nonneg _)] at habp'
    have hh := abs_sub (|a+b|^p) (|a|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hh
    dsimp [C] at hC ⊢
    nlinarith [mul_nonneg hε.le (Real.rpow_nonneg (abs_nonneg a) p)]

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma brezis_lieb_remainder {p : ℝ} (hp : 0 < p) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ j, Integrable (fun x => |f j x|^p) μ)
    (hg : Integrable (fun x => |g x|^p) μ)
    (hz : ∀ j, Integrable (fun x => |f j x-g x|^p) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (M : ℝ) (hM : ∀ j, ∫ x, |f j x-g x|^p ∂μ ≤ M) :
    Tendsto (fun j => ∫ x, abs (|f j x|^p-|f j x-g x|^p-|g x|^p) ∂μ) atTop (𝓝 0) := by
  let R := fun j x => |f j x|^p-|f j x-g x|^p-|g x|^p
  have hR (j : ℕ) : Integrable (R j) μ := ((hf j).sub (hz j)).sub hg
  have hRlim : ∀ᵐ x ∂μ, Tendsto (fun j => R j x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hj := ((hx.abs.rpow_const (Or.inr hp.le)).sub
      ((hx.sub_const (g x)).abs.rpow_const (Or.inr hp.le))).sub_const (|g x|^p)
    simpa only [R,sub_self,abs_zero,Real.zero_rpow hp.ne',sub_zero] using hj
  have hM0 : 0 ≤ M := (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η := ε/(2*(M+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C,hC,hbound⟩ := rpow_abs_difference hp hη
  let H := fun j x => max (abs (R j x)-η*|f j x-g x|^p) 0
  have hH (j : ℕ) : Integrable (H j) μ := (((hR j).abs).sub ((hz j).const_mul η)).sup (integrable_zero _ _ _)
  have hHbound (j : ℕ) (x : α) : ‖H j x‖ ≤ (C+1)*|g x|^p := by
    have hb := hbound (f j x-g x) (g x)
    rw [sub_add_cancel] at hb
    have ht := abs_sub (|f j x|^p-|f j x-g x|^p) (|g x|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at ht
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · dsimp [R]
      nlinarith
    · positivity
  have hHlim : ∀ᵐ x ∂μ, Tendsto (fun j => H j x) atTop (𝓝 0) := by
    filter_upwards [hRlim,hlim] with x hx hfx
    have ht := (hx.abs.sub (((hfx.sub_const (g x)).abs.rpow_const (Or.inr hp.le)).const_mul η)).max (tendsto_const_nhds (x := (0:ℝ)))
    simpa only [H,sub_self,abs_zero,Real.zero_rpow hp.ne',mul_zero,sub_zero,max_self] using ht
  have hc := tendsto_integral_of_dominated_convergence (fun x => (C+1)*|g x|^p)
    (fun j => (hH j).aestronglyMeasurable) (hg.const_mul (C+1))
    (fun j => Eventually.of_forall (hHbound j)) hHlim
  simp only [integral_zero] at hc
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun j hj => ?_⟩
  have hupper : ∫ x, abs (R j x) ∂μ ≤ ∫ x, H j x ∂μ + η*M := by
    have hh := integral_mono ((hR j).abs) ((hH j).add ((hz j).const_mul η)) (fun x => by
      have h := le_max_left (abs (R j x)-η*|f j x-g x|^p) 0
      dsimp [H]
      linarith)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hH j) ((hz j).const_mul η),integral_const_mul] at hh
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hM j) hη.le) _)
  have ht := hN j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => le_max_right _ _)] at ht
  have hηM : η*M < ε/2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(M+1))).mpr
    nlinarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
  exact hupper.trans_lt (by linarith)

lemma brezis_lieb_splitting {p : ℝ} (hp : 0 < p) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ j, Integrable (fun x => |f j x|^p) μ)
    (hg : Integrable (fun x => |g x|^p) μ)
    (hz : ∀ j, Integrable (fun x => |f j x-g x|^p) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (M : ℝ) (hM : ∀ j, ∫ x, |f j x-g x|^p ∂μ ≤ M) :
    Tendsto (fun j => (∫ x, |f j x|^p ∂μ)-(∫ x, |f j x-g x|^p ∂μ)-(∫ x, |g x|^p ∂μ))
      atTop (𝓝 0) := by
  have hh := brezis_lieb_remainder hp f g hf hg hz hlim M hM
  apply squeeze_zero_norm (fun j => ?_) hh
  have he := integral_sub ((hf j).sub (hz j)) hg
  simp only [Pi.sub_apply] at he
  rw [integral_sub (hf j) (hz j)] at he
  rw [←he]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x =>
    |f j x|^p-|f j x-g x|^p-|g x|^p)

end CAT0Fillings.AnalyticMinimizer
end

end OAI
