import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.NormalBudget
import OAI.Geometry.CAT0Fillings.Powers.Potential

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma power_tail_tendsto {f : α → ℝ} {p : ℝ} (hp : 0 < p)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ) :
    Tendsto (fun j : ℕ => ∫ x, if (j:ℝ)+1 < |f x| then |f x|^p else 0 ∂μ) atTop (𝓝 0) := by
  classical
  have hi : Integrable (fun x => |f x|^p) μ := by
    simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hp.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hh := tendsto_integral_of_dominated_convergence (F := fun j : ℕ => fun x => if (j:ℝ)+1 < |f x| then |f x|^p else 0)
    (f := fun _ => (0:ℝ)) (fun x => |f x|^p)
    (fun j => ((hfm.abs.pow_const p).ite (measurableSet_lt measurable_const hfm.abs) measurable_const).aestronglyMeasurable)
    hi (fun j => Eventually.of_forall (fun x => by
      split_ifs
      · simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),le_refl]
      · simpa only [norm_zero] using Real.rpow_nonneg (abs_nonneg (f x)) p))
    (Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      have he : ∀ᶠ j : ℕ in atTop, |f x| ≤ (j:ℝ)+1 :=
        ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually
          (eventually_ge_atTop (|f x|))).mono (fun j hj => by linarith)
      filter_upwards [he] with j hj
      rw [ite_eq_right (not_lt_of_ge hj)]))
  simpa only [integral_zero] using hh

lemma lpNorm_two_sq_integral {g : α → ℝ} (hg : AEStronglyMeasurable g μ) :
    lpNorm g 2 μ ^2 = ∫ x, (g x)^2 ∂μ := by
  have hh := AnalyticMinimizer.lpNorm_sq_eq_integral (by norm_num : (0:ℝ) < 2) hg
  simpa only [ENNReal.ofReal_ofNat,Real.rpow_two,sq_abs,div_self (by norm_num : (2:ℝ) ≠ 0),Real.rpow_one] using hh

lemma potential_split {f g : α → ℝ} {p K : ℝ} (hp : 2 < p) (hK : 0 < K)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) (hg2 : MemLp g 2 μ) :
    (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      K^(p-2)*(lpNorm g 2 μ)^2 +
        (∫ x, if K < |f x| then |f x|^p else 0 ∂μ)^((p-2)/p) *
          (lpNorm g (ENNReal.ofReal p) μ)^2 := by
  let s : Set α := {x | K < |f x|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hfm.abs
  have hft := hf.indicator hs
  have hgi : Integrable (fun x => (g x)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hg2.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hb : (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
      (∫ x, K^(p-2)*(g x)^2 + |s.indicator f x|^(p-2)*(g x)^2 ∂μ) := by
    apply integral_mono (potential_integrable hp hf hg)
      ((hgi.const_mul _).add (potential_integrable hp hft hg))
    intro x
    change |f x|^(p-2)*(g x)^2 ≤ K^(p-2)*(g x)^2+|s.indicator f x|^(p-2)*(g x)^2
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hK.le _) (sq_nonneg _))
    · rw [Set.indicator_of_notMem hx,abs_zero,Real.zero_rpow (by linarith : p-2 ≠ 0),zero_mul,add_zero]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (le_of_not_gt hx) (by linarith)) (sq_nonneg _)
  rw [integral_add (hgi.const_mul _) (potential_integrable hp hft hg),integral_const_mul,
    ←lpNorm_two_sq_integral hg2.aestronglyMeasurable] at hb
  apply hb.trans
  apply add_le_add_right
  have hh := potential_holder hp hft hg
  have he : (∫ x, |s.indicator f x|^p ∂μ) =
      (∫ x, if K < |f x| then |f x|^p else 0 ∂μ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change |s.indicator f x|^p = if K < |f x| then |f x|^p else 0
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx,ite_eq_left (show K < |f x| from hx)]
      · rw [Set.indicator_of_notMem hx,ite_eq_right (show ¬K < |f x| from hx),abs_zero,Real.zero_rpow (by linarith : p ≠ 0)]
  simpa only [he] using hh

lemma potential_small {f : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : α → ℝ, MemLp g (ENNReal.ofReal p) μ → MemLp g 2 μ →
      (∫ x, |f x|^(p-2)*(g x)^2 ∂μ) ≤
        δ*(lpNorm g (ENNReal.ofReal p) μ)^2+B*(lpNorm g 2 μ)^2 := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < (p-2)/p := div_pos (by linarith) hp0
  have ht := (Real.continuous_rpow_const hq.le).continuousAt.tendsto.comp
    (power_tail_tendsto hp0 hfm hf)
  rw [Real.zero_rpow hq.ne'] at ht
  obtain ⟨j,hj⟩ := Filter.Eventually.exists (ht.eventually (eventually_lt_nhds hδ))
  refine ⟨((j:ℝ)+1)^(p-2),Real.rpow_nonneg (by positivity) _,?_⟩
  intro g hg hg2
  have hh := potential_split hp (by positivity : 0 < (j:ℝ)+1) hfm hf hg hg2
  dsimp only [Function.comp_apply] at hj
  have hb := mul_le_mul_of_nonneg_right hj.le (sq_nonneg (lpNorm g (ENNReal.ofReal p) μ))
  linarith

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma power_absorption {p A n d S C M : ℝ} (hp : 2 < p) (hA : 0 < A) (hn : 0 < n)
    (hd : 0 < d) (hS : 0 < S) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (v : Lp ℝ 2 μ) (hv : MemLp (v : α → ℝ) (ENNReal.ofReal p) μ)
    (f : ℕ → Lp ℝ 2 μ) (E : ℕ → ℝ)
    (hf : ∀ j, MemLp (f j : α → ℝ) (ENNReal.ofReal p) μ)
    (_hEv : ∀ j, 0 ≤ E j) (hMv : ∀ j, ‖f j‖^2 ≤ M)
    (hs : ∀ j, S*(lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ A*E j+C*‖f j‖^2)
    (he : ∀ j, A*d*E j ≤ n*(∫ x, |v x|^(p-2)*(f j x)^2 ∂μ)) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      (∀ j, (lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ L) ∧
      (∀ j, E j ≤ B) := by
  have hδ : 0 < d*S/(2*n) := div_pos (mul_pos hd hS) (by positivity)
  obtain ⟨K,hK,hpot⟩ := potential_small hp (Lp.stronglyMeasurable v).measurable hv hδ
  let L := 2*(n*K+d*C)*M/(d*S)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound (j : ℕ) : (lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ L := by
    have ht := hpot (f j) (hf j) (Lp.memLp (f j))
    have hnorm : lpNorm (f j : α → ℝ) 2 μ = ‖f j‖ := by
      rw [Lp.norm_def,toReal_eLpNorm]
    rw [hnorm] at ht
    have ht' := mul_le_mul_of_nonneg_left ht hn.le
    have hs' := mul_le_mul_of_nonneg_left (hs j) hd.le
    have hcoef : n*(d*S/(2*n)) = d*S/2 := by field_simp
    have hm' := mul_le_mul_of_nonneg_left (hMv j) (show 0 ≤ n*K+d*C by positivity)
    have habs : d*S*(lpNorm (f j : α → ℝ) (ENNReal.ofReal p) μ)^2 ≤ 2*(n*K+d*C)*M := by
      have he' := he j
      rw [mul_add] at ht'
      rw [←mul_assoc,hcoef] at ht'
      nlinarith
    exact (le_div_iff₀ (mul_pos hd hS)).mpr (by nlinarith)
  let V := (∫ x, |v x|^p ∂μ)^((p-2)/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  refine ⟨L,n*V*L/(A*d),hL,by positivity,hbound,?_⟩
  intro j
  have ht := mul_le_mul_of_nonneg_left (potential_holder hp hv (hf j)) hn.le
  have hb := mul_le_mul_of_nonneg_left (hbound j) (show 0 ≤ n*V by positivity)
  apply (le_div_iff₀ (mul_pos hA hd)).mpr
  have he' := he j
  dsimp [V] at hb
  nlinarith

end CAT0Fillings.ClosedCalculus
end

end OAI
