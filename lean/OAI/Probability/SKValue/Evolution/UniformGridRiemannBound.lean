import Mathlib

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SKValue

lemma uniform_grid_riemann_bound {f : ℝ → ℝ} {T δ ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (horizon : (N : ℝ)*δ=T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, f ((j : ℝ)*δ))-∫ t in (0 : ℝ)..T, f t| ≤ T*ε := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm : ∀ j≤N, (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    intro j hj
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs : ∀ j<N, Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro j hj t ht
    exact ⟨(hm j (by omega)).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle : ∀ j : ℕ, (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by
    intro j
    push_cast
    nlinarith
  have hint : ∀ j<N, IntervalIntegrable f volume ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) := by
    intro j hj
    apply (hf.mono (hs j hj)).intervalIntegrable_of_Icc (hjle j)
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t) =
      ∫ t in (0 : ℝ)..T, f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc : ∀ j<N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t|≤δ*ε := by
    intro j hj
    have hc : (∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f ((j : ℝ)*δ)-f t) =
        δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ)*δ) (b := ((j+1 : ℕ) : ℝ)*δ) (C := ε)
      (f := fun t ↦ f ((j : ℝ)*δ)-f t)
      (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        rw [Real.norm_eq_abs]
        apply hmod _ (hm j (by omega)) t (hs j hj ⟨ht.1.le,ht.2⟩)
        rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
        push_cast at ht
        nlinarith [ht.2])
    have hwidth : (((j+1 : ℕ) : ℝ)*δ)-(j : ℝ)*δ=δ := by push_cast; ring
    simp only [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    simpa only [mul_comm] using hb
  calc
    _ = |∑ j ∈ Finset.range N, (δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*ε := Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*ε := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ←mul_assoc, horizon]

lemma uniform_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε/(2*T)) (div_pos hε (by positivity))
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  filter_upwards [hδ.eventually_le_const hθ, eventually_gt_atTop 0] with N hNθ hN
  have horizon : (N : ℝ)*(T/N) = T := by field_simp
  have h := uniform_grid_riemann_bound (div_nonneg hT.le (Nat.cast_nonneg _)) horizon hf
    (fun s hs t ht hst ↦ by
      simpa only [Real.dist_eq] using hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ))
  rw [Real.dist_eq]
  apply h.trans_lt
  have : T*(ε/(2*T))=ε/2 := by field_simp
  rw [this]
  exact half_lt_self hε

lemma shifted_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1)))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have hfull := (uniform_grid_riemann_tendsto hT hf).comp (tendsto_add_atTop_nat 1)
  have hδ : Tendsto (fun N : ℕ ↦ T/((N : ℝ)+1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have heq (N : ℕ) : (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1)))) =
      (T/(N+1))*(∑ j ∈ Finset.range (N+1), f ((j : ℝ)*(T/(N+1))))-(T/(N+1))*f 0 := by
    rw [←Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, Fin.val_succ]
    ring
  simp_rw [heq]
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, zero_mul, sub_zero] using hfull.sub (hδ.mul_const (f 0))

lemma perturbed_shifted_grid_tendsto {f : ℝ → ℝ} {T : ℝ}
    {v : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hr : ∀ N, 0≤r N) (hr0 : Tendsto r atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, ∀ i : Fin N, |v N i-f ((i+1 : ℕ)*(T/(N+1)))|≤r N) :
    Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, v N i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have herr : Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, v N i)-
      (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1))))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*r N)
    · filter_upwards [hv] with N hN
      have hδ : 0≤T/((N : ℝ)+1) := by positivity
      have hmul : (T/((N : ℝ)+1))*(N : ℝ)≤T := by
        have hden : (0 : ℝ)<(N : ℝ)+1 := by positivity
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).mpr
        nlinarith [mul_nonneg hT.le (Nat.cast_nonneg N)]
      rw [Real.norm_eq_abs, ←mul_sub, ←Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hδ]
      calc
        _ ≤ (T/(N+1))*(∑ _ : Fin N, r N) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ hN i))
        _ = ((T/(N+1))*(N : ℝ))*r N := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ T*r N := mul_le_mul_of_nonneg_right hmul (hr N)
    · simpa only [mul_zero] using hr0.const_mul T
  have h := herr.add (shifted_grid_riemann_tendsto hT hf)
  simpa only [sub_add_cancel, zero_add] using h

end SKValue

end

end OAI
