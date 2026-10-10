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
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory Set Filter
open scoped Topology BigOperators

lemma monotone_weighted_grid_bound {γ f : ℝ → ℝ} {T δ K ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (hK : 0≤K) (horizon : (N : ℝ)*δ=T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K)
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in (0 : ℝ)..T, γ t*f t| ≤ T*γ T*ε+δ*K*(γ T-γ 0) := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm (j : ℕ) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs (j : ℕ) (hj : j<N) : Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨(hm j hj.le).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle (j : ℕ) : (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
  have hint0 : IntervalIntegrable (fun t ↦ γ t*f t) volume 0 T := by
    apply MonotoneOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hγ) |>.mul_continuousOn
    simpa only [uIcc_of_le hT] using hf
  have hint (j : ℕ) (hj : j<N) : IntervalIntegrable (fun t ↦ γ t*f t) volume
      ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) :=
    hint0.mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc (hm j hj.le) (hm (j+1) (by omega)))
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t) =
      ∫ t in (0 : ℝ)..T, γ t*f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc (j : ℕ) (hj : j<N) :
      |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
        ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| ≤
      δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) := by
    let a := (j : ℝ)*δ
    let b := ((j+1 : ℕ) : ℝ)*δ
    have hγa : 0≤γ a := hγ0.trans (hγ ⟨le_rfl,hT⟩ (hm j hj.le) (hm j hj.le).1)
    have hγaT : γ a≤γ T := hγ (hm j hj.le) ⟨hT,le_rfl⟩ (hm j hj.le).2
    have hc : (∫ t in a..b, γ a*f a-γ t*f t) =
        δ*(γ a*f a)-∫ t in a..b, γ t*f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      dsimp only [a,b]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hwidth : b-a=δ := by dsimp only [a,b]; push_cast; ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := γ T*ε+K*(γ b-γ a))
      (f := fun t ↦ γ a*f a-γ t*f t) (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        have htstrip := hs j hj ⟨ht.1.le,ht.2⟩
        have hag : γ a≤γ t := hγ (hm j hj.le) htstrip ht.1.le
        have hgb : γ t≤γ b := hγ htstrip (hm (j+1) (by omega)) ht.2
        have hmod' : |f a-f t|≤ε := hmod a (hm j hj.le) t htstrip (by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
          have htb : t≤b := ht.2
          linarith)
        rw [Real.norm_eq_abs]
        calc
          _ = |γ a*(f a-f t)-(γ t-γ a)*f t| := by congr 1; ring
          _ ≤ |γ a*(f a-f t)|+|(γ t-γ a)*f t| := abs_sub _ _
          _ = γ a*|f a-f t|+(γ t-γ a)*|f t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hγa, abs_of_nonneg (sub_nonneg.mpr hag)]
          _ ≤ γ T*ε+K*(γ b-γ a) := by
            have hfirst : γ a*|f a-f t|≤γ T*ε :=
              (mul_le_mul_of_nonneg_right hγaT (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hmod' (hγa.trans hγaT))
            have hsecond : (γ t-γ a)*|f t|≤K*(γ b-γ a) := by
              calc
                _ ≤ (γ t-γ a)*K := mul_le_mul_of_nonneg_left (hfB t htstrip) (sub_nonneg.mpr hag)
                _ ≤ (γ b-γ a)*K := mul_le_mul_of_nonneg_right (sub_le_sub_right hgb _) hK
                _ = _ := mul_comm _ _
            exact add_le_add hfirst hsecond)
    rw [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    exact hb.trans_eq (mul_comm _ _)
  calc
    _ = |∑ j ∈ Finset.range N, (δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) :=
      Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*γ T*ε+δ*K*(γ T-γ 0) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, mul_assoc]
      rw [Finset.sum_range_sub (fun j ↦ γ ((j : ℝ)*δ))]
      simp only [Nat.cast_zero,zero_mul,horizon]
      rw [← mul_assoc (N : ℝ) δ, horizon]

lemma monotone_weighted_grid_tendsto {γ f : ℝ → ℝ} {T K : ℝ}
    (hT : 0<T) (hK : 0≤K) (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, γ ((j : ℝ)*(T/N))*f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT.le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T*γ T+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hηeq : η*(2*(T*γ T+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hηb : T*γ T*η<ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ (T/N)*K*(γ T-γ 0)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hδ.mul_const K).mul_const (γ T-γ 0)
  filter_upwards [hδ.eventually_le_const hθ, htail.eventually_lt_const (half_pos hε),
    eventually_gt_atTop 0] with N hNθ hNe hN
  rw [Real.dist_eq]
  have hb := monotone_weighted_grid_bound (N := N) (div_nonneg hT.le (Nat.cast_nonneg N)) hK
    (by
      have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp)
    hγ hγ0 hf hfB (fun s hs t ht hst ↦ by
      have hh := hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ)
      simpa only [Real.dist_eq] using hh)
  exact hb.trans_lt (by nlinarith)

end SKValue

end

end OAI
