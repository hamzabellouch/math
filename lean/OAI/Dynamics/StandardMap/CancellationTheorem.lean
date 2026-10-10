import OAI.Dynamics.StandardMap.CancellationArea

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusCancellation (k : ℝ) (n : ℕ) (z : Torus) : Prop :=
  growthBase k^((1-1/100000000:ℝ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z (-(n:ℤ)) n‖ ∧
  growthBase k^((1-1/100000000:ℝ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z 0 n‖ ∧
  ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖ ≤ growthBase k^((1/100000000:ℝ)*(n:ℝ))
lemma isClosed_torusCancellation (k : ℝ) (n : ℕ) : IsClosed {z | torusCancellation k n z} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
    ((isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
      (isClosed_le (continuous_torusSegmentTransfer k _ _).norm continuous_const))
lemma torusSmallEndpoints_mono (k : ℝ) (Np Nm : ℕ) {R S : ℝ} (hRS : R≤S) (z : Torus)
    (h : torusSmallEndpoints k Np Nm R z) : torusSmallEndpoints k Np Nm S z := by
  obtain ⟨b,hb,hm,hp⟩ := h
  exact ⟨b,hb,hm.trans hRS,hp.trans hRS⟩
lemma torusCancellation_sub_small (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 1≤n) :
    {z | torusCancellation k n z} ⊆
      {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ∪
      ((torusStep k).symm ⁻¹' {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z}) := by
  intro z hz
  obtain ⟨u,hu,hm,hp⟩ := torus_cancellation_vector k hk n (1/100000000) (by norm_num) z hz.1 hz.2.2
  have hM : 1≤growthBase k := by linarith [growthBase_ge_four k hk]
  have hR : 0≤growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) := Real.rpow_nonneg (by linarith) _
  have hRS : 2*growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) ≤
      3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hM
      (show -((1-2*(1/100000000:ℝ))*(n:ℝ)) ≤ -((1-3/100000000:ℝ)*(n:ℝ)) by
        nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    nlinarith [Real.rpow_nonneg (show 0≤growthBase k by linarith) (-((1-3/100000000:ℝ)*(n:ℝ)))]
  rcases torus_small_normalize k hk n hn _ hR z u hu hm hp with h|h
  · exact Or.inl (torusSmallEndpoints_mono _ _ _ hRS _ h)
  · exact Or.inr (torusSmallEndpoints_mono _ _ _ hRS _ h)
lemma eventually_cancellation_area_large :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ, 10000000≤n →
      area {z | torusCancellation k n z} ≤ 2*ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  have hp := hM k hk hMk n n (n+1) hn ⟨le_rfl,by omega⟩ ⟨by omega,le_rfl⟩
  have hm := hM k hk hMk n (n+1) n hn ⟨by omega,le_rfl⟩ ⟨le_rfl,by omega⟩
  have hmp : MeasurePreserving (torusStep k).symm area area := measurePreserving_torusStep_symm k
  calc
    _ ≤ _ := measure_mono (torusCancellation_sub_small k hk.le n (by omega))
    _ ≤ _ := measure_union_le _ _
    _ = area {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} +
        area {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} := by
      rw [hmp.measure_preimage (isClosed_torusSmallEndpoints _ _ _ _).measurableSet.nullMeasurableSet]
    _ ≤ _ := by rw [two_mul]; exact add_le_add hp hm
noncomputable def cancellationConstant : ℝ := 2*(4:ℝ)^10000000
lemma cancellationConstant_pos : 0<cancellationConstant := by unfold cancellationConstant; positivity
lemma eventually_cancellation_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ,
      area {z | torusCancellation k n z} ≤ ENNReal.ofReal (cancellationConstant*(1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area_large
  refine ⟨M₀,?_⟩
  intro k hk hMk n
  by_cases hn : 10000000≤n
  · apply (hM k hk hMk n hn).trans
    have hc : 2≤cancellationConstant := by
      have hp : (1:ℝ)≤4^10000000 := one_le_pow₀ (by norm_num)
      simpa only [mul_one,cancellationConstant] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)
    rw [ENNReal.ofReal_mul cancellationConstant_pos.le]
    exact mul_le_mul_of_nonneg_right (by simpa using ENNReal.ofReal_le_ofReal hc) bot_le
  · have hprob : area {z | torusCancellation k n z}≤1 := by
      calc
        _≤area univ := measure_mono (subset_univ _)
        _=1 := measure_univ
    apply hprob.trans
    have he : (4:ℝ)^n*(1/4:ℝ)^n=1 := by rw [← mul_pow]; norm_num
    have hp := pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) (show n≤10000000 by omega)
    have hc : 1≤cancellationConstant*(1/4:ℝ)^n := by
      have hh := mul_le_mul_of_nonneg_right hp (show 0≤(1/4:ℝ)^n by positivity)
      rw [he] at hh
      have h2 := mul_le_mul_of_nonneg_right (show (1:ℝ)≤2 by norm_num)
        (show 0≤(4:ℝ)^10000000*(1/4:ℝ)^n by positivity)
      simpa only [one_mul,cancellationConstant,mul_assoc] using hh.trans (by simpa only [one_mul] using h2)
    simpa using ENNReal.ofReal_le_ofReal hc
end StandardMapEntropy

end OAI
