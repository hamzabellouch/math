import OAI.Dynamics.StandardMap.VectorGrowth

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def torusFastBridge (k : ℝ) (z : Torus) (N : ℕ) : Prop :=
  growthBase k^((999/1000:ℝ)*(N:ℝ))≤‖torusSegmentTransfer k z 0 N‖
lemma measurableSet_torusFastBridge (k : ℝ) (N : ℕ) : MeasurableSet {z | torusFastBridge k z N} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 N).norm).measurableSet
noncomputable def torusGoodMiddles (k : ℝ) (z : Torus) (N : ℕ) : Finset ℕ := by
  classical
  exact (bridgeMiddle N).filter (fun i => torusIter k (i:ℤ) z∈middlePrefixEvent k (N-i) i)
lemma torus_good_middles_count (k : ℝ) (hk : 0≤k) (N : ℕ) (hN : 100≤N)
    (z : Torus) (hz : torusFastBridge k z N) :
    (N:ℝ)/5≤(torusGoodMiddles k z N).card := by
  classical
  obtain ⟨u,hu,huN⟩ := exists_unit_opNorm (torusSegmentTransfer k z 0 N)
  have hu0 : u≠0 := by intro he; simp [he] at hu
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have hlog := Real.log_pos hM
  let zlog := transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u
  have htotal : (999/1000:ℝ)*(N:ℝ)≤zlog N-zlog 0 := by
    have hh := Real.le_log_of_rpow_le (by linarith : 0 < growthBase k) hz
    dsimp only [zlog,transferVectorLog]
    change _≤Real.log ‖torusSegmentTransfer k z 0 N u‖/Real.log (growthBase k)-Real.log ‖u‖/Real.log (growthBase k)
    rw [huN,hu,Real.log_one,zero_div,sub_zero]
    exact (le_div_iff₀ hlog).mpr hh
  have hcount := middle_log_good_count zlog N hN (fun j _ =>
    transferVectorLog_step (growthBase k) hM _ u hu0 j (by
      obtain ⟨w,rfl⟩ := liftProjection_surjective z
      rw [torusSegmentCoefficient_lift]
      exact liftSegmentCoefficient_bound k hk w 0 (j+1))) htotal
  apply hcount.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hg⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hi,?_⟩
  exact torus_middle_prefix_of_vector k hk z N i (bridgeMiddle_bounds N i hN hi).2.2.2.2 u hu0 hg
lemma lintegral_count_cover {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i∈s, MeasurableSet (E i)) (F : Set X) (hF : MeasurableSet F)
    (w : X → ℝ≥0∞) (hw : Measurable w) (a : ℝ)
    (hcount : ∀ z∈F, a≤(s.filter (fun i => z∈E i)).card) :
    ENNReal.ofReal a*(∫⁻ z in F, w z ∂μ)≤∑ i∈s, ∫⁻ z in E i, w z ∂μ := by
  classical
  have hpoint (z : X) : ENNReal.ofReal a*F.indicator w z≤∑ i∈s, (E i).indicator w z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      have he : (∑ i∈s, (E i).indicator w z)=((s.filter (fun i => z∈E i)).card:ℝ≥0∞)*w z := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
      rw [he]
      apply mul_le_mul_of_nonneg_right _ bot_le
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcount z hz)
    · simp only [Set.indicator_of_notMem hz,mul_zero]
      exact bot_le
  have hh := lintegral_mono hpoint (μ:=μ)
  rw [lintegral_const_mul _ (hw.indicator hF)] at hh
  rw [lintegral_indicator hF] at hh
  rw [lintegral_finsetSum _ (fun i hi => hw.indicator (hE i hi))] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator (hE i hi) _
end StandardMapEntropy

end OAI
