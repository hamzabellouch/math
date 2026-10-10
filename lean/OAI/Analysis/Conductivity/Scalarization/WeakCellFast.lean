import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section
noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma integral_norm_le_L2_const
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → V} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖(memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _‖ * ‖hf.toLp _‖ := by
  let oneLp := (memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _
  let nLp := hf.norm.toLp _
  have heq : (∫ x, ‖f x‖ ∂μ) = inner ℝ oneLp nLp := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (p := 2) (μ := μ) (1 : ℝ)).coeFn_toLp,hf.norm.coeFn_toLp] with x hx hy
    change ‖f x‖ = inner ℝ (oneLp x) (nLp x)
    rw [hx,hy,real_inner_comm]
    simp
  rw [heq]
  calc
    _ ≤ |inner ℝ oneLp nLp| := le_abs_self _
    _ ≤ ‖oneLp‖ * ‖nLp‖ := abs_real_inner_le_norm _ _
    _ = _ := by
      rw [show ‖nLp‖ = ‖hf.toLp _‖ by
        simp only [nLp, Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]]

lemma compact_inner_right
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : X → V} (hc : HasCompactSupport f) (φ : X → V) :
    HasCompactSupport (fun x => inner ℝ (φ x) (f x)) := by
  apply hc.mono
  intro x hx hn
  exact hx (by change inner ℝ (φ x) (f x) = 0; rw [hn,inner_zero_right])

lemma vector_pairing_bound_of_zero_mean
    {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f φ : X → V) (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : Continuous φ) (hmean : (∫ x, f x ∂μ) = 0)
    {c : V} {ω : ℝ} (hosc : ∀ x ∈ tsupport f, ‖φ x-c‖ ≤ ω) :
    |∫ x, inner ℝ (φ x) (f x) ∂μ| ≤ ω * ∫ x, ‖f x‖ ∂μ := by
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have h1 : Integrable (fun x => inner ℝ (φ x) (f x)) μ :=
    (hφ.inner hf).integrable_of_hasCompactSupport (compact_inner_right hc _)
  have h2 : Integrable (fun x => inner ℝ (φ x-c) (f x)) μ :=
    ((hφ.sub continuous_const).inner hf).integrable_of_hasCompactSupport (compact_inner_right hc _)
  have he : (∫ x, inner ℝ (φ x) (f x) ∂μ) = ∫ x, inner ℝ (φ x-c) (f x) ∂μ := by
    simp_rw [inner_sub_left]
    rw [integral_sub h1 (hfi.const_inner c),integral_inner hfi c,hmean,inner_zero_right,sub_zero]
  rw [he]
  calc
    _ ≤ ∫ x, |inner ℝ (φ x-c) (f x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ω * ‖f x‖ ∂μ := by
      apply integral_mono_ae h2.abs (hfi.norm.const_mul ω)
      exact Eventually.of_forall fun x => by
        change |inner ℝ (φ x-c) (f x)| ≤ ω * ‖f x‖
        by_cases hx : x ∈ tsupport f
        · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hosc x hx) (norm_nonneg _))
        · rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_right,norm_zero,abs_zero,mul_zero]
    _ = _ := integral_const_mul _ _

lemma norm_finite_disjoint_sum
    {ι X V : Type*} [Fintype ι] [TopologicalSpace X] [NormedAddCommGroup V]
    (f : ι → X → V) (hd : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j)))) (x : X) :
    ‖∑ i, f i x‖ = ∑ i, ‖f i x‖ := by
  classical
  by_cases h : ∃ i, f i x ≠ 0
  · obtain ⟨i,hi⟩ := h
    have hz : ∀ j, j ≠ i → f j x = 0 := by
      intro j hji
      by_contra hj
      exact Set.disjoint_left.mp (hd hji) (subset_closure hj) (subset_closure hi)
    rw [Finset.sum_eq_single i,Finset.sum_eq_single i]
    · intro j _ hji; rw [hz j hji,norm_zero]
    · simp
    · intro j _ hji; exact hz j hji
    · simp
  · push Not at h
    simp only [h,Finset.sum_const_zero,norm_zero]

lemma finite_cell_pairing_bound
    {ι X V : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : ι → X → V) (φ : X → V)
    (hf : ∀ i, Continuous (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (hφ : Continuous φ) (hmean : ∀ i, (∫ x, f i x ∂μ) = 0)
    (hd : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (c : ι → V) {ω : ℝ} (hosc : ∀ i x, x ∈ tsupport (f i) → ‖φ x-c i‖ ≤ ω) :
    |∫ x, inner ℝ (φ x) (∑ i, f i x) ∂μ| ≤ ω * ∫ x, ‖∑ i, f i x‖ ∂μ := by
  classical
  simp_rw [inner_sum]
  rw [integral_finsetSum _ (fun i _ => (hφ.inner (hf i)).integrable_of_hasCompactSupport (compact_inner_right (hc i) _))]
  calc
    _ ≤ ∑ i, |∫ x, inner ℝ (φ x) (f i x) ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ω * ∫ x, ‖f i x‖ ∂μ := Finset.sum_le_sum fun i _ =>
      vector_pairing_bound_of_zero_mean μ (f i) φ (hf i) (hc i) hφ (hmean i) (hosc i)
    _ = _ := by
      rw [← Finset.mul_sum,← integral_finsetSum _ (fun i _ => ((hf i).integrable_of_hasCompactSupport (hc i)).norm)]
      simp_rw [norm_finite_disjoint_sum f hd]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma fine_cell_pairing_bound
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) (φ : X → V) (hφ : Continuous φ)
    {ω : ℝ} (hω : 0 < ω) :
    ∃ δ > 0, ∀ (N : ℕ) (f : Fin N → X → V) (center : Fin N → X),
      (∀ i, Continuous (f i)) → (∀ i, HasCompactSupport (f i)) →
      (∀ i, (∫ x, f i x ∂μ) = 0) →
      Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))) →
      (∀ i, tsupport (f i) ⊆ K) →
      (∀ i, tsupport (f i) ⊆ Metric.ball (center i) δ) →
      |∫ x, inner ℝ (φ x) (∑ i, f i x) ∂μ| ≤ ω * ∫ x, ‖∑ i, f i x‖ ∂μ := by
  classical
  obtain ⟨d,hd,hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hφ.continuousOn) ω hω
  refine ⟨d/2,by positivity,?_⟩
  intro N f center hf hc hmean hdis hsK hsball
  have hex : ∀ i, ∃ c : V, ∀ x ∈ tsupport (f i), ‖φ x-c‖ ≤ ω := by
    intro i
    by_cases hi : (tsupport (f i)).Nonempty
    · obtain ⟨z,hz⟩ := hi
      refine ⟨φ z,fun x hx => ?_⟩
      have hdist : dist x z < d := by
        have h1 := hsball i hx
        have h2 := hsball i hz
        rw [Metric.mem_ball] at h1 h2
        have hh := dist_triangle_right x z (center i)
        linarith
      have hh : ‖φ x - φ z‖ < ω := by
        simpa only [dist_eq_norm] using hcont x (hsK i hx) z (hsK i hz) hdist
      exact hh.le
    · exact ⟨0,fun x hx => (hi ⟨x,hx⟩).elim⟩
  choose c hc' using hex
  exact finite_cell_pairing_bound μ f φ hf hc hφ hmean hdis c hc'

lemma inner_tendsto_zero_of_dense_tests
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : W → V) (hT : DenseRange T) (z : ℕ → V)
    {C : ℝ} (hC : 0 ≤ C) (hz : ∀ n, ‖z n‖ ≤ C)
    (ht : ∀ w, Tendsto (fun n => inner ℝ (T w) (z n)) atTop (𝓝 0)) :
    ∀ v, Tendsto (fun n => inner ℝ v (z n)) atTop (𝓝 0) := by
  intro v
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨w,hw⟩ := hT.exists_dist_lt v (show 0 < ε/(2*(C+1)) by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ht w) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have he : inner ℝ v (z n) = inner ℝ (v-T w) (z n) + inner ℝ (T w) (z n) := by
    rw [inner_sub_left]; ring
  rw [Real.dist_eq, sub_zero, he]
  calc
    _ ≤ |inner ℝ (v-T w) (z n)| + |inner ℝ (T w) (z n)| := abs_add_le _ _
    _ ≤ ‖v-T w‖ * C + |inner ℝ (T w) (z n)| := by
      gcongr
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hz n) (norm_nonneg _))
    _ < ε := by
      have htest : |inner ℝ (T w) (z n)| < ε/2 := by
        simpa only [Real.dist_eq,sub_zero] using hN n hn
      rw [dist_eq_norm] at hw
      have hmul := mul_le_mul_of_nonneg_right hw.le hC
      have hd : ε/(2*(C+1))*C < ε/2 := by
        have hpos : 0 < 2*(C+1) := by positivity
        have hdiv := (div_lt_iff₀ hpos).mpr (show ε*C < (ε/2)*(2*(C+1)) by nlinarith)
        simpa only [div_mul_eq_mul_div] using hdiv
      linarith

lemma fine_cells_continuous_pairing_tendsto_zero
    {X V : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K)
    (N : ℕ → ℕ) (f : (n : ℕ) → Fin (N n) → X → V)
    (center : (n : ℕ) → Fin (N n) → X)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ n i, Continuous (f n i)) (hc : ∀ n i, HasCompactSupport (f n i))
    (hmean : ∀ n i, (∫ x, f n i x ∂μ) = 0)
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (tsupport (f n i)) (tsupport (f n j))))
    (hsK : ∀ n i, tsupport (f n i) ⊆ K)
    (hsball : ∀ n i, tsupport (f n i) ⊆ Metric.ball (center n i) (δ n))
    (hLp : ∀ n, MemLp (fun x => ∑ i, f n i x) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ‖(hLp n).toLp _‖ ≤ C)
    (φ : X → V) (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, inner ℝ (φ x) (∑ i, f n i x) ∂μ) atTop (𝓝 0) := by
  let M : ℝ := ‖(memLp_const (p := 2) (μ := μ) (1 : ℝ)).toLp _‖
  have hM : 0 ≤ M := norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ω := ε/(M*C+1)
  have hω : 0 < ω := div_pos hε (by positivity)
  obtain ⟨d,hd,hfine⟩ := fine_cell_pairing_bound μ hK φ hφ hω
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp ((tendsto_order.mp hδ).2 d hd)
  refine ⟨n₀,fun n hn => ?_⟩
  have hs : ∀ i, tsupport (f n i) ⊆ Metric.ball (center n i) d := fun i x hx =>
    (Metric.ball_subset_ball (hn₀ n hn).le) (hsball n i hx)
  have hp := hfine (N n) (f n) (center n) (hf n) (hc n) (hmean n) (hdis n) (hsK n) hs
  have hl : (∫ x, ‖∑ i, f n i x‖ ∂μ) ≤ M*C :=
    (integral_norm_le_L2_const μ (hLp n)).trans
      (mul_le_mul_of_nonneg_left (hbound n) hM)
  rw [Real.dist_eq,sub_zero]
  apply lt_of_le_of_lt (hp.trans (mul_le_mul_of_nonneg_left hl hω.le))
  change ε/(M*C+1)*(M*C) < ε
  have hpos : 0 < M*C+1 := by positivity
  have hdiv := (div_lt_iff₀ hpos).mpr (show ε*(M*C) < ε*(M*C+1) by nlinarith)
  simpa only [div_mul_eq_mul_div] using hdiv

end ScalarConductivity

end
end

end OAI
