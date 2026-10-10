import OAI.Probability.FreeIsing.Brownian.FiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.UniformIsometry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid
open BrownianGrid

theorem preBrownian_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ j, StronglyMeasurable[F (t (j * k))] (H j))
    (hK : ∀ i, StronglyMeasurable[F (t i)] (K i))
    (hH2 : ∀ j, MemLp (H j) 2 P) (hK2 : ∀ i, MemLp (K i) 2 P) (n : ℕ) :
    (∫ ω, (integralSum B (fun j => t (j * k)) H n ω -
      integralSum B t K (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) *
        ∫ ω, (H (i / k) ω - K i ω) ^ 2 ∂P := by
  rw [integralSum_refinement B t H n hk]
  simpa only [integralSum, sub_mul, Finset.sum_sub_distrib] using
    BrownianFiltration.predictable_sum_isometry hB hAd hind t ht
    (fun i ω => H (i / k) ω - K i ω)
    (fun i => ((hH (i / k)).mono (F.mono (ht (Nat.div_mul_le_self i k)))).sub (hK i))
    (fun i => (hH2 (i / k)).sub (hK2 i)) (Finset.range (n * k))

theorem preBrownian_uniform_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k),
        ((uniformGrid T (n * k) (i + 1) : ℝ) - (uniformGrid T (n * k) i : ℝ)) *
          ∫ ω, (H (uniformGrid T n (i / k)) ω - H (uniformGrid T (n * k) i) ω) ^ 2 ∂P := by
  have hgrid : (fun j => uniformGrid T (n * k) (j * k)) = uniformGrid T n := by
    funext j
    exact uniformGrid_refine T hn hk j
  have hcoeff : ∀ j, StronglyMeasurable[
      F (uniformGrid T (n * k) (j * k))]
      (H (uniformGrid T n j)) := by
    intro j
    rw [uniformGrid_refine T hn hk]
    exact hH _
  simpa only [hgrid, uniformSum] using preBrownian_difference_isometry hB hAd hind
    (uniformGrid T (n * k)) (uniformGrid_mono T (n * k))
    (fun j => H (uniformGrid T n j)) (fun i => H (uniformGrid T (n * k) i)) hk
    hcoeff (fun i => hH _) (fun j => hH2 _) (fun i => hH2 _) n

theorem preBrownian_uniform_difference_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (H (uniformGrid T n (i / k)) ω -
        H (uniformGrid T (n * k) i) ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) ≤
      (T : ℝ) * ε := by
  rw [preBrownian_uniform_difference_isometry hB hAd hind H hH hH2 T hn hk]
  calc
    _ ≤ ∑ i ∈ Finset.range (n * k),
        ((uniformGrid T (n * k) (i + 1) : ℝ) - (uniformGrid T (n * k) i : ℝ)) * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (happrox i (Finset.mem_range.mp hi))
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (uniformGrid_mono T (n * k) (Nat.le_succ i)))
    _ = (T : ℝ) * ε := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (uniformGrid T (n * k) i : ℝ))]
      simp [uniformGrid_end T (Nat.mul_pos hn hk)]

theorem integralSum_memLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (_hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (n : ℕ) :
    MemLp (integralSum B t H n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact BrownianFiltration.predictable_mul_memLp_two hB (hind _ _ (ht (Nat.le_succ i))) (hH i) (hH2 i)

theorem uniformSum_memLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    MemLp (uniformSum B H T n) 2 P :=
  integralSum_memLp hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
    (fun i => H (uniformGrid T n i)) (fun _ => hH _) (fun _ => hH2 _) n

theorem preBrownian_uniform_difference_bound_of_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε δ : ℝ}
    (hmesh : (T : ℝ) / (n : ℝ) ≤ δ)
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
      (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) ≤
      (T : ℝ) * ε := by
  apply preBrownian_uniform_difference_bound hB hAd hind H hH hH2 T hn hk
  intro i hi
  apply hmod
  · exact uniformGrid_floor_le T hn hk i
  · exact uniformGrid_le_horizon T (Nat.mul_pos hn hk) hi.le
  · exact (uniformGrid_floor_sub_le T hn hk i).trans hmesh

theorem preBrownian_uniform_pair_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n m : ℕ} (hn : 0 < n) (hmn : 0 < m) {ε δ : ℝ}
    (hmeshN : (T : ℝ) / (n : ℝ) ≤ δ) (hmeshM : (T : ℝ) / (m : ℝ) ≤ δ)
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
      (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T m ω) ^ 2 ∂P) ≤
      4 * (T : ℝ) * ε := by
  have hN := preBrownian_uniform_difference_bound_of_modulus hB hAd hind H hH hH2 T hn hmn hmeshN hmod
  have hM := preBrownian_uniform_difference_bound_of_modulus hB hAd hind H hH hH2 T hmn hn hmeshM hmod
  rw [Nat.mul_comm m n] at hM
  have htriangle := integral_sq_sub_le_two (uniformSum_memLp hB hAd hind H hH hH2 T n)
    (uniformSum_memLp hB hAd hind H hH hH2 T m) (uniformSum_memLp hB hAd hind H hH hH2 T (n * m))
  linarith

def uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 P :=
  (uniformSum_memLp hB hAd hind H hH hH2 T n).toLp (uniformSum B H T n)

lemma coe_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    (uniformSumLp hB hAd hind H hH hH2 T n : Ω → ℝ) =ᵐ[P] uniformSum B H T n :=
  (uniformSum_memLp hB hAd hind H hH hH2 T n).coeFn_toLp

theorem cauchySeq_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    CauchySeq (uniformSumLp hB hAd hind H hH hH2 T) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let η := ε ^ 2 / (4 * (T : ℝ) + 1)
  have hden : 0 < 4 * (T : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨δ, hδ, hmod⟩ := hcont η hη
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  have hmesh (n : ℕ) (hn : N + 1 ≤ n) : (T : ℝ) / (n : ℝ) ≤ δ := by
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    apply (div_le_iff₀ hnR).2
    have hN' : (T : ℝ) < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show N ≤ n by omega)
    nlinarith
  refine ⟨N + 1, ?_⟩
  intro n hn m hmn
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hb := preBrownian_uniform_pair_bound hB hAd hind H hH hH2 T hn0 hm0
    (hmesh n hn) (hmesh m hmn) hmod
  have hnorm : ‖uniformSumLp hB hAd hind H hH hH2 T n - uniformSumLp hB hAd hind H hH hH2 T m‖ ^ 2 ≤
      4 * (T : ℝ) * η := by
    rw [uniformSumLp, uniformSumLp, norm_sq_toLp_sub]
    exact hb
  have hsmall : 4 * (T : ℝ) * η < ε ^ 2 := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_pos_of_pos hε]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg
    (uniformSumLp hB hAd hind H hH hH2 T n - uniformSumLp hB hAd hind H hH hH2 T m)]

theorem exists_uniformSumLp_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Lp ℝ 2 P, Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I) :=
  cauchySeq_tendsto_of_complete (cauchySeq_uniformSumLp hB hAd hind H hH hH2 T hcont)

theorem exists_uniform_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Ω → ℝ, StronglyMeasurable I ∧ MemLp I 2 P ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hAd hind H hH hH2 T hcont
  refine ⟨I, Lp.stronglyMeasurable I, Lp.memLp I, ?_⟩
  have hnorm := (hI.sub (tendsto_const_nhds (x := I))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (uniformSumLp hB hAd hind H hH hH2 T n) I,
    coe_uniformSumLp hB hAd hind H hH hH2 T n] with ω hsub hsum
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hsum]

theorem exists_uniform_integral_of_bounded_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable I ∧ MemLp I 2 P ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono (F.le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  apply exists_uniform_integral hB hAd hind H hH hH2 T
  intro ε hε
  exact MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε

theorem uniformSumLp_norm_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    ‖uniformSumLp hB hAd hind H hH hH2 T n‖ ^ 2 =
      ((T : ℝ) / n) * ∑ i ∈ Finset.range n, ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P := by
  calc
    _ = ∫ ω, (uniformSum B H T n ω) ^ 2 ∂P := by
      rw [norm_sq_L2_eq_integral]
      apply integral_congr_ae
      filter_upwards [coe_uniformSumLp hB hAd hind H hH hH2 T n] with ω hω
      rw [hω]
    _ = ∑ i ∈ Finset.range n,
        ((uniformGrid T n (i + 1) : ℝ) - (uniformGrid T n i : ℝ)) *
          ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P :=
      BrownianFiltration.predictable_sum_isometry hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
        (fun i => H (uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _) (Finset.range n)
    _ = _ := by simp_rw [uniformGrid_step]; rw [← Finset.mul_sum]

theorem uniformSumLp_limit_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    (∫ ω, (I ω) ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have henergy := EnergyRiemann.tendsto_energy_sum
    (fun t => (hH2 t).aestronglyMeasurable) hc hC hb T
  have hnorm := hI.norm.pow 2
  have henergy' : Tendsto
      (fun n => ((T : ℝ) / n) * ∑ i ∈ Finset.range n,
        ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P) atTop (𝓝 (‖I‖ ^ 2)) := by
    apply hnorm.congr'
    exact Filter.Eventually.of_forall (uniformSumLp_norm_sq hB hAd hind H hH hH2 T)
  rw [← norm_sq_L2_eq_integral]
  exact tendsto_nhds_unique henergy' henergy

end Problem367.BrownianFiltrationGrid

end

end OAI
