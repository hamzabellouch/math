import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Estimates.MeanSquareContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

lemma norm_sq_L2_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma norm_sq_toLp_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with ω hsub hfw hgw
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hfw, hgw]

def uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 P :=
  (uniformSum_memLp hB hm H hH hH2 T n).toLp (uniformSum B H T n)

lemma coe_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    (uniformSumLp hB hm H hH hH2 T n : Ω → ℝ) =ᵐ[P] uniformSum B H T n :=
  (uniformSum_memLp hB hm H hH hH2 T n).coeFn_toLp

theorem cauchySeq_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    CauchySeq (uniformSumLp hB hm H hH hH2 T) := by
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
  have hb := preBrownian_uniform_pair_bound hB hm H hH hH2 T hn0 hm0
    (hmesh n hn) (hmesh m hmn) hmod
  have hnorm : ‖uniformSumLp hB hm H hH hH2 T n - uniformSumLp hB hm H hH hH2 T m‖ ^ 2 ≤
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
    (uniformSumLp hB hm H hH hH2 T n - uniformSumLp hB hm H hH hH2 T m)]

theorem exists_uniformSumLp_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Lp ℝ 2 P, Tendsto (uniformSumLp hB hm H hH hH2 T) atTop (𝓝 I) :=
  cauchySeq_tendsto_of_complete (cauchySeq_uniformSumLp hB hm H hH hH2 T hcont)

theorem exists_uniform_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Ω → ℝ, StronglyMeasurable I ∧ MemLp I 2 P ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hm H hH hH2 T hcont
  refine ⟨I, Lp.stronglyMeasurable I, Lp.memLp I, ?_⟩
  have hnorm := (hI.sub (tendsto_const_nhds (x := I))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (uniformSumLp hB hm H hH hH2 T n) I,
    coe_uniformSumLp hB hm H hH hH2 T n] with ω hsub hsum
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hsum]

theorem exists_uniform_integral_of_bounded_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable I ∧ MemLp I 2 P ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono ((Filtration.natural B hm).le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  apply exists_uniform_integral hB hm H hH hH2 T
  intro ε hε
  exact MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε

end Problem367.BrownianGrid

end

end OAI
