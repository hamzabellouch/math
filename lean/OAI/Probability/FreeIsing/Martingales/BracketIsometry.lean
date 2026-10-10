import OAI.Probability.FreeIsing.Martingales.QuadraticVariation
import OAI.Probability.FreeIsing.Martingales.TransformL2

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.MartingaleBracketIsometry

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_sq_mul {H D : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hH : AEStronglyMeasurable H μ) (hD : Integrable D μ)
    (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    Integrable (fun ω => H ω ^ 2 * D ω) μ := by
  apply hD.bdd_mul (c := K ^ 2) (hH.pow 2)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, Pi.pow_apply, abs_sq, sq_abs] using
    (sq_le_sq₀ (abs_nonneg (H ω)) hK).2 hω

theorem integral_sq_mul_increment [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    (∫ ω, (H ω * (M t ω - M s ω)) ^ 2 ∂μ) =
      ∫ ω, H ω ^ 2 * (A t ω - A s ω) ∂μ := by
  have hHae : AEStronglyMeasurable H μ := (hH.mono (F.le s)).aestronglyMeasurable
  have hD2 := (hM2 t).sub (hM2 s)
  have hHD2 : MemLp (fun ω => H ω * (M t ω - M s ω)) 2 μ :=
    MartingaleTransformL2.bounded_mul_memLp_two hHae hD2 hbound
  have hAint : Integrable (fun ω => A t ω - A s ω) μ :=
    (MartingaleQuadraticVariation.integrable_compensator hQ hM2 t).sub
      (MartingaleQuadraticVariation.integrable_compensator hQ hM2 s)
  have hHAint := integrable_sq_mul hK hHae hAint hbound
  have herr := MartingaleQuadraticVariation.integrable_squareError hQ hM2 s t
  have hHEint := integrable_sq_mul hK hHae herr hbound
  have hzero := SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero
    (F.le s) (hH.pow 2) herr hHEint
    (MartingaleQuadraticVariation.condExp_squareError_eq_zero hM hQ hM2 hst)
  have hident : (fun ω => H ω ^ 2 *
      MartingaleQuadraticVariation.squareError M A s t ω) =
      (fun ω => (H ω * (M t ω - M s ω)) ^ 2) -
        (fun ω => H ω ^ 2 * (A t ω - A s ω)) := by
    funext ω
    simp only [MartingaleQuadraticVariation.squareError,
      MartingaleQuadraticVariation.increment, Pi.sub_apply]
    ring
  simp only [Pi.pow_apply] at hzero
  rw [hident] at hzero
  change (∫ ω, (H ω * (M t ω - M s ω)) ^ 2 -
    H ω ^ 2 * (A t ω - A s ω) ∂μ) = 0 at hzero
  rw [integral_sub hHD2.integrable_sq hHAint] at hzero
  exact sub_eq_zero.mp hzero

theorem integral_sq_transform [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, H i ω ^ 2 * (A (i + 1) ω - A i ω) ∂μ := by
  rw [MartingaleTransformL2.integral_sq_transform hM hM2 hH hbound]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_sq_mul_increment hM hQ hM2 (Nat.le_succ i) (hH i) hK (hbound i)

theorem integral_sq_transform_le_random_envelope [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) {R : Ω → ℝ} (hR : Integrable R μ)
    (hRnonneg : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hEnvelope : ∀ᵐ ω ∂μ, ∀ i ∈ s, H i ω ^ 2 ≤ R ω)
    (hA : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ A (i + 1) ω - A i ω)
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, (∑ i ∈ s, (A (i + 1) ω - A i ω)) ≤ C) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤
      C * ∫ ω, R ω ∂μ := by
  have hint (i : ℕ) : Integrable (fun ω => H i ω ^ 2 *
      (A (i + 1) ω - A i ω)) μ :=
    integrable_sq_mul hK ((hH i).mono (F.le i)).aestronglyMeasurable
      ((MartingaleQuadraticVariation.integrable_compensator hQ hM2 (i + 1)).sub
        (MartingaleQuadraticVariation.integrable_compensator hQ hM2 i)) (hbound i)
  rw [integral_sq_transform hM hQ hM2 hH hK hbound,
    ← integral_finsetSum s (fun i _ => hint i), ← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum s (fun i _ => hint i)) (hR.const_mul C)
  filter_upwards [hRnonneg, hEnvelope, hA, htotal] with ω hRω hEω hAω htω
  calc
    (∑ i ∈ s, H i ω ^ 2 * (A (i + 1) ω - A i ω)) ≤
        ∑ i ∈ s, R ω * (A (i + 1) ω - A i ω) := by
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_right (hEω i hi) (hAω i hi))
    _ = R ω * (∑ i ∈ s, (A (i + 1) ω - A i ω)) := by rw [Finset.mul_sum]
    _ ≤ R ω * C := mul_le_mul_of_nonneg_left htω hRω
    _ = C * R ω := mul_comm _ _

theorem integral_sq_grid_transform [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, H i ω ^ 2 * (A (t (i + 1)) ω - A (t i) ω) ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable (t i), fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  have hQG : Martingale (fun i ω => M (t i) ω ^ 2 - A (t i) ω) G μ :=
    ⟨fun i => hQ.stronglyMeasurable (t i), fun _ _ hij => hQ.condExp_ae_eq (ht hij)⟩
  exact integral_sq_transform hMG hQG (fun i => hM2 (t i)) hH hK hbound s

theorem integral_sq_grid_transform_le_random_envelope [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (n : ℕ) {R : Ω → ℝ} (hR : Integrable R μ)
    (hRnonneg : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hEnvelope : ∀ᵐ ω ∂μ, ∀ i < n, H i ω ^ 2 ≤ R ω)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun u => A u ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A (t n) ω - A (t 0) ω ≤ C) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) ≤
      C * ∫ ω, R ω ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable (t i), fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  have hQG : Martingale (fun i ω => M (t i) ω ^ 2 - A (t i) ω) G μ :=
    ⟨fun i => hQ.stronglyMeasurable (t i), fun _ _ hij => hQ.condExp_ae_eq (ht hij)⟩
  apply integral_sq_transform_le_random_envelope hMG hQG
    (fun i => hM2 (t i)) hH hK hbound (Finset.range n) hR hRnonneg
  · filter_upwards [hEnvelope] with ω hω
    exact fun i hi => hω i (Finset.mem_range.mp hi)
  · filter_upwards [hA] with ω hω
    exact fun i _ => sub_nonneg.mpr (hω (ht (Nat.le_succ i)))
  · filter_upwards [htotal] with ω hω
    have htel : (∑ i ∈ Finset.range n, (A (t (i + 1)) ω - A (t i) ω)) =
        A (t n) ω - A (t 0) ω := by
      clear hEnvelope htotal hω
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    simpa only [htel] using hω

theorem tendsto_integral_sq_grid_transform [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k))
    (H : ℕ → ℕ → Ω → ℝ) (hH : ∀ k i, StronglyMeasurable[F (t k i)] (H k i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ k i, ∀ᵐ ω ∂μ, |H k i ω| ≤ K)
    (N : ℕ → ℕ) {R : ℕ → Ω → ℝ} (hR : ∀ k, Integrable (R k) μ)
    (hRnonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ R k ω)
    (hEnvelope : ∀ k, ∀ᵐ ω ∂μ, ∀ i < N k, H k i ω ^ 2 ≤ R k ω)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun u => A u ω))
    {C : ℝ} (htotal : ∀ k, ∀ᵐ ω ∂μ, A (t k (N k)) ω - A (t k 0) ω ≤ C)
    (hlim : Tendsto (fun k => ∫ ω, R k ω ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (∑ i ∈ Finset.range (N k),
      H k i ω * (M (t k (i + 1)) ω - M (t k i) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun ω => sq_nonneg _))
    (fun k => ?_) (by simpa using hlim.const_mul C)
  exact integral_sq_grid_transform_le_random_envelope hM hQ hM2 (t k) (ht k)
    (H k) (hH k) hK (hbound k) (N k) (hR k) (hRnonneg k)
    (hEnvelope k) hA (htotal k)

end Problem367.MartingaleBracketIsometry

end

end OAI
