import OAI.Probability.FreeIsing.Estimates.ContinuousCoefficientModulus
import OAI.Probability.FreeIsing.Martingales.BracketIsometry

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem367.MartingaleCoefficientApproximation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_integral_sq_coefficient_error [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M A H : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {S : Set I} (hS : IsCompact S)
    (hcH : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) S)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (s t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    (hst : ∀ n i, s n i ≤ t n i)
    (hs : ∀ n i, i < N n → s n i ∈ S)
    (htmem : ∀ n i, i < N n → t n i ∈ S)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (s n i) (t n i) ≤ δ n)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun u => A u ω))
    {C : ℝ} (htotal : ∀ n, ∀ᵐ ω ∂μ, A (t n (N n)) ω - A (t n 0) ω ≤ C) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ Finset.range (N n),
      (H (s n i) ω - H (t n i) ω) *
        (M (t n (i + 1)) ω - M (t n i) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  let E : ℕ → ℕ → Ω → ℝ := fun n i ω => H (s n i) ω - H (t n i) ω
  let R : ℕ → Ω → ℝ := fun n ω => ContinuousCoefficientModulus.pairModulus
    (fun i => H (s n i) ω) (fun i => H (t n i) ω) (N n)
  have hm (u : I) : StronglyMeasurable (H u) := (hH u).mono (F.le u)
  have hE (n i : ℕ) : StronglyMeasurable[F (t n i)] (E n i) :=
    ((hH (s n i)).mono (F.mono (hst n i))).sub (hH (t n i))
  have hbE (n i : ℕ) : ∀ᵐ ω ∂μ, |E n i ω| ≤ 2 * K := by
    filter_upwards [hbound (s n i), hbound (t n i)] with ω hsω htω
    exact (abs_sub _ _).trans (by linarith)
  have hR2 (n : ℕ) : MemLp (R n) 2 μ :=
    ContinuousCoefficientModulus.memLp_pairModulus
      (fun i => H (s n i)) (fun i => H (t n i))
      (fun i => hm (s n i)) (fun i => hm (t n i)) (N n)
      (show 0 ≤ 2 * K by positivity) (fun i _ => hbE n i) 2
  have henv (n : ℕ) : ∀ᵐ ω ∂μ, ∀ i < N n, E n i ω ^ 2 ≤ R n ω ^ 2 := by
    apply Filter.Eventually.of_forall
    intro ω i hi
    have hb := ContinuousCoefficientModulus.abs_sub_le_pairModulus
      (fun j => H (s n j) ω) (fun j => H (t n j) ω) hi
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (ContinuousCoefficientModulus.pairModulus_nonneg _ _ _)).2 hb
  have hlim : Tendsto (fun n => ∫ ω, R n ω ^ 2 ∂μ) atTop (𝓝 0) :=
    ContinuousCoefficientModulus.tendsto_integral_pairModulus_pow hS hm hcH hK
      (fun u _ => hbound u) s t N hs htmem δ hδ hdist 2 (by norm_num)
  exact MartingaleBracketIsometry.tendsto_integral_sq_grid_transform hM hQ hM2 t ht E hE
    (show 0 ≤ 2 * K by positivity) hbE N (fun n => (hR2 n).integrable_sq)
    (fun _ => Filter.Eventually.of_forall (fun ω => sq_nonneg _)) henv hA htotal hlim

end Problem367.MartingaleCoefficientApproximation

end

end OAI
