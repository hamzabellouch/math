import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingPhaseMoments
import OAI.Analysis.IrrationalRotation.Sampling.ProductScaleSampling

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments

theorem samplingPair_of_product_powers {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} {powers : Finset ℕ} (hs : ProductSamplingPowersAt p j powers)
    {N₀ : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ p.N j)
    {n n' : ℕ} (hn : n ∈ powers) (hn' : n' ∈ powers) (hne : n ≠ n') :
    ScalarSampling.SamplingPair (p.m j) N₀ (p.N j) n n' := by
  refine ⟨hN₀, hN, ?_, hs.positive n hn, hs.positive n' hn', hne,
    hs.range n hn, hs.range n' hn', ?_⟩
  · have hK : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
    dsimp [ProductScaleData.N]
    nlinarith [Nat.cast_nonneg (α := ℝ) (p.m j)]
  · intro v v' hv hv' hnonzero
    have h := hs.separation n hn n' hn' hne v v' hv hv' hnonzero
    have hr : ((p.m j * p.K j * p.m j ^ 1000 : ℕ) : ℝ) <
        |(v : ℝ) * n + (v' : ℝ) * n'| := by exact_mod_cast h
    simpa only [ProductScaleData.N, Nat.cast_mul, Nat.cast_pow] using hr

theorem coordinate_scale_le_power {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} (hm : 200 ≤ p.m j) {powers : Finset ℕ}
    (hs : ProductSamplingPowersAt p j powers) {N₀ : ℝ} (hN : N₀ ≤ p.N j)
    {n : ℕ} (hn : n ∈ powers) : N₀ ≤ (n : ℝ) := by
  have hK : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
  have hNm : p.N j ≤ (p.m j : ℝ)^2 := by
    dsimp [ProductScaleData.N]
    nlinarith [Nat.cast_nonneg (α := ℝ) (p.m j)]
  have hh := ScalarRectangles.horizon_ge_twice_square (m := (p.m j : ℝ)) (by exact_mod_cast hm)
  have hr := (hs.range n hn).1
  linarith

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
