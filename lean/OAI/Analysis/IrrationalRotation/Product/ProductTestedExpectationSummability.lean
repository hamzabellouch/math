import OAI.Analysis.IrrationalRotation.Product.ProductTestedKernelMoments
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingAsymptotics

namespace OAI

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.ProductSamplingPhaseMoments

def testedExpectedError {κ : Type*} [Fintype κ] (m : ℕ)
    (N₀ : κ → ℝ) (powers : Finset ℕ) (selected : κ → Bool)
    (endpoint : Bool) (a b c d : κ → ℝ) : ℝ :=
  let u := fun i => testedKernel m (selected i) endpoint (a i) (b i) (c i) (d i)
  ∫ θ, ∫ x, ((powers.card : ℝ)⁻¹ *
      (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * θ i))) -
      ∏ i, mean (u i) (x i))^2
    ∂Measure.pi (fun _ : κ => unitInterval)
    ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))

theorem testedExpectedError_nonneg {κ : Type*} [Fintype κ] (m : ℕ)
    (N₀ : κ → ℝ) (powers : Finset ℕ) (selected : κ → Bool)
    (endpoint : Bool) (a b c d : κ → ℝ) :
    0 ≤ testedExpectedError m N₀ powers selected endpoint a b c d := by
  apply integral_nonneg
  intro θ
  apply integral_nonneg
  intro x
  exact sq_nonneg _

theorem testedExpectedError_le_majorant {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (selected : κ → Bool) (endpoint : Bool) (a b c d : κ → ℝ)
    (hd : (Fintype.card κ : ℝ) ≤ (101 / 100 : ℝ) * p.m j)
    (hlog : 8 * Real.log (p.m j) ≤ (p.m j : ℝ)^(1 / 25 : ℝ)) :
    testedExpectedError (p.m j) N₀ powers selected endpoint a b c d ≤
      ((303 / 100 : ℝ) * 8 * Real.exp ((101 / 50 : ℝ) * 8)) *
        (p.m j : ℝ)^(-39 : ℝ) + (p.m j : ℝ)^(-(p.m j : ℝ) / 25) := by
  have hm1 : (1 : ℝ) ≤ p.m j := by exact_mod_cast (show 1 ≤ p.m j by omega)
  have hm0 : (0 : ℝ) ≤ p.m j := Nat.cast_nonneg _
  have hbase : 1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) + (p.m j : ℝ)^(-50 : ℝ) ≤
      1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) + 8 * (p.m j : ℝ)^(-50 : ℝ) := by
    nlinarith [Real.rpow_nonneg hm0 (-6 / 5 : ℝ), Real.rpow_nonneg hm0 (-50 : ℝ)]
  have hsmall : (p.m j : ℝ)^(-50 : ℝ) ≤ 8 * (p.m j : ℝ)^(-50 : ℝ) := by
    nlinarith [Real.rpow_nonneg hm0 (-50 : ℝ)]
  have hoff := ProductSampling.exact_moment_error_le (d := Fintype.card κ)
    hm1 (show (0 : ℝ) ≤ 8 by norm_num) hd
  have hdiag := ProductSampling.diagonal_sampling_ratio_le hm1
    (show (0 : ℝ) ≤ 8 by norm_num) hlog hd hs.cardinality
  have hraw := tested_expected_average_error_le hp hm N₀ hN hNle powers hs
    selected endpoint a b c d
  apply hraw.trans
  calc
    _ ≤ (p.m j : ℝ)^(-(p.m j : ℝ) / 25) +
        3 * ((Fintype.card κ : ℝ) * (8 * (p.m j : ℝ)^(-50 : ℝ)) *
          (1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            8 * (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
      apply add_le_add hdiag
      gcongr
    _ ≤ _ := by
      simpa only [add_comm] using
        (add_le_add_left hoff ((p.m j : ℝ)^(-(p.m j : ℝ) / 25)))

theorem testedExpectedError_summable {p : ProductScaleData}
    (hp : ProductScaleLaws p) (powers : ℕ → Finset ℕ)
    (hs : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (powers j))
    (N₀ : (j : ℕ) → Fin (p.prefixCount (j + 1)) → ℝ)
    (hN : ∀ j i, 0 < N₀ j i) (hNle : ∀ j i, N₀ j i ≤ p.N j)
    (selected : (j : ℕ) → Fin (p.prefixCount (j + 1)) → Bool)
    (endpoint : Bool)
    (a b c d : (j : ℕ) → Fin (p.prefixCount (j + 1)) → ℝ) :
    Summable (fun j => testedExpectedError (p.m j) (N₀ j) (powers j)
      (selected j) endpoint (a j) (b j) (c j) (d j)) := by
  have hgrowth : ∀ j, (2 : ℝ)^j ≤ (p.m j : ℝ) := by
    intro j
    exact_mod_cast hp.m_ge_pow_self j
  have hmTop : Tendsto (fun j => (p.m j : ℝ)) atTop atTop :=
    tendsto_atTop_mono hgrowth (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlogs := hmTop.eventually (ProductSampling.eventually_const_log_le_rpow 8
    (by norm_num : (0 : ℝ) < 1 / 25))
  apply (ProductSampling.sampling_error_majorant_summable hgrowth
    ((303 / 100 : ℝ) * 8 * Real.exp ((101 / 50 : ℝ) * 8))).of_norm_bounded_eventually_nat
  filter_upwards [hs, hlogs, hmTop.eventually_ge_atTop 200] with j hsj hlog hm
  rw [Real.norm_of_nonneg (testedExpectedError_nonneg _ _ _ _ _ _ _ _ _)]
  apply testedExpectedError_le_majorant hp (by exact_mod_cast hm)
    (N₀ j) (hN j) (hNle j) (powers j) hsj (selected j) endpoint (a j) (b j) (c j) (d j)
  · simpa only [Fintype.card_fin] using hp.prefix_count_succ_le j
  · exact hlog

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
