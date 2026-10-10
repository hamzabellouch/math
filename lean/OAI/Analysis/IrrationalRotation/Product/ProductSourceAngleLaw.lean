import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingScaleTrimming

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal

namespace Invariant233.ProductScaleLaws
open ProductPhases InvariantProjection.IndependentAngles

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem source_coordinate_reciprocal (S : ℕ → ℝ)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    Summable (fun i => 1 / S i) ∧
      (∑' i, 1 / S i) = ∑' j, 1 / (p.K j : ℝ) := by
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv p.m hp.m_pos
  have hS (i : ℕ) : S i = (p.m (e i).1 : ℝ) * p.K (e i).1 :=
    hblock _ _ (mem_consecutiveBlock_enumeration p.m e he i)
  simpa only [hS] using enumerated_block_reciprocal p.m hp.m_pos
    (fun j => (p.K j : ℝ)) hp.real_K_pos hp.summable_reciprocal e

theorem ae_source_angles (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      (∀ j, ∀ i ∈ consecutiveBlock p.m j,
        θ i ∈ Icc (1 / p.N j) (2 / p.N j)) ∧
      (∀ i, 0 < θ i ∧ θ i < 1) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 1 / 25 ∧ ProductModel.JointlyRationallyIndependent θ := by
  have hrec := hp.source_coordinate_reciprocal S hblock
  filter_upwards [prescribedIntervals_ae_summable_independent S hS hrec.1] with θ hθ
  have hb (j i : ℕ) (hi : i ∈ consecutiveBlock p.m j) :
      θ i ∈ Icc (1 / p.N j) (2 / p.N j) := by
    simpa only [hblock j i hi, ProductScaleData.N] using hθ.1 i
  have hpos (i : ℕ) : 0 < θ i :=
    (one_div_pos.mpr (hS i)).trans_le (hθ.1 i).1
  have hsum : (∑' i, θ i) ≤ 1 / 25 := by
    have ht := hθ.2.2.1
    rw [hrec.2] at ht
    have hk := hp.reciprocal_sum_le
    linarith
  refine ⟨hb, ?_, hθ.2.1, hsum, hθ.2.2.2⟩
  intro i
  refine ⟨hpos i, ?_⟩
  have hi : θ i ≤ ∑' k, θ k :=
    hθ.2.1.le_tsum i (fun k _ => (hpos k).le)
  linarith

theorem ae_source_horizon_angle_tail_le (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ l t : ℕ, (t : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l) →
        ENNReal.ofReal (t : ℝ) *
          (∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
            ENNReal.ofReal (θ i)) ≤
          ENNReal.ofReal (4 * (p.m l : ℝ) ^ (-(p.m l : ℝ) / 20)) := by
  filter_upwards [hp.ae_source_angles S hS hblock] with θ hθ
  intro l t ht
  exact ProductModel.TailTrimming.source_horizon_angle_tail_le hp θ
    (fun i => (hθ.2.1 i).1.le) hθ.2.2.1
    (fun j i hi => (hθ.1 j i hi).2) l t ht

theorem ae_source_horizon_angle_tail_tendsto_zero
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ M : ℕ → ℕ,
        (∀ l, (M l : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)) →
        Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
          ∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
            ENNReal.ofReal (θ i)) atTop (𝓝 0) := by
  filter_upwards [hp.ae_source_angles S hS hblock] with θ hθ
  intro M hM
  exact ProductModel.TailTrimming.source_horizon_angle_tail_tendsto_zero hp θ
    (fun i => (hθ.2.1 i).1.le) hθ.2.2.1
    (fun j i hi => (hθ.1 j i hi).2) M hM

end Invariant233.ProductScaleLaws

end

end OAI
