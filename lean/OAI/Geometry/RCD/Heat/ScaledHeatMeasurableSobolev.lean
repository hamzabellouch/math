import OAI.Geometry.RCD.Sobolev.RadialSobolevMeasurableLimit
import OAI.Geometry.RCD.Metric.FixedGaugeLocalBounds
import OAI.Geometry.RCD.Heat.FixedGaugeTimeContinuous

namespace OAI

/-! # Measurable Sobolev realization of the actual global heat limit

The input compactness data is supplied by `scaled_heat_global_compactness`.
The original subsequence and its one exceptional time set are retained.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_measurable_sobolev_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (N : Set ℝ) (hN : N.Countable)
    (Lg : ℝ≥0) (Mg : ℝ) (hMg : 0 ≤ Mg)
    (hgood : ∀ t ∈ Ioo δ 1, t ∉ N →
      LipschitzOnWith Lg (G t) (closedBall z (2*r)) ∧
      (∀ x ∈ closedBall z (2*r), |G t x| ≤ Mg) ∧
      TendstoUniformly (fun k (x : closedBall z (2*r)) =>
        hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
        (fun x => G t x) atTop) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let T := Ioo δ 1
    let σ := volume.comap (Subtype.val : T → ℝ)
    ∃ (u : ℕ → T → SobolevSpace μ Q) (v : T → SobolevSpace μ Q) (C : ℝ),
      0 ≤ C ∧ (∀ k, StronglyMeasurable (u k)) ∧ AEStronglyMeasurable v σ ∧
      (∀ k t, ‖u k t‖ ≤ C) ∧ (∀ t, ‖v t‖ ≤ C) ∧
      (∀ k t, SobolevSpace.toLp μ Q (u k t) =ᵐ[μ] fun x => radialCutoff z r x*
        hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x) ∧
      (∀ t : T, (t:ℝ) ∉ N → SobolevSpace.toLp μ Q (v t) =ᵐ[μ] fun x => radialCutoff z r x*G t x) ∧
      (∀ᵐ t ∂σ, Tendsto (fun k => SobolevSpace.toLp μ Q (u k t)) atTop
        (𝓝 (SobolevSpace.toLp μ Q (v t)))) := by
  intro μ Q T σ
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SeparableSpace (Lp ℝ 2 μ) := inferInstance
  have hgoodtime : ∀ᵐ t : T ∂σ, (t:ℝ) ∉ N := by
    apply ae_iff.mpr
    have hm : MeasurableSet {t : T | (t:ℝ) ∈ N} :=
      hN.measurableSet.preimage measurable_subtype_coe
    have hb : σ {t : T | (t:ℝ) ∈ N} ≤ volume N :=
      (Measure.comap_apply_le Subtype.val volume hm.nullMeasurableSet).trans
        (measure_mono (by rintro _ ⟨t,ht,rfl⟩; exact ht))
    simpa only [not_not] using le_antisymm (hb.trans_eq (hN.measure_zero volume)) (by positivity)
  obtain ⟨Ls,As,hseq⟩ := hX.fixed_gauge_local_bounds hn p hK
    ν ρ hρ hρ0 hB hν z hR hdist (r := 2*r) (by positivity) hδ
  let L : ℝ≥0 := Ls+Lg
  let Ag : ℝ≥0 := ⟨Mg,hMg⟩
  let A : ℝ≥0 := As+Ag
  let H := fun k (t : T) => hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k))
    (hε (ι k)) δ hδ z t
  have hHl (k : ℕ) (t : T) : LipschitzOnWith L (H k t) (closedBall z (2*r)) :=
    ((hseq (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) t
      ⟨t.property.1.le,t.property.2.le⟩).1).weaken
      (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ Lg from zero_le))
  have hHb (k : ℕ) (t : T) (x : X) (hx : x ∈ closedBall z (2*r)) : |H k t x| ≤ A :=
    ((hseq (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) t
      ⟨t.property.1.le,t.property.2.le⟩).2 x hx).trans
      (by change (As:ℝ) ≤ (As:ℝ)+Mg; exact le_add_of_nonneg_right hMg)
  have hHc (k : ℕ) (x : X) (_hx : x ∈ closedBall z (2*r)) : Continuous (fun t : T => H k t x) := by
    have hh := hX.fixedGaugeScaledPotential_continuous hn p ν ρ hρ hρ0 hB hν
      (F (ι k)) (hF (ι k)) (hε (ι k)) hδ z
    have hi : Continuous (fun t : T => ((t:ℝ),x)) :=
      continuous_subtype_val.prodMk continuous_const
    have hcomp := hh.comp hi
    dsimp only [Function.comp_def,Function.uncurry] at hcomp
    exact hcomp
  have hgl (t : T) (ht : (t:ℝ) ∉ N) : LipschitzOnWith L (G t) (closedBall z (2*r)) :=
    (hgood t t.property ht).1.weaken
      (le_add_of_nonneg_left (show (0:ℝ≥0) ≤ Ls from zero_le))
  have hgb (t : T) (ht : (t:ℝ) ∉ N) (x : X) (hx : x ∈ closedBall z (2*r)) : |G t x| ≤ A :=
    ((hgood t t.property ht).2.1 x hx).trans
      (by change Mg ≤ (As:ℝ)+Mg; exact le_add_of_nonneg_left As.coe_nonneg)
  have hc (t : T) (ht : (t:ℝ) ∉ N) (x : X) (hx : x ∈ closedBall z (2*r)) :
      Tendsto (fun k => H k t x) atTop (𝓝 (G t x)) :=
    ((hgood t t.property ht).2.2).tendsto_at ⟨x,hx⟩
  exact radial_sobolev_measurable_limit μ Q σ {t : T | (t:ℝ) ∉ N} hgoodtime z hr H
    (fun t => G t) L A hHl hHb hHc hgl hgb hc

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
