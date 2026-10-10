import OAI.Geometry.RCD.Heat.ScaledHeatMeasurableSobolev
import OAI.Geometry.RCD.Heat.ScaledHeatIteratedFromCompactness
import OAI.Geometry.RCD.Harmonic.SubtypeL2PairingLimit
import OAI.Geometry.RCD.Heat.ScaledHeatCutoffEnergyLimit
import OAI.Geometry.RCD.Sobolev.WeightedSobolevIntegralLower

namespace OAI

/-! # The weak Hamilton--Jacobi inequality for a prescribed heat limit

The Sobolev energy of the limiting function is bounded by twice its time
derivative in the distributional sense. The tests retain their exact
compact weak Laplacians, nonnegativity and common inner support.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_hamilton_jacobi_subsolution_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hG : Measurable (Function.uncurry G))
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => G t x) atTop) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (v : Ioo δ 1 → SobolevSpace μ Q) (C : ℝ),
        0 ≤ C ∧ AEStronglyMeasurable v (volume.comap Subtype.val) ∧
        (∀ t, ‖v t‖ ≤ C) ∧
        (∀ t : Ioo δ 1, (t:ℝ) ∉ N → SobolevSpace.toLp μ Q (v t) =ᵐ[μ]
          fun x => radialCutoff z r x*G t x) ∧
        ∀ (φ : SobolevSpace μ Q) (ξ : Lp ℝ 2 μ), IsWeakLaplacian μ Q φ ξ →
          (∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q φ x = 0) →
          (∀ᵐ x ∂μ, x ∉ closedBall z r → ξ x = 0) →
          ∀ Bφ : ℝ≥0, (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ Bφ) →
          (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q φ x) →
          ∀ θ θ' : ℝ → ℝ, ContinuousOn θ (Icc δ 1) → ContinuousOn θ' (Icc δ 1) →
            (∀ t ∈ Ioo δ 1, HasDerivAt θ (θ' t) t) → θ δ = 0 → θ 1 = 0 →
            (∀ t ∈ Ioo δ 1, 0 ≤ θ t) →
            (∫ t : Ioo δ 1, θ t*weightedGamma μ Q (SobolevSpace.toLp μ Q φ) (v t) (v t)
              ∂volume.comap Subtype.val) ≤
              -2*(∫ t in Ioo δ 1, θ' t*∫ x in closedBall z r,
                SobolevSpace.toLp μ Q φ x*G t x ∂μ) := by
  intro μ Q
  have hvalue := hX.scaled_heat_iterated_limit_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 z hR hdist G ι N hN hG hdata
  intro r hr δ hδ hδ1
  obtain ⟨Lg,Mg,hMg,hgood⟩ := hdata (2*r) (by positivity) δ hδ
  obtain ⟨u,v,C,hC,hu,hv,hbu,hbv,hurep,hvrep,hconv⟩ :=
    hX.scaled_heat_measurable_sobolev_of_compactness hn p hK ν ρ hρ hρ0 hB hν
      F hF ε hε hε1 z hR hdist hr hδ G ι N hN Lg Mg hMg hgood
  refine ⟨v,C,hC,hv,hbv,hvrep,?_⟩
  intro φ ξ hξ hφs hξs Bφ hBφ hφ0 θ θ' hθ hθ' hder hθδ hθ1 hθ0
  let Ω := closedBall z r
  let σx : Measure Ω := μ.comap Subtype.val
  let : IsFiniteMeasureOnCompacts σx := IsFiniteMeasureOnCompacts.comap' μ
    continuous_subtype_val (MeasurableEmbedding.subtype_coe measurableSet_closedBall)
  let : IsFiniteMeasure σx := inferInstance
  have hlocal := local_L2_pairing_limit_of_subtype_tests μ measurableSet_closedBall
    (isCompact_closedBall z r).measure_lt_top.ne
    (fun k t => hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t)
    G δ (hvalue r hr.le δ hδ σx)
  have he := hX.scaled_heat_cutoff_energy_limit hn p ν ρ hρ hρ0 hB hν F hF ε hε hε0
    G ι hι z hr hδ hδ1 u hurep hlocal φ ξ hξ hφs hξs Bφ hBφ θ θ'
    hθ hθ' hder hθδ hθ1
  have hθI : Integrable θ (volume.restrict (Ioo δ 1)) :=
    (hθ.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hθT : Integrable (fun t : Ioo δ 1 => θ t) (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hθI
  exact weighted_sobolev_integral_lower μ Q (volume.comap Subtype.val) u v
    (fun k => (hu k).aestronglyMeasurable) hv hC
    (fun k => Eventually.of_forall (hbu k)) (Eventually.of_forall hbv) hconv
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ Q φ))
    (hBφ.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx) hφ0
    (fun t => θ t) hθT (Eventually.of_forall fun t => hθ0 t t.property) he

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
