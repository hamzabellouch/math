import OAI.Geometry.RCD.Heat.ScaledHeatIntervalEnergy
import OAI.Geometry.RCD.Sobolev.CompactCoreEnergyExtension
import OAI.Geometry.RCD.Sobolev.WeakLaplacianSupport

namespace OAI

/-! # The actual heat-limit energy inequality for all compact Lipschitz tests

No weak Laplacian is required of the spatial test. Positive heat-core
approximation and exact source locality extend the same interval bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_lipschitz_energy_of_compactness (hK : K ≤ 0)
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
    let H := goodTimeExtension N G
    let μ := hausdorff n X
    let Q := hX.quadratic
    ContinuousOn (Function.uncurry H) (Ioo 0 1 ×ˢ univ) ∧
      Measurable (Function.uncurry H) ∧
      (∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
        ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r)) ∧
      ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ (v : Ioo δ 1 → SobolevSpace μ Q) (C : ℝ),
          0 ≤ C ∧ AEStronglyMeasurable v (volume.comap Subtype.val) ∧
          (∀ t, ‖v t‖ ≤ C) ∧
          (∀ t : Ioo δ 1, (t:ℝ) ∉ N → SobolevSpace.toLp μ Q (v t) =ᵐ[μ]
            fun x => radialCutoff z r x*H t x) ∧
          ∀ (φ : X → ℝ) (L : ℝ≥0), LipschitzWith L φ → HasCompactSupport φ →
            tsupport φ ⊆ ball z r → (∀ x, 0 ≤ φ x) →
            ∀ s t : ℝ, δ < s → s < t → t < 1 →
              (∫ u in Icc s t, intervalExtension
                (fun τ => weightedGamma μ Q φ (v τ) (v τ)) u) ≤
                2*((∫ x in closedBall z r, φ x*H t x ∂μ) -
                  (∫ x in closedBall z r, φ x*H s x ∂μ)) := by
  intro H μ Q
  obtain ⟨hc,hm,hlocal,henergy⟩ := hX.scaled_heat_interval_energy_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  refine ⟨hc,hm,hlocal,?_⟩
  intro r hr δ hδ hδ1
  obtain ⟨v,C,hC,hv,hvb,hrep,hineq⟩ := henergy r hr δ hδ hδ1
  refine ⟨v,C,hC,hv,hvb,hrep,?_⟩
  intro φ L hφ hφc hφs hφ0 s t hs hst ht
  have htime : Icc s t ⊆ Ioo δ 1 := fun q hq => ⟨hs.trans_le hq.1,hq.2.trans_lt ht⟩
  have hcont (q : ℝ) (hq : q ∈ Ioo 0 1) : Continuous (H q) :=
    continuousOn_univ.mp (hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hq,mem_univ x⟩))
  obtain ⟨A,hA⟩ := hφc.exists_bound_of_continuous hφ.continuous
  let Bφ : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  have hBφ (x : X) : |φ x| ≤ Bφ :=
    (show |φ x| ≤ A by simpa only [Real.norm_eq_abs] using hA x).trans (le_max_left _ _)
  apply hX.compact_core_energy_extension hn z htime v hv hC hvb
    (H s) (H t) (hcont s ⟨hδ.trans hs,hst.trans ht⟩)
    (hcont t ⟨hδ.trans (hs.trans hst),ht⟩) ?_ φ hφ hφc hφs hφ0 hBφ
  intro ψ hψ Bψ hBψ hψ0
  obtain ⟨f,Lf,hf,hfc,hfs,hψf⟩ := hψ.1
  obtain ⟨ξ,hξ⟩ := hψ.2
  have hψs : ∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q ψ x = 0 := by
    filter_upwards [hψf] with x hx hout
    exact hx.trans (image_eq_zero_of_notMem_tsupport
      (fun hmem => hout (ball_subset_closedBall (hfs hmem))))
  have hξs := hξ.zero_off_closedBall μ Q z r hψs
  exact hineq ψ ξ hξ hψs hξs Bψ hBψ hψ0 s t hs hst ht

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
