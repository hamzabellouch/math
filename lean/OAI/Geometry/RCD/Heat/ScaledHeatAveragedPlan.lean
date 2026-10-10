import OAI.Geometry.RCD.Heat.ScaledHeatAveragedGradient
import OAI.Geometry.RCD.Sobolev.SobolevHamiltonJacobiEndpoints

namespace OAI

/-! # Transport comparison for the actual averaged small-noise heat limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_averaged_plan_comparison_of_compactness (hK : K ≤ 0)
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
    ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (π : Measure C(Time,X)) [IsFiniteMeasure π],
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      ∀ (C : ℝ≥0∞), C ≠ (∞ : ℝ≥0∞) →
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) →
      MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π →
      (∀ t : Time, ∀ᵐ γ ∂π, γ t ∈ closedBall z (r/4)) →
      ∀ h a b : ℝ, 0 < h → a < b → δ < a-h → b+h < 1 →
        (∫ γ : C(Time,X), timeIntervalAverage (fun q => H q (γ 0)) h a ∂π) -
          (∫ γ : C(Time,X), timeIntervalAverage (fun q => H q (γ 1)) h b ∂π) ≤
          (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/(2*(b-a)) := by
  intro H μ r hr δ hδ hδ1 π _ hgeo C hC hcomp hLength hs h a b hh hab ha hb
  let Q := hX.quadratic
  obtain ⟨_,_,_,hfamily⟩ := hX.scaled_heat_averaged_gradient_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  obtain ⟨v,_,_,_,_,_,hvc,hrep,hder⟩ := hfamily r hr δ hδ hδ1
  let u := timeIntervalAverage (intervalVectorExtension v) h
  have hall (t : ℝ) : ∃ D : Lp ℝ 2 μ, t ∈ Icc a b →
      HasDerivAt (fun s => SobolevSpace.toLp μ Q (u s)) D t ∧
      (∀ᵐ x ∂μ.restrict (closedBall z (r/4)),
        (SobolevSpace.minimalSlope μ Q (u t) x)^2 ≤ 2*D x) := by
    by_cases ht : t ∈ Icc a b
    · obtain ⟨D,hd,_,hg⟩ := hder h t hh (by linarith [ht.1]) (by linarith [ht.2])
      exact ⟨D,fun _ => ⟨hd,hg⟩⟩
    · exact ⟨0,fun ht' => False.elim (ht ht')⟩
  choose D hD using hall
  have hplan := sobolev_hamilton_jacobi_endpoint_comparison μ Q π hgeo hC hcomp hLength
    hab isClosed_closedBall.measurableSet hs u (hvc h).continuousOn D
    (fun t ht => (hD t ht).1) (fun t ht => (hD t ht).2)
  have he (t : ℝ) (ht : t ∈ Icc a b) (s : Time) :
      (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u t) (γ s) ∂π) =
        ∫ γ : C(Time,X), timeIntervalAverage (fun q => H q (γ s)) h t ∂π := by
    have hu := hrep h t hh (by linarith [ht.1]) (by linarith [ht.2])
    have hp := ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_eq hu)
    apply integral_congr_ae
    filter_upwards [hp,hs s] with γ hγ hsγ
    change SobolevSpace.toLp μ Q (u t) (γ s) = _ at hγ
    rw [hγ,radialCutoff_eq_one z hr,one_mul]
    exact mem_closedBall'.mp ((closedBall_subset_closedBall (by linarith : r/4 ≤ r)) hsγ)
  rw [he a ⟨le_rfl,hab.le⟩ 0,he b ⟨hab.le,le_rfl⟩ 1] at hplan
  exact hplan

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
