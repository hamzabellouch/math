import OAI.Geometry.RCD.Coordinates.RegularQuadraticTransportPaths
import OAI.Geometry.RCD.Transport.QuadraticMidpointSelection

namespace OAI

/-! # Simultaneous approximate midpoint identities near a regular point -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hX in
theorem regular_quadratic_midpoint_selection (hn : 2≤n) (hK : K≤0)
    {o : X} (ho : IsRegular n o) (z : ℕ → ℕ → X) (r : ℕ → ℕ → ℝ)
    (hz : ∀ i, Tendsto (z i) atTop (𝓝 o)) (hr : ∀ i k, 0<r i k)
    (hr0 : ∀ i, Tendsto (r i) atTop (𝓝 0))
    (π : ℕ → ℕ → Measure C(Time,X)) [∀ m k, IsProbabilityMeasure (π m k)]
    (hg : ∀ m k, ∀ᵐ γ ∂π m k, IsGeodesic γ)
    (hopt : ∀ m k, IsOptimalCoupling ((π m k).map (fun γ => γ 0)) ((π m k).map (fun γ => γ 1))
      ((π m k).map (fun γ => (γ 0,γ 1))))
    (B : ℕ → ℕ → ℝ≥0∞) (hB : ∀ m k, B m k≠∞)
    (hcomp : ∀ m k (t : Time), (π m k).map (fun γ => γ t)≤B m k • hausdorff n X)
    (hends : ∀ m i, i ≤ m → ∀ k,
      (∀ᵐ x ∂(π m k).map (fun γ => γ 0), dist x (z i k)≤r i k/512) ∧
      (∀ᵐ x ∂(π m k).map (fun γ => γ 1), dist x (z i k)≤r i k/512))
    (hcompression : ∀ m i, i ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      (B m k).toReal*(hausdorff n X).real (ball (z i k) (r i k))≤C)
    (P : ℕ → ℕ → C(Time,X) → Prop) (hP : ∀ m k, ∀ᵐ γ ∂π m k, P m k γ) :
    ∃ (d : ℕ → ℕ) (γ : ℕ → C(Time,X)), Tendsto d atTop atTop ∧
      (∀ k, P (d k) k (γ k) ∧ IsGeodesic (γ k)) ∧
      ∀ i, Tendsto (fun k => fullMidpointDefect (z i k) (γ k)/(r i k)^2) atTop (𝓝 0) := by
  let δ m := heatStep m/4
  have hδ m : 0<δ m ∧ δ m<1/2 := by
    have hm : heatStep m≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    constructor
    · exact div_pos (heatStep_pos m) (by norm_num)
    · dsimp only [δ]
      linarith
  have hδ0 : Tendsto δ atTop (𝓝 0) := by simpa only [zero_div] using heatStep_tendsto.div_const 4
  let a (m : ℕ) : Time := ⟨δ m,(hδ m).1.le,by linarith [(hδ m).2]⟩
  let b (m : ℕ) : Time := ⟨1-δ m,by linarith [(hδ m).2],by linarith [(hδ m).1]⟩
  have hs m i (him : i ≤ m) k : ∀ᵐ γ ∂π m k,
      dist (z i k) (γ 0)≤r i k ∧ dist (z i k) (γ 1)≤r i k := by
    have h0 := ae_of_ae_map (measurable_path_eval 0).aemeasurable (hends m i him k).1
    have h1 := ae_of_ae_map (measurable_path_eval 1).aemeasurable (hends m i him k).2
    filter_upwards [h0,h1] with γ hγ0 hγ1
    rw [dist_comm] at hγ0 hγ1
    exact ⟨hγ0.trans (by linarith [hr i k]),hγ1.trans (by linarith [hr i k])⟩
  have hl m i (him : i ≤ m) : Tendsto (fun k =>
      (∫ γ, |interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
        (a m) (b m) quadraticMidpointTime γ| ∂π m k)/(r i k)^2) atTop (𝓝 0) := by
    obtain ⟨C,hC,hbound⟩ := hcompression m i him
    exact hX.regular_quadratic_transport_paths hn hK ho (z i) (r i) (hz i) (hr i) (hr0 i)
      (π m) (hg m) (hopt m) (B m) (hB m) (hcomp m)
      (fun k => (hends m i him k).1) (fun k => (hends m i him k).2) hC hbound
      (a m) (b m) quadraticMidpointTime (hδ m).1
      (by change δ m<1-δ m; linarith [(hδ m).2])
      (by change 1-δ m<1; linarith [(hδ m).1])
      (by constructor
          · change δ m ≤ 1/2
            linarith [(hδ m).2]
          · change 1/2 ≤ 1-δ m
            linarith [(hδ m).2])
  exact quadratic_midpoint_selection π z r hr δ hδ hδ0 a b (fun _ => rfl) (fun _ => rfl) hg hs hl P hP

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
