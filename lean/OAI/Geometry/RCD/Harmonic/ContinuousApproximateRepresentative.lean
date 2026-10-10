import OAI.Geometry.RCD.Harmonic.PointedRadialDistance
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Sequences

namespace OAI

/-! # From almost everywhere to every point against an approximate map -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem continuous_approximate_representative {X Y : Type*}
    [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] (μ : Measure X) [μ.IsOpenPosMeasure]
    {Ω : Set X} (hΩ : IsOpen Ω) (u F : X → Y) (hu : ContinuousOn u Ω)
    {L ε δ : ℝ}
    (hF : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (F x) (F y) ≤ L*dist x y+ε)
    (hAE : ∀ᵐ x ∂μ.restrict Ω, dist (u x) (F x) ≤ δ) :
    ∀ x ∈ Ω, dist (u x) (F x) ≤ δ+ε := by
  intro x hx
  let A := {y | y ∈ Ω ∧ dist (u y) (F y) ≤ δ}
  have hdense := Measure.dense_of_ae (μ := μ) (ae_imp_of_ae_restrict hAE)
  have hxcl : x ∈ closure A := by
    apply Metric.mem_closure_iff.mpr
    intro η hη
    obtain ⟨y,hy,hgood⟩ := hdense.exists_mem_open (isOpen_ball.inter hΩ)
      ⟨x,mem_ball_self hη,hx⟩
    exact ⟨y,⟨hgood.2,hy hgood.2⟩,by simpa only [mem_ball,dist_comm] using hgood.1⟩
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hxcl
  have hut : Tendsto (fun k => u (y k)) atTop (𝓝 (u x)) :=
    (hu.continuousAt (hΩ.mem_nhds hx)).tendsto.comp hyt
  have hdist : Tendsto (fun k => dist (u x) (u (y k))+δ+(L*dist (y k) x+ε))
      atTop (𝓝 (δ+ε)) := by
    have h1 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x))).dist hut
    have h2 := hyt.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    simpa only [dist_self,mul_zero,zero_add] using (h1.add_const δ).add ((h2.const_mul L).add_const ε)
  apply ge_of_tendsto hdist
  exact Eventually.of_forall fun k => calc
    dist (u x) (F x) ≤ dist (u x) (u (y k))+dist (u (y k)) (F x) := dist_triangle _ _ _
    _ ≤ dist (u x) (u (y k))+(dist (u (y k)) (F (y k))+dist (F (y k)) (F x)) := by
      linarith [dist_triangle (u (y k)) (F (y k)) (F x)]
    _ ≤ dist (u x) (u (y k))+δ+(L*dist (y k) x+ε) := by
      have h1 := (hy k).2
      have h2 := hF (y k) (hy k).1 x hx
      linarith

end RegularPointCoordinates

end

end OAI
