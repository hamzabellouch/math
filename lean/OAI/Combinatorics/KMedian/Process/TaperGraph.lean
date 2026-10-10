import Mathlib
import OAI.Combinatorics.KMedian.Process.TaperData
import OAI.Combinatorics.KMedian.Process.SourceDriftLaw

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

structure GraphData (Δ : ℕ) (g P : ℝ) (location : I → X) (own : I → Finset I) where
  radius : I → ℝ
  marginal : I → I → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  marginal_nonneg : ∀ h i, 0 ≤ marginal h i
  marginal_le_one : ∀ h i, marginal h i ≤ 1
  incoming_mass : ∀ i, ∑ h, g*marginal h i=1
  incoming_count : ∀ i, ∑ h, marginal h i=Δ
  own_certain : ∀ i h, h ∈ own i → marginal h i=1
  lower : ∀ h i, marginal h i < 1 →
    radius i*(1-P*marginal h i) ≤ dist (location i) (location h)
  upper : ∀ h i, 0 < marginal h i →
    dist (location i) (location h) ≤ radius i*(1-P*marginal h i)
  minimal : ∀ i R, 0 < R →
    1 ≤ mass g P (fun h => dist (location i) (location h)) (1/R) → radius i ≤ R

def GraphData.Good {Δ : ℕ} {g P : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (G : I → Finset I) : Prop :=
  (∀ i, (G i).card=Δ) ∧ (∀ i, own i ⊆ G i) ∧
    (∀ h i, h ∈ G i → 0 < D.marginal h i)

theorem exists_graph (Δ : ℕ) {g P : ℝ} (location : I → X) (own : I → Finset I)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hP : 0 < P) (hP1 : P ≤ 1/2)
    (htotal : 1 ≤ ∑ _i : I, g)
    (hown : ∀ i h, h ∈ own i → dist (location i) (location h)=0)
    (howncard : ∀ i, (own i).card ≤ Δ) :
    ∃ D : GraphData Δ g P location own, ∃ μ : FiniteLaw (I → Finset I),
      (∀ G, 0 < μ.weight G → D.Good G) ∧
      (∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=
        D.marginal h i*D.marginal k j) := by
  choose N q hN hq0 hq1 hmass hcount hcertain hlower hupper hmin using fun i =>
    exists_data Δ (fun h => dist (location i) (location h)) (own i)
      hg hunit hP hP1 (fun _ => dist_nonneg) htotal (hown i) (howncard i)
  let D : GraphData Δ g P location own :=
    ⟨N, fun h i => q i h, hN, fun h i => hq0 i h, fun h i => hq1 i h,
      hmass, hcount, hcertain, fun h i => hlower i h, fun h i => hupper i h, hmin⟩
  obtain ⟨μ,hcard,hfirst,hpair,hone,hzero⟩ := GraphLaw.exists_law D.marginal Δ
    D.marginal_nonneg D.marginal_le_one D.incoming_count
  refine ⟨D,μ,?_,hfirst,hpair⟩
  intro G hG
  refine ⟨hcard G hG,fun i h hh => hone G hG h i (D.own_certain i h hh),?_⟩
  intro h i hedge
  apply lt_of_le_of_ne (D.marginal_nonneg h i)
  intro hz
  exact hzero G hG h i hz.symm hedge

theorem GraphData.drift {Δ : ℕ} {g P x ζ b : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (μ : FiniteLaw (I → Finset I))
    (client : X) (S : Finset I)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (hP : 0 ≤ P) (hP1 : P ≤ 1/2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : PhysicalPotential.mass g S ≤ 1)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |P-Analytic.P x| ≤ ζ)
    (hfirst : ∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=D.marginal h i)
    (hpair : ∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=
      D.marginal h i*D.marginal k j) :
    Analytic.timeRate x (PhysicalPotential.mass g S)*
        PhysicalPotential.cost g (fun i => dist client (location i)) S+
      μ.expect (fun G => g*∑ h ∈ FixedBatch.relevant (FixedBatch.graphActions G) S,
        FixedBatch.charge (FixedBatch.graphActions G) x g b
          (fun i => dist client (location i)) S h) ≤
      Analytic.B x*g*PhysicalPotential.cost g (fun i => dist client (location i)) S+
        12*ζ*PhysicalPotential.cost g (fun i => dist client (location i)) S := by
  apply FixedBatch.source_drift_of_law μ Δ S (fun i => dist client (location i))
    D.radius D.marginal hg hunit hx0 hx1 hy (fun _ => dist_nonneg) D.radius_nonneg
    D.marginal_nonneg D.marginal_le_one D.incoming_count hP hP1 hζ0 hζ1 he
    _ _ hfirst hpair
  · intro i _ t _ hq
    apply (D.lower t i hq).trans
    simpa only [dist_comm (location i) client] using
      (dist_triangle (location i) client (location t))
  · intro h i hq
    have ht := dist_triangle client (location i) (location h)
    have hu := D.upper h i hq
    have hm := min_le_right b (dist client (location h))
    nlinarith only [ht,hu,hm]

end MetricKMedian.Taper
end
end

end OAI
