import OAI.Dynamics.StandardMap.GraphFamilySmooth

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma continuousOn_contractive_fixedPoints {α E : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set α) (B : Set E) (T : α → E → E) (p : α → E)
    (hp : ∀ a ∈ s, p a ∈ B) (hfix : ∀ a ∈ s, T a (p a)=p a)
    (hcontract : ∀ a ∈ s, ∀ x ∈ B, ∀ y ∈ B,
      ‖T a x-T a y‖ ≤ (1/2)*‖x-y‖)
    (hcont : ∀ x ∈ B, ContinuousOn (fun a => T a x) s) : ContinuousOn p s := by
  intro a ha
  have hbound (b : α) (hb : b ∈ s) : ‖p b-p a‖ ≤ 2*‖T b (p a)-T a (p a)‖ := by
    have hh:=hcontract b hb (p b) (hp b hb) (p a) (hp a ha)
    rw [hfix b hb] at hh
    have ht:=dist_triangle (p b) (T b (p a)) (p a)
    simp only [dist_eq_norm] at ht
    rw [hfix a ha]
    nlinarith
  change Tendsto p (𝓝[s] a) (𝓝 (p a))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε/2 := by positivity
  have ht : ∀ᶠ b in 𝓝[s] a, dist (T b (p a)) (T a (p a)) < ε/2 :=
    (hcont (p a) (hp a ha) a ha).eventually (ball_mem_nhds _ hε')
  filter_upwards [self_mem_nhdsWithin,ht] with b hb hnear
  rw [dist_eq_norm]
  have hh:=hbound b hb
  rw [dist_eq_norm] at hnear
  linarith
end StandardMapEntropy

end OAI
