import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.AssignedCharging

namespace OAI

/-! Spectral metric bridge. -/

section

namespace AlgorithmicThinTrees.MetricProfiles
noncomputable section
open Finset

variable {V E F : Type*} [Fintype V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def SquaredTriangle (p : V → E) : Prop :=
  ∀ u v w, ‖p u-p w‖^2 ≤ ‖p u-p v‖^2+‖p v-p w‖^2

@[instance_reducible] def squaredPseudoMetric (p : V → E) (ht : SquaredTriangle p) : PseudoMetricSpace V where
  dist u v := ‖p u-p v‖^2
  dist_self u := by simp
  dist_comm u v := by rw [norm_sub_rev]
  dist_triangle := ht

def spectralProfile (p : V → E) (ht : SquaredTriangle p) (v : V) : Doubled V → ℝ :=
  letI := squaredPseudoMetric p ht
  profile (plus v)

def spectralPolytope (p : V → E) (ht : SquaredTriangle p) : Set (Doubled V → ℝ) :=
  letI := squaredPseudoMetric p ht
  polytope

omit [InnerProductSpace ℝ E] in
lemma spectral_profile_length (p : V → E) (ht : SquaredTriangle p) (u v : V) :
    ‖spectralProfile p ht u-spectralProfile p ht v‖ = ‖p u-p v‖^2 := by
  let := squaredPseudoMetric p ht
  change ‖profile (plus u)-profile (plus v)‖ = _
  rw [profile_norm_sub,dist_plus]
  rfl

omit [InnerProductSpace ℝ E] in
lemma spectral_profile_mem (p : V → E) (ht : SquaredTriangle p) (u : V) :
    spectralProfile p ht u ∈ spectralPolytope p ht := by
  let := squaredPseudoMetric p ht
  exact profile_mem (plus u)

omit [InnerProductSpace ℝ E] in
lemma spectral_polytope_convex (p : V → E) (ht : SquaredTriangle p) :
    Convex ℝ (spectralPolytope p ht) := by
  let := squaredPseudoMetric p ht
  exact polytope_convex

lemma contraction_to_profile (p : V → E) (ht : SquaredTriangle p)
    (U : E →L[ℝ] F) (hU : ‖U‖ ≤ 1) (u v : V) :
    ‖U (p u)-U (p v)‖^2 ≤ ‖spectralProfile p ht u-spectralProfile p ht v‖ := by
  rw [spectral_profile_length,←map_sub]
  have h := U.le_opNorm (p u-p v)
  have hmul := mul_le_mul_of_nonneg_right hU (norm_nonneg (p u-p v))
  have hn : ‖U (p u-p v)‖ ≤ ‖p u-p v‖ := by linarith
  nlinarith [norm_nonneg (U (p u-p v)),norm_nonneg (p u-p v)]

omit [InnerProductSpace ℝ E] in
lemma squared_euclidean_compact_charge {n m : ℕ} (G : StrongThinTree.MultiGraph n m)
    {k : ℕ} (hk : G.EdgeConnected k) (p : Fin n → E) (ht : SquaredTriangle p) :
    letI := squaredPseudoMetric p ht
    ∀ (q : ℕ) (δ Δ : ℕ → ℝ)
      (bags : ∀ i, CompactGeometry.RadialShell.CompactFamily
        (fun v : Fin n => profile (plus v)) (δ i) (Δ i)),
      (∀ i, i+1 < q → Δ (i+1) ≤ δ i/12) →
      (k:ℝ)/4*(∑i ∈ range q, δ i*(∑D ∈ (bags i).bags, (D.card : ℝ))) ≤
        ∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2 := by
  let := squaredPseudoMetric p ht
  intro q δ Δ bags hnext
  exact CompactGeometry.doubled_compact_bound G hk id q δ Δ bags hnext

open AssignedGeometry AssignedGeometry.AssignedSequence

omit [InnerProductSpace ℝ E] in
lemma squared_euclidean_assigned_charge {n m : ℕ}
    (H : StrongThinTree.MultiGraph.Hierarchy n) (G : StrongThinTree.MultiGraph n m)
    (p : Fin n → E) (ht : SquaredTriangle p) {q : ℝ} (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) :
    letI := squaredPseudoMetric p ht
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1/1536 →
    ∀ (bags : List (AssignedFamily H G (fun v : Fin n => profile (plus v)) (6144/q))),
      GeometricAt ρ bags → Ratios ρ bags → Fresh ∅ bags →
      (q/8192)*mass bags ≤ ∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2 := by
  let := squaredPseudoMetric p ht
  intro ρ hρ hρsmall bags hgeo hR hfresh
  have h := assigned_bound (fun v : Fin n => ⟨plus v,rfl⟩) hq hconn hρ hρsmall
    bags hgeo hR hfresh
  have hd (u v : Fin n) : dist u v = ‖p u-p v‖^2 := rfl
  simpa only [CompactGeometry.normDistance,profile_norm_sub,dist_plus,hd] using h

end
end AlgorithmicThinTrees.MetricProfiles
end

end OAI
