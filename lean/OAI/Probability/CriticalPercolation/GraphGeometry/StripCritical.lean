import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.Criticality.OpenRay
import OAI.Probability.CriticalPercolation.Criticality.DirectionalTail
import OAI.Probability.CriticalPercolation.Criticality.PositiveCritical
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.GraphGeometry.StripUniform

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma OpenRay.reachable (ω : Set E) (r : G.OpenRay ω) (n : ℕ) :
    (G.openGraph ω).Reachable (r.vertex 0) (r.vertex n) := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (r.adjacent n).reachable

lemma OpenRay.infinite_cluster (ω : Set E) (r : G.OpenRay ω) :
    (G.cluster ω (r.vertex 0)).Infinite := by
  apply (Set.infinite_range_of_injective r.injective).mono
  rintro x ⟨n,rfl⟩
  exact r.reachable G ω n

lemma stripPercolates_iff_ray (hl : G.LocallyFinite) (v : V → ℝ) (W : ℝ) (ω : Set E) :
    ω∈G.stripPercolates v W ↔ ∃ r : G.OpenRay ω, ∀ n, |v (r.vertex n)|≤W := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨r,_hr,hS⟩ := G.infinite_induced_openRay hl ω {x | |v x|≤W} a ha
    exact ⟨r,hS⟩
  · rintro ⟨r,hr⟩
    let r' : G.OpenRay (ω∩G.inducedEdges {x | |v x|≤W}) := {
      vertex := r.vertex, injective := r.injective,
      adjacent := fun n => (G.open_induced_adj _ ω _ _).mpr ⟨r.adjacent n,hr n,hr (n+1)⟩ }
    exact ⟨r.vertex 0,r'.infinite_cluster G _⟩

theorem critical_strip_null (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (hpc1 : G.criticalProbability<1)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hvunbounded : ∀ n : ℕ, ∃ x, (n : ℝ)<v x)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    G.law G.criticalProbability (G.someStripPercolates v)=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hne
  have hstrip : 0<(BernoulliProduct.law (fun _ : E => G.criticalProbability))
      (G.someStripPercolates v) := by
    simpa only [law,BernoulliProduct.law_const] using (pos_iff_ne_zero.mpr hne)
  have hsub : G.someStripPercolates v⊆G.percolates := by
    intro ω hω
    obtain ⟨n,a,ha⟩ := Set.mem_iUnion.mp hω
    exact ⟨a,ha.mono (G.cluster_mono Set.inter_subset_left a)⟩
  have hpositive : 0<G.law G.criticalProbability G.percolates :=
    (pos_iff_ne_zero.mpr hne).trans_le (measure_mono hsub)
  have hpc := G.criticalProbability_pos hc hl hq
  have hdir := G.unique_cluster_direction_unbounded_ae hc hl hq hg G.criticalProbability
    ⟨hpc,hpc1⟩ hpositive v hvunbounded
  have hdir' : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x := by
    simpa only [law,BernoulliProduct.law_const] using hdir
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
    intro U W
    have h := hnoray.mono (fun ω hω => G.no_bounded_ray_rectangles hl u v ω hω U W)
    simpa only [law,BernoulliProduct.law_const] using h
  exact G.strip_critical_contradiction hc hl hq u v o c D hD hpc hpc1 huo hvo hu hv hdense
    hstrip hdir' hbox

end CriticalPercolation.BondGraph
end
end
end

end OAI
