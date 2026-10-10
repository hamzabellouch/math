import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.CoordinateRotation
import OAI.Probability.CriticalPercolation.Clusters.PercolationTail
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseUniform
import OAI.Probability.CriticalPercolation.GraphGeometry.StripCritical

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stripPercolates_subset_some (v : V → ℝ) (w : ℝ) :
    G.stripPercolates v w⊆G.someStripPercolates v := by
  obtain ⟨n,hn⟩ := exists_nat_ge w
  rintro ω ⟨a,ha⟩
  apply Set.mem_iUnion.mpr
  exact ⟨n,a,ha.mono (G.cluster_mono (Set.inter_subset_inter_right _
    (G.inducedEdges_mono (fun _ hx => hx.trans hn))) a)⟩

theorem critical_null_of_unbounded_projection
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (hpc1 : G.criticalProbability<1)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |(pi (r.vertex n)).re|≤U ∧ |(pi (r.vertex n)).im|≤W) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hpc := G.criticalProbability_pos hc hl hq
  have hur : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |(pi x).re-(pi y).re|≤D :=
    fun {_ _} h => (Complex.abs_re_le_norm _).trans (hpi h)
  have hvi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |(pi x).im-(pi y).im|≤D :=
    fun {_ _} h => (Complex.abs_im_le_norm _).trans (hpi h)
  have hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => G.criticalProbability)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0 := by
    intro a b hab w
    let u := parallelCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b
    let v := normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b
    have huo : u o=0 := by simp [u,parallelCoordinate,hpo]
    have hvo : v o=0 := by simp [v,normalCoordinate,hpo]
    have hsteps := G.rotated_coordinate_increments (fun x => (pi x).re) (fun x => (pi x).im) a b D hab hD hur hvi
    have hdense' : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
        (∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y) ∧
        (∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) := by
      intro y
      obtain ⟨phi,hphi,hP⟩ := hdense y
      have hpr : ∀ x y, (pi (phi.vertex x)).re-(pi (phi.vertex y)).re=(pi x).re-(pi y).re :=
        fun x y => congrArg Complex.re (hP x y)
      have hpi' : ∀ x y, (pi (phi.vertex x)).im-(pi (phi.vertex y)).im=(pi x).im-(pi y).im :=
        fun x y => congrArg Complex.im (hP x y)
      exact ⟨phi,hphi,G.rotated_aut_differences _ _ a b phi hpr hpi'⟩
    have hn : ∀ᵐ ω ∂G.law G.criticalProbability,
        ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W := by
      filter_upwards [hnoray] with ω hω
      exact G.rotated_no_bounded_ray _ _ a b hab ω hω
    have hs := G.critical_strip_null hc hl hq hg hpc1 u v o c (2*D) (by positivity) huo hvo hsteps.1 hsteps.2
      (integer_coordinates_direction_unbounded pi honto a b hab) hdense' hn
    have hm := measure_mono (μ := G.law G.criticalProbability) (G.stripPercolates_subset_some v w)
    rw [hs] at hm
    simpa only [law,BernoulliProduct.law_const] using le_antisymm hm (bot_le)
  by_contra hne
  have hpos := pos_iff_ne_zero.mpr hne
  have hone : BernoulliProduct.law (fun _ : E => G.criticalProbability) G.percolates=1 := by
    simpa only [law,BernoulliProduct.law_const] using G.percolates_probability_one G.criticalProbability hpos
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite := by
    intro U W
    have hh := hnoray.mono (fun ω hω => G.no_bounded_ray_rectangles hl (fun x => (pi x).re) (fun x => (pi x).im) ω hω U W)
    simpa only [law,BernoulliProduct.law_const] using hh
  exact G.ellipse_critical_contradiction hc hl hq pi o c D hD hpc hpc1 hpo hpi hdense hone hbox hnull

end CriticalPercolation.BondGraph
end
end
end

end OAI
