import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.EuclideanEllipse
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseSeed
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseExit
import OAI.Probability.CriticalPercolation.Gluing.CorridorGraph

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma normalized_edge_bound (pi : V → ℂ) (R W D : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D) :
    ∀ ⦃x y⦄, G.fullGraph.Adj x y →
      ‖EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y)‖≤D/W := by
  intro x y hxy
  rw [←EuclideanEllipse.normalize_sub]
  exact (EuclideanEllipse.normalize_norm_le R W hW hWR c _).trans
    (div_le_div_of_nonneg_right (hpi hxy) hW.le)

lemma normalized_clusters_finite (pi : V → ℂ) (R W : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (mu : Measure (Set E))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) a).Finite) :
    ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) a).Finite := by
  have hR : 0<R := hW.trans_le hWR
  have hsub : {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}⊆
      {x | |(pi x).re|≤R ∧ |(pi x).im|≤R} := by
    intro x hx
    change ‖EuclideanEllipse.normalize R W c (pi x)‖≤1 at hx
    have hn : ‖pi x‖≤R := by
      calc
        _ = ‖EuclideanEllipse.expand R W c (EuclideanEllipse.normalize R W c (pi x))‖ := by
          rw [EuclideanEllipse.expand_normalize R W hR.ne' hW.ne']
        _ ≤ R*‖EuclideanEllipse.normalize R W c (pi x)‖ := EuclideanEllipse.expand_norm_le R W hW.le hWR c _
        _ ≤ R := by nlinarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩
  filter_upwards [hbox R R] with ω hω a
  exact (hω a).subset (G.cluster_mono (Set.inter_subset_inter_right _ (G.inducedEdges_mono hsub)) a)

theorem all_ellipses_favored [Countable E]
    (pi : V → ℂ) (A : Set V) (W B D zeta : ℝ) (hD : 0≤D) (hW : 0<W)
    (hBW : B<W) (hDz : D/W≤zeta)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hA : ∀ a∈A, ‖pi a‖≤B) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite) :
    ∀ R : ℝ, W≤R → ∀ c : Circle, ∃ d∈S,
      1-a<(BernoulliProduct.law q).real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) := by
  intro R hWR c
  have hseed : ∀ x∈A, ‖EuclideanEllipse.normalize R W c (pi x)‖<1 := by
    intro x hx
    exact (EuclideanEllipse.normalize_norm_le R W hW hWR c (pi x)).trans_lt
      ((div_lt_one hW).mpr ((hA x hx).trans_lt hBW))
  have hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) x).Finite := by
    filter_upwards [G.normalized_clusters_finite pi R W hW hWR c (BernoulliProduct.law q) hbox] with ω hω x _hx
    exact hω x
  exact G.exists_favored_ellipse _ A zeta (D/W) (by positivity) hDz
    (G.normalized_edge_bound pi R W D hW hWR c hpi) hseed S hcover q a ha hi hbound

end CriticalPercolation.BondGraph
end
end
end

end OAI
