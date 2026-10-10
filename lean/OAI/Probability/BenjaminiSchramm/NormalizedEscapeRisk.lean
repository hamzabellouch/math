import OAI.Probability.BenjaminiSchramm.ExteriorEscape
import OAI.Probability.BenjaminiSchramm.CriticalHeightHit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedFullHit_upper (a : V → ℝ) (x : V) (t : ℝ) :
    IsUpperSet (G.adjustedFullHit a x t) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  refine ⟨y,hy,?_⟩
  rw [G.cluster_eq_percolationCluster] at hxy ⊢
  exact Percolation.conn_mono G.ends hωη hxy

lemma exteriorEscape_subset_adjustedFullHit
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (S : Set V) (x u : V) (t : ℝ)
    (ht : t ≤ -G.orbitAdjustedHeight a x u) :
    exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u ⊆ G.adjustedFullHit a u t := by
  rintro η ⟨y,_hy,hheight,_hyS,hconn⟩
  refine ⟨y,?_,?_⟩
  · rw [G.orbitAdjustedHeight_self] at hheight
    have hadd := G.orbitAdjustedHeight_change_base hc hl a x u y
    linarith
  · rw [G.cluster_eq_percolationCluster]
    exact Percolation.conn_mono G.ends Set.sdiff_subset hconn

theorem exteriorEscape_avoidance_profile [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (O : G.OrbitRepresentatives) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (r : E → unitInterval) (p : unitInterval) (hr : ∀ e, r e ≤ p)
    (R : ℝ) (n : ℕ) (S : Set V) (x u : V)
    (ht : R*n ≤ -G.orbitAdjustedHeight a x u) :
    1-G.rootHeightHitProfile O a R p n ≤
      (BernoulliProduct.law r).real (exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u)ᶜ := by
  let A := exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u
  have hA : MeasurableSet A := measurableSet_exteriorEscape G.ends _ _ x u
  have hh := BernoulliProduct.law_mono_pointwise r (fun _ => p) hr
    (G.adjustedFullHit a u (R*n)) (G.measurableSet_adjustedFullHit _ _ _)
      (G.adjustedFullHit_upper _ _ _)
  rw [BernoulliProduct.law_const] at hh
  have hμ : BernoulliProduct.law r A ≤ G.law p (G.adjustedFullHit a u (R*n)) :=
    (measure_mono (G.exteriorEscape_subset_adjustedFullHit hc hl a S x u (R*n) ht)).trans hh
  have hreal := (ENNReal.toReal_mono (measure_ne_top _ _) hμ).trans
    (G.adjustedFullHit_le_rootProfile O a ha R p n u)
  change (BernoulliProduct.law r).real A ≤ G.rootHeightHitProfile O a R p n at hreal
  rw [measureReal_compl hA,probReal_univ]
  linarith

end CriticalPercolation.BondGraph

end

end OAI
