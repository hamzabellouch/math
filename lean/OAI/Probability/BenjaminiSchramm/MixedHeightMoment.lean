import OAI.Probability.BenjaminiSchramm.MixedRootPathComparison
import OAI.Probability.BenjaminiSchramm.PeakHalfspaceTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma connectionAvoidingHit_mono (D D' J J' : Set E) (T T' : Set V)
    (hD : D' ⊆ D) (hJ : J ⊆ J') (hT : T' ⊆ T) (x y : V) :
    connectionAvoidingHit G D J x y T ⊆ connectionAvoidingHit G D' J' x y T' := by
  rintro ω ⟨hxy,havoid⟩
  refine ⟨conn_mono G (Set.inter_subset_inter_right _ hJ) hxy,?_⟩
  rintro ⟨z,hz,hxz⟩
  exact havoid ⟨z,hT hz,conn_mono G (Set.inter_subset_inter_right _ hD) hxz⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def mixedHeightLayerMoment (a : V → ℝ) (p : unitInterval)
    (d c l u ad t : ℝ) (x : V) : ℝ≥0∞ :=
  ∑' y, if l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u then
    G.law p (connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      x y {z | t ≤ G.orbitAdjustedHeight a x z}) else 0

omit [Countable V] [Countable E] in
lemma mixedHeight_connection_event_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d c ad t : ℝ) (φ : G.Aut) (ω : Set E) (x y : V) :
    φ.edge '' ω ∈ connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a (φ.vertex x) z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
        G.orbitAdjustedHeight a (φ.vertex x) z ≤ c})
      (φ.vertex x) (φ.vertex y) {z | t ≤ G.orbitAdjustedHeight a (φ.vertex x) z} ↔
    ω ∈ connectionAvoidingHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      x y {z | t ≤ G.orbitAdjustedHeight a x z} := by
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c}) =
      ω ∩ Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    have hD : φ.vertex ⁻¹' {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
        G.orbitAdjustedHeight a (φ.vertex x) z ≤ c} =
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
      ext z
      simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  have hconn : Percolation.Conn G.ends (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c})
      (φ.vertex x) (φ.vertex y) ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y := by
    rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask]
  have hhit : φ.edge '' ω ∈ restrictedHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a (φ.vertex x) z})
      (φ.vertex x) {z | t ≤ G.orbitAdjustedHeight a (φ.vertex x) z} ↔
    ω ∈ restrictedHit G.ends
      (Percolation.internalEdges G.ends {z | ad ≤ G.orbitAdjustedHeight a x z})
      x {z | t ≤ G.orbitAdjustedHeight a x z} := by
    constructor
    · rintro ⟨z,hz,hxz⟩
      obtain ⟨w,rfl⟩ := φ.vertex.surjective z
      refine ⟨w,?_,(G.adjustedHalfspaceConn_aut a ha ad φ ω x x w).mp hxz⟩
      simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hz
    · rintro ⟨z,hz,hxz⟩
      refine ⟨φ.vertex z,?_,(G.adjustedHalfspaceConn_aut a ha ad φ ω x x z).mpr hxz⟩
      simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hz
  exact and_congr hconn (not_congr hhit)

lemma mixedHeightLayerMoment_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u ad t : ℝ) (φ : G.Aut) (x : V) :
    G.mixedHeightLayerMoment a p d c l u ad t (φ.vertex x) =
      G.mixedHeightLayerMoment a p d c l u ad t x := by
  unfold mixedHeightLayerMoment
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  simp only [G.orbitAdjustedHeight_aut a ha]
  split_ifs
  · conv_lhs => rw [←G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
      (measurableSet_connectionAvoidingHit G.ends _ _ _ _ _)]
    congr 1
    ext ω
    exact G.mixedHeight_connection_event_aut a ha d c ad t φ ω x y
  · rfl

omit [Countable V] [Countable E] in
lemma mixedHeightLayerMoment_le_continuation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (_hM : 0 ≤ M)
    (x v : V)
    (hlo : -ell-R-M ≤ G.orbitAdjustedHeight a x v)
    (hhi : G.orbitAdjustedHeight a x v ≤ -ell-R) :
    G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v ≤
      ∑' w, if -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
          G.orbitAdjustedHeight a x w ≤ -ell-k then
        G.law p (connectionAvoidingHit G.ends
          (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
          (Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
            G.orbitAdjustedHeight a x z ≤ -ell})
          v w {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}) else 0 := by
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : -k-R ≤ G.orbitAdjustedHeight a v w ∧ G.orbitAdjustedHeight a v w ≤ -k+R
  · have hw' : -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
        G.orbitAdjustedHeight a x w ≤ -ell-k := by
      rw [G.orbitAdjustedHeight_change_base hc hl a x v w]
      constructor <;> linarith [hw.1,hw.2]
    simp only [hw,hw']
    apply measure_mono
    apply connectionAvoidingHit_mono G.ends
    · apply Percolation.internalEdges_mono G.ends
      intro z hz
      change -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z at hz
      change -k-r-2*M-2*R ≤ G.orbitAdjustedHeight a v z
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z] at hz
      linarith
    · apply Percolation.internalEdges_mono G.ends
      intro z hz
      change -k-r ≤ G.orbitAdjustedHeight a v z ∧ G.orbitAdjustedHeight a v z ≤ 0 at hz
      change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z]
      constructor <;> linarith [hz.1,hz.2]
    · intro z hz
      change z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z at hz
      change ell ≤ G.orbitAdjustedHeight a v z
      rw [G.orbitAdjustedHeight_change_base hc hl a x v z] at hz
      linarith [hz.2]
  · simp only [hw,ite_false]
    exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
