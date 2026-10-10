import OAI.Probability.BenjaminiSchramm.BoundedOrbitDescent
import OAI.Probability.BenjaminiSchramm.MixedHeightMoment
import OAI.Probability.BenjaminiSchramm.PeakExposureGeometry
import OAI.Probability.BenjaminiSchramm.CriticalPeakBand
import OAI.Probability.BenjaminiSchramm.PeakSurgeryProbability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma mixedHeightLayerMoment_eq_of_orbit (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u ad t : ℝ) {x y : V}
    (h : G.vertexOrbit x=G.vertexOrbit y) :
    G.mixedHeightLayerMoment a p d c l u ad t x =
      G.mixedHeightLayerMoment a p d c l u ad t y := by
  obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  change φ.vertex y=x at hφ
  rw [←hφ,G.mixedHeightLayerMoment_aut a ha]

lemma mixedHeight_continuation_at_boundary
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (d N : ℕ) (hd : ∀ z, Percolation.degree G.ends z ≤ d)
    (p : unitInterval) (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell) (x u v₀ : V)
    (hu : -ell-R ≤ G.orbitAdjustedHeight a x u ∧ G.orbitAdjustedHeight a x u ≤ -ell)
    (hpath : ∃ v, ∃ q : G.fullGraph.Walk u v,
      G.vertexOrbit v=G.vertexOrbit v₀ ∧ q.length ≤ N ∧
      (∀ z ∈ q.support, -M ≤ G.orbitAdjustedHeight a u z ∧ G.orbitAdjustedHeight a u z ≤ 0) ∧
      G.orbitAdjustedHeight a u v ≤ -R) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1)))*
      G.mixedHeightLayerMoment a p (-k-r) 0 (-k-R) (-k+R) (-k-r-2*M-2*R) ell v₀ ≤
      ∑' w, if -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x w ∧
          G.orbitAdjustedHeight a x w ≤ -ell-k then
        G.law p (connectionAvoidingHit G.ends
          (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
          (Percolation.internalEdges G.ends {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
            G.orbitAdjustedHeight a x z ≤ -ell})
          u w {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}) else 0 := by
  obtain ⟨v,q,horb,hlen,hq,hend⟩ := hpath
  let P : Set V := {z | -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧
    G.orbitAdjustedHeight a x z ≤ -ell}
  let D := Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z}
  let J := Percolation.internalEdges G.ends P
  let T : Set V := {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z}
  let W : Set V := {z | -ell-k-M-2*R ≤ G.orbitAdjustedHeight a x z ∧
    G.orbitAdjustedHeight a x z ≤ -ell-k}
  have hsupp : ∀ z ∈ q.support, z ∈ P := by
    intro z hz
    change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell
    rw [G.orbitAdjustedHeight_change_base hc hl a x u z]
    have hh := hq z hz
    constructor <;> linarith [hu.1,hu.2,hh.1,hh.2]
  have hg : G.fullGraph=Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  obtain ⟨q',hqlen,hqsupp⟩ := walk_internal_restriction G.ends (q.map f) P (by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    change z ∈ q.support.map id at hz
    exact hsupp z (by simpa only [List.map_id_fun,id_eq] using hz))
  have hlen' : q'.length ≤ N := by
    rw [hqlen,SimpleGraph.Walk.length_map]
    exact hlen
  have havoid : ∀ z ∈ q'.support, z ∉ T := by
    intro z hz hzt
    rw [hqsupp,SimpleGraph.Walk.support_map] at hz
    change z ∈ q.support.map id at hz
    have hzq : z ∈ q.support := by simpa only [List.map_id_fun,id_eq] using hz
    have hh := (hsupp z hzq).2
    exact (not_le_of_gt hell) (by linarith [hzt.2])
  have hJD : J ⊆ D := Percolation.internalEdges_mono G.ends (by
    intro z hz
    change -ell-k-r-R-M ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell at hz
    change -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z
    linarith [hz.1])
  have hroot := mixed_root_walk_layer_moment G.ends hl d hd p D J hJD T W u v q' havoid
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(N+1))) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q'.length+1))) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1
      (Nat.mul_le_mul_left d (Nat.add_le_add_right hlen' 1)))
  have hvlo : -ell-R-M ≤ G.orbitAdjustedHeight a x v := by
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    have hh := (hq v q.end_mem_support).1
    linarith [hu.1]
  have hvhi : G.orbitAdjustedHeight a x v ≤ -ell-R := by
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    linarith [hu.2]
  rw [←G.mixedHeightLayerMoment_eq_of_orbit a ha p _ _ _ _ _ _ horb]
  have hroot' := hroot
  simp only [D,J,T,W,Set.mem_ofPred_eq] at hroot'
  exact (mul_le_mul' hcost
    (G.mixedHeightLayerMoment_le_continuation hc hl a p R M k r ell hR hM x v hvlo hvhi)).trans hroot'

def fullPeakDownHit (a : V → ℝ) (ell : ℝ) (x : V) : Set (Set E) :=
  strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x x ∩
    restrictedHit G.ends Set.univ x {z | G.orbitAdjustedHeight a x z ≤ -ell}

lemma measurableSet_fullPeakDownHit (a : V → ℝ) (ell : ℝ) (x : V) :
    MeasurableSet (G.fullPeakDownHit a ell x) :=
  (measurableSet_strictHeightPeakConnection G.ends _ x x).inter
    (measurableSet_restrictedHit G.ends Set.univ x _)

omit [Countable V] [Countable E] in
lemma fullPeakDownHit_subset_exposed
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R M k r ell : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hell : 0 < ell)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (x : V) :
    G.fullPeakDownHit a ell x ⊆
      (restrictedHit G.ends
        (Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z})
        x {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z})ᶜ ∩
      restrictedHit G.ends
        ((Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z}) \
          Percolation.internalEdges G.ends {z | G.orbitAdjustedHeight a x z ≤ -ell})
        x {z | -ell-R ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -ell} := by
  rintro ω ⟨⟨_hxx,hpeak⟩,y,hy,hxy⟩
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a x w-G.orbitAdjustedHeight a x v| ≤ R := by
    intro e v w hv hw
    rw [G.orbitAdjustedHeight_change_base hc hl a x v w,add_sub_cancel_left]
    exact hjump e v w hv hw
  obtain ⟨z,hzlo,hzhi,hxz⟩ := upper_cluster_crossing_cover G.ends (G.orbitAdjustedHeight a x)
    R (-ell) hj Set.univ ω x y (by rw [G.orbitAdjustedHeight_self]; linarith) hy hxy
  have hmask : Set.univ \ Percolation.internalEdges G.ends {z | G.orbitAdjustedHeight a x z ≤ -ell} ⊆
      Percolation.internalEdges G.ends {z | -ell-k-r-2*M-3*R ≤ G.orbitAdjustedHeight a x z} :=
    upper_mask_lower_bound G.ends (G.orbitAdjustedHeight a x) R (-ell) _ hj Set.univ (by linarith)
  refine ⟨?_,z,⟨hzlo,hzhi⟩,?_⟩
  · rintro ⟨v,⟨hvx,hv⟩,hxv⟩
    have hh := hpeak v (Percolation.conn_mono G.ends Set.inter_subset_left hxv) hvx
    have hself := G.orbitAdjustedHeight_self a x
    linarith
  · apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _ ?_) hxz
    intro e he
    exact ⟨hmask he,he.2⟩

end CriticalPercolation.BondGraph

end

end OAI
