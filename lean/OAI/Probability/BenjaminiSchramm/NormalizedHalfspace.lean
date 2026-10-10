import OAI.Probability.BenjaminiSchramm.ModularCrossingRate
import OAI.Probability.BenjaminiSchramm.HeightOrbitConnection

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedHalfspaceHit (a : V → ℝ) (x : V) (b t : ℝ) : Set (Set E) :=
  restrictedHit G.ends (Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v}) x
    {v | t ≤ G.orbitAdjustedHeight a x v}

def infimalAdjustedCrossing (a : V → ℝ) (p : unitInterval) (t : ℝ) : ℝ≥0∞ :=
  ⨅ x, G.law p (G.adjustedHalfspaceHit a x 0 t)

lemma adjustedHalfspaceHit_zero (a : V → ℝ) (x : V) :
    G.adjustedHalfspaceHit a x 0 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact ⟨x,by simp,Percolation.conn_refl G.ends _ x⟩

@[simp] lemma infimalAdjustedCrossing_zero [Nonempty V] (a : V → ℝ) (p : unitInterval) :
    G.infimalAdjustedCrossing a p 0 = 1 := by
  simp only [infimalAdjustedCrossing,G.adjustedHalfspaceHit_zero,measure_univ,ciInf_const]

lemma adjustedHalfspaceHit_upper (a : V → ℝ) (x : V) (b t : ℝ) :
    IsUpperSet (G.adjustedHalfspaceHit a x b t) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,Percolation.conn_mono G.ends (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma adjustedHalfspaceHit_finiteWitness (a : V → ℝ) (x : V) (b t : ℝ) :
    Percolation.FiniteWitness (G.adjustedHalfspaceHit a x b t) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := Percolation.finiteWitness_conn G.ends x y _ hxy
  refine ⟨s,fun _ he => (hs he).1,y,hy,?_⟩
  exact Percolation.conn_mono G.ends (show (s : Set E) ⊆ (s : Set E) ∩
    Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v}
      from fun _ he => ⟨he,(hs he).2⟩) hconn

lemma adjustedHalfspaceHit_hasFiniteOpenWitness (a : V → ℝ) (x : V) (b t : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.adjustedHalfspaceHit a x b t) := by
  intro ω hω
  obtain ⟨s,hs,hsa⟩ := G.adjustedHalfspaceHit_finiteWitness a x b t ω hω
  exact ⟨s,s.finite_toSet,hs,hsa⟩

lemma measurableSet_adjustedHalfspaceHit [Countable E] (a : V → ℝ) (x : V) (b t : ℝ) :
    MeasurableSet (G.adjustedHalfspaceHit a x b t) :=
  Percolation.measurableSet_finiteWitness _ (G.adjustedHalfspaceHit_upper a x b t)
    (G.adjustedHalfspaceHit_finiteWitness a x b t)

lemma Aut.adjustedHalfspaceHit_preimage (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (x : V) (b t : ℝ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.adjustedHalfspaceHit a (φ.vertex x) b t =
      G.adjustedHalfspaceHit a x b t := by
  have hD : φ.vertex ⁻¹' {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v} =
      {v | b ≤ G.orbitAdjustedHeight a x v} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  ext ω
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v}) =
      ω ∩ Percolation.internalEdges G.ends {v | b ≤ G.orbitAdjustedHeight a x v} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ← Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  have hconn (y : V) :
      Percolation.Conn G.ends (φ.edge '' ω ∩ Percolation.internalEdges G.ends
        {v | b ≤ G.orbitAdjustedHeight a (φ.vertex x) v}) (φ.vertex x) (φ.vertex y) ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | b ≤ G.orbitAdjustedHeight a x v}) x y := by
    rw [← Percolation.conn_aut_iff G.ends φ.preserves,hmask]
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    exact ⟨z,by simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hy,(hconn z).mp hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨φ.vertex y,by simpa only [Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha] using hy,
      (hconn y).mpr hxy⟩

lemma Aut.adjustedHalfspaceHit_measure [Countable E] (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (p : unitInterval)
    (x : V) (b t : ℝ) :
    G.law p (G.adjustedHalfspaceHit a (φ.vertex x) b t) = G.law p (G.adjustedHalfspaceHit a x b t) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_adjustedHalfspaceHit _ _ _ _),Aut.adjustedHalfspaceHit_preimage G a ha φ]

lemma infimalAdjustedCrossing_le_one [Nonempty V] (a : V → ℝ) (p : unitInterval) (t : ℝ) :
    G.infimalAdjustedCrossing a p t ≤ 1 :=
  (iInf_le (fun x => G.law p (G.adjustedHalfspaceHit a x 0 t)) (Classical.arbitrary V)).trans prob_le_one

theorem infimalAdjustedCrossing_supermultiplicative [Encodable V] [Countable E] [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (a : V → ℝ) (m M : ℝ) (hm : 0 < m) (ha : ∀ x, m ≤ a x ∧ a x ≤ M)
    (p : unitInterval) {s t : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t) :
    G.infimalAdjustedCrossing a p s * G.infimalAdjustedCrossing a p t ≤
      G.infimalAdjustedCrossing a p (s+t) := by
  by_cases hs0 : s = 0
  · simp only [hs0,zero_add,G.infimalAdjustedCrossing_zero,one_mul,le_refl]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  let D := Real.log M-Real.log m
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.log_le_log hm
    ((ha (Classical.arbitrary V)).1.trans (ha (Classical.arbitrary V)).2))
  let R := D+max 0 (Real.log (K : ℝ))
  have hR : 0 ≤ R := add_nonneg hD (le_max_left _ _)
  apply le_iInf
  intro x
  have hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
    intro e u v hu hv
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v,add_sub_cancel_left]
    have hr := G.modularLogHeight_edge_jump hc hl K hK u u v e hu hv
    rw [G.modularLogHeight_self,sub_zero] at hr
    have ht := abs_add_le (G.orbitAdjustedHeight a u v-G.modularLogHeight u v) (G.modularLogHeight u v)
    rw [sub_add_cancel] at ht
    exact ht.trans (add_le_add (G.orbitAdjustedHeight_sub_bound a m M hm ha u v)
      (hr.trans (le_max_right _ _)))
  have hcont (z : V) (hz : s ≤ G.orbitAdjustedHeight a x z)
      (_hzR : G.orbitAdjustedHeight a x z ≤ s+R) :
      G.infimalAdjustedCrossing a p t ≤ BernoulliProduct.law (fun _ : E => p)
        (restrictedHit G.ends (Percolation.internalEdges G.ends {v | s ≤ G.orbitAdjustedHeight a x v})
          z {v | s+t ≤ G.orbitAdjustedHeight a x v}) := by
    apply (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 t)) z).trans
    rw [BernoulliProduct.law_const]
    apply measure_mono
    rintro ω ⟨y,hy,hzy⟩
    change t ≤ G.orbitAdjustedHeight a z y at hy
    refine ⟨y,?_,Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
      (Percolation.internalEdges_mono G.ends ?_)) hzy⟩
    · change s+t ≤ G.orbitAdjustedHeight a x y
      rw [G.orbitAdjustedHeight_change_base hc hl a x z y]
      linarith
    · intro v hv
      change 0 ≤ G.orbitAdjustedHeight a z v at hv
      change s ≤ G.orbitAdjustedHeight a x v
      rw [G.orbitAdjustedHeight_change_base hc hl a x z v]
      linarith
  have hprod := halfspace_crossing_fresh_product G.ends (fun _ : E => p)
    (G.orbitAdjustedHeight a x) R hR hjump x 0 s (s+t) (by simp) (by simpa using hspos)
    (G.infimalAdjustedCrossing a p t) hcont
  simp only [BernoulliProduct.law_const] at hprod
  exact (mul_le_mul' (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 s)) x) le_rfl).trans hprod

end CriticalPercolation.BondGraph

end

end OAI
