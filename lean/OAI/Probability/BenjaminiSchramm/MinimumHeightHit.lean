import OAI.Probability.BenjaminiSchramm.SlabLastMaximum
import OAI.Probability.BenjaminiSchramm.NormalizedHalfspace

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedHit_upper (I : Set E) (x : V) (A : Set V) :
    IsUpperSet (restrictedHit G I x A) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma restrictedHit_finiteWitness (I : Set E) (x : V) (A : Set V) :
    FiniteWitness (restrictedHit G I x A) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x y _ hxy
  refine ⟨s,fun e he => (hs he).1,y,hy,?_⟩
  exact conn_mono G (show (s : Set E) ⊆ (s : Set E) ∩ I from fun e he => ⟨he,(hs he).2⟩) hconn

lemma unrestricted_hit_minimum_disjoint (f : V → ℝ) (x : V) (A : Set V)
    (ω : Set E) (hω : ω ∈ restrictedHit G Set.univ x A) :
    ∃ z, f z ≤ f x ∧ ω ∈ DisjointOccurrence {η | Conn G η x z}
      (restrictedHit G (internalEdges G {v | f z ≤ f v}) z A) := by
  obtain ⟨y,hy,hxy⟩ := hω
  obtain ⟨z,hzx,_hzy,s,t,hs,ht,hd,hxs,hyt⟩ :=
    conn_max_height_disjoint G (fun v => -f v) Set.univ ω x y hxy
  have hD : {v : V | -f v ≤ -f z}={v | f z ≤ f v} := by ext v; simp
  rw [Set.univ_inter,hD] at hxs hyt
  refine ⟨z,neg_le_neg_iff.mp hzx,s,t,hs,ht,hd,conn_mono G Set.inter_subset_left hxs,y,hy,hyt⟩

theorem unrestricted_hit_minimum_bound [Countable V] [Countable E]
    (f : V → ℝ) (p : unitInterval) (x : V) (A : Set V) :
    law p (restrictedHit G Set.univ x A) ≤
      ∑' z, if f z ≤ f x then law p {ω | Conn G ω x z} *
        law p (restrictedHit G (internalEdges G {v | f z ≤ f v}) z A) else 0 := by
  let B (z : V) := restrictedHit G (internalEdges G {v | f z ≤ f v}) z A
  let D (z : V) := if f z ≤ f x then DisjointOccurrence {ω | Conn G ω x z} (B z) else ∅
  have hs : restrictedHit G Set.univ x A ⊆ ⋃ z, D z := by
    intro ω hω
    obtain ⟨z,hz,hdis⟩ := unrestricted_hit_minimum_disjoint G f x A ω hω
    exact Set.mem_iUnion.mpr ⟨z,by simpa only [D,ite_eq_left hz] using hdis⟩
  calc
    _ ≤ law p (⋃ z, D z) := measure_mono hs
    _ ≤ ∑' z, law p (D z) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ f x
      · simp only [D,ite_eq_left hz]
        exact bk_ennreal p _ _ (fun _ _ h hc => conn_mono G h hc)
          (restrictedHit_upper G _ _ _) (finiteWitness_conn G x z)
            (restrictedHit_finiteWitness G _ _ _)
      · simp only [D,ite_eq_right hz,measure_empty,le_refl]

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem unrestricted_adjusted_upward_hit_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (C κ : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (t : ℝ) (hκ : ∀ z, G.law p (G.adjustedHalfspaceHit a z 0 t) ≤ κ) (x : V) :
    G.law p (restrictedHit G.ends Set.univ x {v | t ≤ G.orbitAdjustedHeight a x v}) ≤ C*κ := by
  let f := G.orbitAdjustedHeight a x
  let A := {v | t ≤ f v}
  have hcont (z : V) (hz : f z ≤ f x) :
      G.law p (restrictedHit G.ends (Percolation.internalEdges G.ends {v | f z ≤ f v}) z A) ≤ κ := by
    apply le_trans (measure_mono ?_) (hκ z)
    rintro ω ⟨y,hy,hzy⟩
    have hz0 : f z ≤ 0 := by simpa only [f,G.orbitAdjustedHeight_self] using hz
    have hdom : {v : V | f z ≤ f v} ⊆ {v | 0 ≤ G.orbitAdjustedHeight a z v} := by
      intro v hv
      change 0 ≤ G.orbitAdjustedHeight a z v
      have hh := G.orbitAdjustedHeight_change_base hc hl a x z v
      change f z ≤ f v at hv
      dsimp only [f] at hv
      linarith
    refine ⟨y,?_,Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
      (Percolation.internalEdges_mono G.ends hdom)) hzy⟩
    change t ≤ G.orbitAdjustedHeight a z y
    have hh := G.orbitAdjustedHeight_change_base hc hl a x z y
    change t ≤ f y at hy
    dsimp only [f] at hy hz0
    linarith
  calc
    _ ≤ ∑' z, if f z ≤ f x then G.law p {ω | Percolation.Conn G.ends ω x z} *
        G.law p (restrictedHit G.ends (Percolation.internalEdges G.ends {v | f z ≤ f v}) z A) else 0 :=
      unrestricted_hit_minimum_bound G.ends f p x A
    _ ≤ ∑' z, G.law p {ω | Percolation.Conn G.ends ω x z}*κ := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z ≤ f x
      · rw [ite_eq_left hz]
        exact mul_le_mul' le_rfl (hcont z hz)
      · rw [ite_eq_right hz]
        exact bot_le
    _ ≤ C*κ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul' (hrow x) le_rfl

end CriticalPercolation.BondGraph

end

end OAI
