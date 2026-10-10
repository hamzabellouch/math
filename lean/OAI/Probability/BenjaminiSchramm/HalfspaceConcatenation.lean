import OAI.Probability.BenjaminiSchramm.FreshSlabConcatenation
import OAI.Probability.BenjaminiSchramm.SubcriticalUpward

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem halfspace_crossing_fresh_product [Encodable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (x : V) (a b t : ℝ) (hx : a ≤ f x) (hxb : f x < b) (κ : ℝ≥0∞)
    (hκ : ∀ z, b ≤ f z → f z ≤ b+R →
      κ ≤ CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | b ≤ f v}) z {v | t ≤ f v})) :
    CriticalPercolation.BernoulliProduct.law q
      (restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | b ≤ f v}) * κ ≤
      CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | t ≤ f v}) := by
  let I := lowerCrossingBlock G f a b R
  let J := internalEdges G {v | b ≤ f v}
  let A := {v | b ≤ f v ∧ f v ≤ b+R}
  let B := {v | t ≤ f v}
  have hstart : restrictedHit G (internalEdges G {v | a ≤ f v}) x {v | b ≤ f v} ⊆
      restrictedHit G I x A := by
    intro ω hω
    obtain ⟨y,hy,hxy⟩ := hω
    obtain ⟨z,hz,hzR,hzconn⟩ :=
      conn_above_lower_first_crossing G f R hR hjump ω x y a b hx hxb hy hxy
    exact ⟨z,⟨hz,hzR⟩,hzconn⟩
  have hfinish : I ∪ J ⊆ internalEdges G {v | a ≤ f v} := by
    intro e he
    rcases he with he | he
    · exact internalEdges_mono G (fun _ h => h.1) he.1
    · exact internalEdges_mono G (show {v | b ≤ f v} ⊆ {v | a ≤ f v}
        from fun _ h => (hx.trans hxb.le).trans h) he
  calc
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G I x A) * κ :=
      mul_le_mul' (measure_mono hstart) le_rfl
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G (I ∪ J) x B) :=
      restrictedHit_fresh_concatenation G q I J
        (lowerCrossingBlock_disjoint_upper G f a b R) x A B κ
        (fun z hz => hκ z hz.1 hz.2)
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      obtain ⟨y,hy,hxy⟩ := hω
      exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_right _ hfinish) hxy⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def upwardHalfspaceHit (x : V) (t : ℝ) : Set (Set E) :=
  restrictedHit G.ends (Percolation.internalEdges G.ends {v | 0 ≤ G.modularLogHeight x v}) x
    {v | t ≤ G.modularLogHeight x v}

def infimalUpwardCrossing (p : unitInterval) (t : ℝ) : ℝ≥0∞ :=
  ⨅ x, G.law p (G.upwardHalfspaceHit x t)

lemma upwardHalfspaceHit_zero (x : V) : G.upwardHalfspaceHit x 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact ⟨x,by simp,Percolation.conn_refl G.ends _ x⟩

@[simp] lemma infimalUpwardCrossing_zero [Nonempty V] (p : unitInterval) :
    G.infimalUpwardCrossing p 0 = 1 := by
  simp only [infimalUpwardCrossing,G.upwardHalfspaceHit_zero,measure_univ,ciInf_const]

lemma upwardHalfspaceHit_upper (x : V) (t : ℝ) : IsUpperSet (G.upwardHalfspaceHit x t) := by
  rintro ω η hωη ⟨y,hy,hxy⟩
  exact ⟨y,hy,Percolation.conn_mono G.ends (Set.inter_subset_inter_left _ hωη) hxy⟩

lemma upwardHalfspaceHit_finiteWitness (x : V) (t : ℝ) :
    Percolation.FiniteWitness (G.upwardHalfspaceHit x t) := by
  rintro ω ⟨y,hy,hxy⟩
  obtain ⟨s,hs,hconn⟩ := Percolation.finiteWitness_conn G.ends x y _ hxy
  refine ⟨s,fun _ he => (hs he).1,y,hy,?_⟩
  exact Percolation.conn_mono G.ends (show (s : Set E) ⊆ (s : Set E) ∩
    Percolation.internalEdges G.ends {v | 0 ≤ G.modularLogHeight x v}
      from fun _ he => ⟨he,(hs he).2⟩) hconn

lemma measurableSet_upwardHalfspaceHit [Countable E] (x : V) (t : ℝ) :
    MeasurableSet (G.upwardHalfspaceHit x t) :=
  Percolation.measurableSet_finiteWitness _ (G.upwardHalfspaceHit_upper x t)
    (G.upwardHalfspaceHit_finiteWitness x t)

theorem infimalUpwardCrossing_supermultiplicative [Encodable V] [Countable E] [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {s t : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t) :
    G.infimalUpwardCrossing p s * G.infimalUpwardCrossing p t ≤
      G.infimalUpwardCrossing p (s+t) := by
  by_cases hs0 : s = 0
  · simp only [hs0,zero_add,G.infimalUpwardCrossing_zero,one_mul,le_refl]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  let R := max 0 (Real.log (K : ℝ))
  have hR : 0 ≤ R := le_max_left _ _
  apply le_iInf
  intro x
  have hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.modularLogHeight x v-G.modularLogHeight x u| ≤ R := by
    intro e u v hu hv
    exact (G.modularLogHeight_edge_jump hc hl K hK x u v e hu hv).trans (le_max_right _ _)
  have hcont (z : V) (hz : s ≤ G.modularLogHeight x z) (_hzR : G.modularLogHeight x z ≤ s+R) :
      G.infimalUpwardCrossing p t ≤ BernoulliProduct.law (fun _ : E => p)
        (restrictedHit G.ends (Percolation.internalEdges G.ends {v | s ≤ G.modularLogHeight x v})
          z {v | s+t ≤ G.modularLogHeight x v}) := by
    apply (iInf_le (fun y => G.law p (G.upwardHalfspaceHit y t)) z).trans
    rw [BernoulliProduct.law_const]
    apply measure_mono
    rintro ω ⟨y,hy,hzy⟩
    change t ≤ G.modularLogHeight z y at hy
    refine ⟨y,?_,Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
      (Percolation.internalEdges_mono G.ends ?_)) hzy⟩
    · change s+t ≤ G.modularLogHeight x y
      rw [G.modularLogHeight_change_base hc hl x z y]
      linarith
    · intro v hv
      change 0 ≤ G.modularLogHeight z v at hv
      change s ≤ G.modularLogHeight x v
      rw [G.modularLogHeight_change_base hc hl x z v]
      linarith
  have hprod := halfspace_crossing_fresh_product G.ends (fun _ : E => p)
    (G.modularLogHeight x) R hR hjump x 0 s (s+t) (by simp) (by simpa using hspos)
    (G.infimalUpwardCrossing p t) hcont
  simp only [BernoulliProduct.law_const] at hprod
  exact (mul_le_mul' (iInf_le (fun y => G.law p (G.upwardHalfspaceHit y s)) x) le_rfl).trans hprod

end CriticalPercolation.BondGraph

end

end OAI
