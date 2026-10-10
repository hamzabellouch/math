import OAI.Probability.BenjaminiSchramm.SlabCrossing
import OAI.Probability.BenjaminiSchramm.EventLeftContinuity

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def modularSlabHit (o : V) (a b c : ℝ) : Set (Set E) :=
  {ω | ∃ y, Percolation.Conn G.ends
    (ω ∩ Percolation.internalEdges G.ends (G.modularSlab o a c)) o y ∧
      b ≤ G.modularLogHeight o y}

lemma modularSlabHit_upper (o : V) (a b c : ℝ) : IsUpperSet (G.modularSlabHit o a b c) := by
  rintro ω η hωη ⟨y,hxy,hy⟩
  exact ⟨y,Percolation.conn_mono G.ends (Set.inter_subset_inter_left _ hωη) hxy,hy⟩

lemma modularSlabHit_finiteWitness (o : V) (a b c : ℝ) :
    Percolation.FiniteWitness (G.modularSlabHit o a b c) := by
  rintro ω ⟨y,hxy,hy⟩
  obtain ⟨s,hs,hconn⟩ := Percolation.finiteWitness_conn G.ends o y _ hxy
  refine ⟨s,fun _ he => (hs he).1,y,?_,hy⟩
  have hsub : (s : Set E) ⊆ (s : Set E) ∩
      Percolation.internalEdges G.ends (G.modularSlab o a c) := fun _ he => ⟨he,(hs he).2⟩
  exact Percolation.conn_mono G.ends hsub hconn

lemma measurableSet_modularSlabHit [Countable E] (o : V) (a b c : ℝ) :
    MeasurableSet (G.modularSlabHit o a b c) :=
  Percolation.measurableSet_finiteWitness _ (G.modularSlabHit_upper o a b c)
    (G.modularSlabHit_finiteWitness o a b c)

theorem modularSlabHit_left_tendsto [Countable E] (o : V) (a b c : ℝ)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => G.law (q n) (G.modularSlabHit o a b c)) atTop
      (𝓝 (G.law p (G.modularSlabHit o a b c))) :=
  law_finiteWitness_left_tendsto _ (G.modularSlabHit_upper o a b c)
    (G.modularSlabHit_finiteWitness o a b c) p q hmono hqp hq

end CriticalPercolation.BondGraph

end

end OAI
