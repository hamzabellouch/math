import Mathlib
import OAI.Probability.CriticalPercolation.Modular.GraphModular

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def stabilizerWeight (o x : V) : ℝ≥0∞ := ENNReal.ofReal (G.modularRatio x o)

def modularMass (o : V) (S : Set V) : ℝ≥0∞ :=
  ∑' x : V, if x∈S then G.stabilizerWeight o x else 0

lemma stabilizerWeight_ne_top (o x : V) : G.stabilizerWeight o x ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma stabilizerWeight_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : 0 < G.stabilizerWeight o x :=
  ENNReal.ofReal_pos.mpr (G.modularRatio_pos hc hl x o)

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  unfold stabilizerWeight
  rw [←ENNReal.ofReal_mul (G.modularRatio_pos hc hl a o).le]
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma modularMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S =
      G.stabilizerWeight o a * G.modularMass a S := by
  unfold modularMass
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact G.stabilizerWeight_change_base hc hl o a x
  · exact (mul_zero _).symm

lemma modularMass_eq_top_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S = ∞ ↔ G.modularMass a S = ∞ := by
  rw [G.modularMass_change_base hc hl o a S,ENNReal.mul_eq_top]
  simp [G.stabilizerWeight_ne_top o a,(G.stabilizerWeight_pos hc hl o a).ne']

lemma modularMass_mono (o : V) {S T : Set V} (h : S⊆T) :
    G.modularMass o S ≤ G.modularMass o T := by
  apply ENNReal.tsum_le_tsum
  intro x
  split_ifs with hS hT
  · rfl
  · exact False.elim (hT (h hS))
  · exact zero_le
  · rfl

lemma modularMass_finite (o : V) {S : Set V} (hS : S.Finite) :
    G.modularMass o S < ∞ := by
  classical
  unfold modularMass
  rw [tsum_eq_sum (s := hS.toFinset) (fun x hx => by
    simp only [hS.mem_toFinset] at hx
    simp only [ite_eq_right hx])]
  apply ENNReal.sum_lt_top.mpr
  intro x hx
  rw [ite_eq_left (hS.mem_toFinset.mp hx)]
  exact ENNReal.ofReal_lt_top

lemma infinite_of_modularMass_top (o : V) {S : Set V} (hS : G.modularMass o S = ∞) :
    S.Infinite := by
  intro hf
  have hh := G.modularMass_finite o hf
  rw [hS] at hh
  exact (lt_irrefl _ hh)

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

lemma Aut.modularMass_image (φ : G.Aut) (o : V) (S : Set V) :
    G.modularMass (φ.vertex o) (φ.vertex '' S) = G.modularMass o S := by
  unfold modularMass
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro x
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,Aut.stabilizerWeight]

def lightInfiniteEvent (o v : V) : Set (Set E) :=
  {ω | (G.cluster ω v).Infinite ∧ G.modularMass o (G.cluster ω v) < ∞}

def heavyClusterEvent (o v : V) : Set (Set E) :=
  {ω | G.modularMass o (G.cluster ω v) = ∞}

lemma measurable_modularClusterMass [Countable V] [Countable E] (o v : V) :
    Measurable (fun ω : Set E => G.modularMass o (G.cluster ω v)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (G.measurable_reachable v x).setOf measurable_const

lemma measurableSet_lightInfiniteEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.lightInfiniteEvent o v) := by
  exact (G.measurable_infinite_cluster v).setOf.inter
    (measurableSet_lt (G.measurable_modularClusterMass o v) measurable_const)

lemma measurableSet_heavyClusterEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.heavyClusterEvent o v) :=
  measurableSet_eq_fun (G.measurable_modularClusterMass o v) measurable_const

lemma infiniteEvent_eq_light_union_heavy (o v : V) :
    G.infiniteEvent v = G.lightInfiniteEvent o v ∪ G.heavyClusterEvent o v := by
  ext ω
  change (G.cluster ω v).Infinite ↔
    ((G.cluster ω v).Infinite ∧ _) ∨ _
  constructor
  · intro h
    rcases lt_or_eq_of_le (le_top : G.modularMass o (G.cluster ω v) ≤ ∞) with hl|hh
    · exact Or.inl ⟨h,hl⟩
    · exact Or.inr hh
  · rintro (⟨h,_⟩|h)
    · exact h
    · exact G.infinite_of_modularMass_top o h

end CriticalPercolation.BondGraph
end
end

end OAI
