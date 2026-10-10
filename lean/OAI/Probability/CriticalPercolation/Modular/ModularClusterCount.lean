import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Modular.PeakRatioTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def reciprocalClusterMass (ω : Set E) (x : V) : ℝ≥0∞ :=
  (G.modularMass x (G.cluster ω x))⁻¹

def finiteMassIndicator (ω : Set E) (x : V) : ℝ≥0∞ :=
  if G.modularMass x (G.cluster ω x)=∞ then 0 else 1

lemma reciprocalClusterMass_le_one (ω : Set E) (x : V) : G.reciprocalClusterMass ω x≤1 :=
  ENNReal.inv_le_one.mpr (G.one_le_modularClusterMass ω x)

lemma measurable_reciprocalClusterMass [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.reciprocalClusterMass ω x) :=
  (G.measurable_modularClusterMass x x).inv

lemma measurable_finiteMassIndicator [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.finiteMassIndicator ω x) :=
  measurable_const.ite (measurableSet_eq_fun (G.measurable_modularClusterMass x x) measurable_const) measurable_const

lemma Aut.reciprocalClusterMass (φ : G.Aut) (ω : Set E) (x : V) :
    G.reciprocalClusterMass (φ.edge '' ω) (φ.vertex x)=G.reciprocalClusterMass ω x := by
  unfold CriticalPercolation.BondGraph.reciprocalClusterMass
  rw [←φ.cluster_image,φ.modularMass_image]

lemma finiteMassIndicator_eq_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable x y) :
    G.finiteMassIndicator ω x=G.finiteMassIndicator ω y := by
  unfold finiteMassIndicator
  simp only [G.cluster_eq_of_reachable h,G.modularMass_eq_top_change_base hc hl x y]

lemma stabilizerWeight_mul_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    G.stabilizerWeight x y*G.stabilizerWeight y x=1 := by
  rw [←G.stabilizerWeight_change_base hc hl x y x,G.stabilizerWeight_self]

lemma stabilizerWeight_inv (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    (G.stabilizerWeight x y)⁻¹=G.stabilizerWeight y x := by
  apply (ENNReal.mul_left_inj (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y)).mp
  rw [ENNReal.inv_mul_cancel (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y),
    G.stabilizerWeight_mul_reverse hc hl]

lemma reciprocalClusterMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable y x) :
    G.reciprocalClusterMass ω x=G.stabilizerWeight y x*G.reciprocalClusterMass ω y := by
  unfold reciprocalClusterMass
  rw [G.cluster_eq_of_reachable h.symm,G.modularMass_change_base hc hl x y,
    ENNReal.mul_inv (Or.inl (G.stabilizerWeight_pos hc hl x y).ne') (Or.inl (G.stabilizerWeight_ne_top x y)),
    G.stabilizerWeight_inv hc hl]

lemma sum_reciprocalClusterMass (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (y : V) :
    (∑' x, if x∈G.cluster ω y then G.reciprocalClusterMass ω x else 0)=G.finiteMassIndicator ω y := by
  calc
    _ = (G.modularMass y (G.cluster ω y))*G.reciprocalClusterMass ω y := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases h : x∈G.cluster ω y
      · simp only [ite_eq_left h,G.reciprocalClusterMass_change_base hc hl ω h]
      · simp only [ite_eq_right h,zero_mul]
    _ = _ := by
      unfold reciprocalClusterMass finiteMassIndicator
      split_ifs with hm
      · simp [hm]
      · exact ENNReal.mul_inv_cancel
          (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm

def incidentClusterCount (ω : Set E) (e : E) : ℝ≥0∞ :=
  ∑' x, if e∈G.incidentEdges (G.cluster ω x) then G.reciprocalClusterMass ω x else 0

lemma measurable_incidentClusterCount [Countable V] [Countable E] (e : E) :
    Measurable (fun ω : Set E => G.incidentClusterCount ω e) := by
  apply Measurable.tsum
  intro x
  exact (G.measurable_reciprocalClusterMass x).ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf measurable_const

lemma incident_cluster_iff_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) (x : V) :
    e∈G.incidentEdges (G.cluster ω x) ↔ x∈G.cluster ω a ∨ x∈G.cluster ω b := by
  constructor
  · rintro ⟨v,hv,hve⟩
    rw [he,Sym2.mem_iff] at hve
    rcases hve with rfl|rfl
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  · rintro (ha|hb)
    · exact ⟨a,ha.symm,by simp [he]⟩
    · exact ⟨b,hb.symm,by simp [he]⟩

lemma incidentClusterCount_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.incidentClusterCount ω e = if (G.openGraph ω).Reachable a b then
      G.finiteMassIndicator ω a else G.finiteMassIndicator ω a+G.finiteMassIndicator ω b := by
  unfold incidentClusterCount
  simp only [G.incident_cluster_iff_ends ω e a b he]
  by_cases hr : (G.openGraph ω).Reachable a b
  · rw [ite_eq_left hr]
    have hC := G.cluster_eq_of_reachable hr
    simp only [hC,or_self,G.sum_reciprocalClusterMass hc hl]
    exact (G.finiteMassIndicator_eq_of_reachable hc hl ω hr).symm
  · rw [ite_eq_right hr,←G.sum_reciprocalClusterMass hc hl ω a,←G.sum_reciprocalClusterMass hc hl ω b,
      ←ENNReal.tsum_add]
    apply tsum_congr
    intro x
    have hnot : ¬(x∈G.cluster ω a ∧ x∈G.cluster ω b) := fun h => hr (h.1.trans h.2.symm)
    by_cases ha : x∈G.cluster ω a <;> by_cases hb : x∈G.cluster ω b <;>
      simp_all only [true_or,or_true,false_or,ite_true,ite_false,zero_add,add_zero,and_self,not_true_eq_false]

lemma incidentClusterCount_le_two (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.incidentClusterCount ω e≤2 := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.incidentClusterCount_of_ends hc hl ω e a b he.symm]
  unfold finiteMassIndicator
  split_ifs <;> norm_num

end CriticalPercolation.BondGraph
end
end

end OAI
