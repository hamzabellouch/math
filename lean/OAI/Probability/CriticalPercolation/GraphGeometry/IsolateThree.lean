import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterObjectAvoidanceCross
import OAI.Probability.CriticalPercolation.Modular.ObjectAvoidMass
import OAI.Probability.CriticalPercolation.ProductMeasure.Prob

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

def isolateThree (a s t : V) (ω : Set E) : Prop :=
  ¬(G.openGraph ω).Reachable a s ∧ ¬(G.openGraph ω).Reachable a t

def separateThree (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ ¬(G.openGraph ω).Reachable s t

def joinedPair (a s t : V) (ω : Set E) : Prop :=
  G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable s t

lemma isolateThree_eq_avoid (a s t : V) (ω : Set E) :
    Disjoint (G.clusterObject ω {a}).1 {s,t} ↔ G.isolateThree a s t ω := by
  simp [clusterObject, roots, Set.disjoint_insert_right, Set.disjoint_singleton_right, isolateThree]

lemma isolateThree_decreasing (a s t : V) {ω ω' : Set E} (h : ω ⊆ ω')
    (hi : G.isolateThree a s t ω') : G.isolateThree a s t ω := by
  have hG : G.openGraph ω ≤ G.openGraph ω' :=
    SimpleGraph.fromEdgeSet_mono (Set.image_mono h)
  exact ⟨fun hs => hi.1 (hs.mono hG), fun ht => hi.2 (ht.mono hG)⟩

lemma separateThree_rotate (a s t : V) (ω : Set E) :
    G.separateThree t a s ω ↔ G.separateThree a s t ω := by
  constructor
  · rintro ⟨⟨hta, hts⟩, has⟩
    exact ⟨⟨has, fun h => hta h.symm⟩, fun h => hts h.symm⟩
  · rintro ⟨⟨has, hat⟩, hst⟩
    exact ⟨⟨fun h => hat h.symm, fun h => hst h.symm⟩, has⟩

lemma isolateThree_inter (a s t : V) (ω : Set E) :
    (G.isolateThree a s t ω ∧ G.isolateThree t a s ω) ↔ G.separateThree a s t ω := by
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨ha, fun h => ht.2 h.symm⟩
  · rintro ⟨ha, hst⟩
    exact ⟨ha, (G.separateThree_rotate a s t ω).mpr ⟨ha, hst⟩ |>.1⟩

variable [Fintype V] [Fintype E]

theorem threeCluster_avoidance (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z) (hc : ∀ e, 0 < w e False)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) :
    prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair a s t) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  let f : ClusterObject V E → ℝ := fun C => if b ∈ C.1 then 1 else 0
  let g : ClusterObject V E → ℝ := fun C => if (G.openGraph C.2).Reachable s t then 1 else 0
  have hf : Monotone f := indicator_monotone (fun _ _ h hm => h.1 hm)
  have hg : Monotone g := by
    intro C D h
    dsimp only [g]
    by_cases hC : (G.openGraph C.2).Reachable s t
    · have hD : (G.openGraph D.2).Reachable s t :=
        hC.mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono h.2))
      simp only [ite_eq_left hC, ite_eq_left hD, le_refl]
    · simp only [ite_eq_right hC]
      split_ifs <;> norm_num
  have hd : Disjoint ({a} : Set V) {s,t} := by simp [has, hat]
  have h := G.clusterObject_avoidance_cross_mul w hw hp hc hd f g hf hg
  have hf' (ω : Set E) : f (G.clusterObject ω {a}) =
      if (G.openGraph ω).Reachable a b then 1 else 0 := by simp [f, clusterObject, roots]
  have hg' (ω : Set E) : g (G.clusterObject ω {s,t}) =
      if (G.openGraph ω).Reachable s t then 1 else 0 := by
    simp only [g, G.reachable_clusterObject (Set.mem_insert s {t})]
  have hZ : G.objectAvoidTotal w {a} {s,t} = prob w (G.isolateThree a s t) := by
    unfold objectAvoidTotal prob
    apply congrArg (expect w)
    funext ω
    rw [G.isolateThree_eq_avoid a s t ω]
  have hfg : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      f (G.clusterObject ω {a}) * g (G.clusterObject ω {s,t}) else 0) =
      prob w (fun ω => G.isolateThree a s t ω ∧
        (G.openGraph ω).Reachable a b ∧ (G.openGraph ω).Reachable s t) := by
    apply congrArg (expect w)
    funext ω
    rw [hf' ω, hg' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases hb : (G.openGraph ω).Reachable a b <;>
      by_cases ht : (G.openGraph ω).Reachable s t <;> simp [hi,hb,ht]
  have hf'' : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      f (G.clusterObject ω {a}) else 0) =
      prob w (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) := by
    apply congrArg (expect w)
    funext ω
    rw [hf' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases hb : (G.openGraph ω).Reachable a b <;> simp [hi,hb]
  have hg'' : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      g (G.clusterObject ω {s,t}) else 0) = prob w (G.joinedPair a s t) := by
    apply congrArg (expect w)
    funext ω
    rw [hg' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases ht : (G.openGraph ω).Reachable s t <;> simp [hi,ht,joinedPair]
  rw [hfg,hf'',hg'',hZ] at h
  have hγ : prob w (fun ω => G.isolateThree a s t ω ∧
      (G.openGraph ω).Reachable a b ∧ (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  have hu := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  have hb := prob_split w (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    (fun ω => (G.openGraph ω).Reachable s t)
  have hβ : prob w (fun ω => (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧
      ¬(G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [separateThree]; tauto)
  have hγ' : prob w (fun ω => (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧
      (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  rw [hγ] at h
  rw [hβ, hγ'] at hb
  change prob w (G.isolateThree a s t) = prob w (G.joinedPair a s t) +
    prob w (G.separateThree a s t) at hu
  rw [hu, hb] at h
  nlinarith

omit [Fintype V] in

theorem threeCluster_harris (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z) (a s t : V) :
    (prob w (G.separateThree a s t) + prob w (G.joinedPair a s t)) *
      (prob w (G.separateThree a s t) + prob w (G.joinedPair t a s)) ≤
      prob w (G.separateThree a s t) := by
  have h := prob_harris_decreasing w hw hp (G.isolateThree a s t) (G.isolateThree t a s)
    (fun _ _ hh hi => G.isolateThree_decreasing a s t hh hi)
    (fun _ _ hh hi => G.isolateThree_decreasing t a s hh hi)
  have he := prob_congr w (G.isolateThree_inter a s t)
  rw [he] at h
  have ha := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  have ht := prob_split w (G.isolateThree t a s) (fun ω => (G.openGraph ω).Reachable a s)
  change prob w (G.isolateThree a s t) = prob w (G.joinedPair a s t) +
    prob w (G.separateThree a s t) at ha
  change prob w (G.isolateThree t a s) = prob w (G.joinedPair t a s) +
    prob w (G.separateThree t a s) at ht
  rw [prob_congr w (G.separateThree_rotate a s t)] at ht
  rw [ha, ht] at h
  nlinarith

end CriticalPercolation.BondGraph

end
end

end OAI
