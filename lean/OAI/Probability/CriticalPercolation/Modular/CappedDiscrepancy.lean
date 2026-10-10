import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ExpectClosedFlip
import OAI.Probability.CriticalPercolation.Entropy.BinaryLaw
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma capped_gap_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    0 ≤ min a 1 + min b 1 - min (a+b) 1 := by
  rcases le_total a 1 with ha1|ha1 <;> rcases le_total b 1 with hb1|hb1
  · rw [min_eq_left ha1,min_eq_left hb1]
    exact sub_nonneg.mpr (min_le_left _ _)
  · rw [min_eq_left ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_left hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]

def cappedMass (s m : ℕ) : ℝ := min ((m:ℝ)/s) 1

lemma cappedMass_nonneg (s m : ℕ) : 0≤cappedMass s m := by
  unfold cappedMass
  positivity

lemma cappedMass_gap (s a b : ℕ) (hs : 0<s) :
    (if s≤a ∧ s≤b then (1:ℝ) else 0) ≤
      cappedMass s a + cappedMass s b - cappedMass s (a+b) := by
  have hs' : 0<(s:ℝ) := Nat.cast_pos.mpr hs
  simp only [cappedMass,Nat.cast_add,add_div]
  split_ifs with h
  · have ha : 1 ≤ (a:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.1 : (s:ℝ)≤a))
    have hb : 1 ≤ (b:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.2 : (s:ℝ)≤b))
    rw [min_eq_right ha,min_eq_right hb]
    linarith [min_le_right ((a:ℝ)/s+(b:ℝ)/s) 1]
  · exact capped_gap_nonneg (by positivity) (by positivity)

namespace BondGraph
open FiniteProduct

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

def edgeClusterMass (f : ℕ → ℝ) (ω : Set E) (e : E) : ℝ :=
  ∑ v, if e ∈ G.incidentEdges (G.cluster ω v) then G.rootMass f ω v else 0

lemma edgeClusterMass_insert_gap (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    G.edgeClusterMass f ω e - G.edgeClusterMass f (insert e ω) e =
      if (G.openGraph ω).Reachable x y then 0 else
        f (G.clusterSize ω x) + f (G.clusterSize ω y) -
          f (G.clusterSize ω x + G.clusterSize ω y) := by
  have hopen : (G.openGraph (insert e ω)).Reachable x y :=
    LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he
  simp only [edgeClusterMass,G.sum_incident_rootMass f ω e x y he,
    G.sum_incident_rootMass f (insert e ω) e x y he,ite_eq_left hopen,add_zero]
  by_cases hc : (G.openGraph ω).Reachable x y
  · rw [ite_eq_left hc,G.clusterSize_insert_of_connected ω e x y he hc]
    simp only [ite_eq_left hc,add_zero,sub_self]
  · rw [ite_eq_right hc,G.clusterSize_insert_of_disconnected ω e x y he hc,ite_eq_right hc]

lemma capped_edge_gap (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y))
    (s : ℕ) (hs : 0<s) :
    (if BinaryLaw.endpointEvent G x y s ω then (1:ℝ) else 0) ≤
      G.edgeClusterMass (cappedMass s) ω e - G.edgeClusterMass (cappedMass s) (insert e ω) e := by
  rw [G.edgeClusterMass_insert_gap _ ω e x y he]
  by_cases hc : (G.openGraph ω).Reachable x y
  · simp [BinaryLaw.endpointEvent,hc]
  · have hh := cappedMass_gap s (G.clusterSize ω x) (G.clusterSize ω y) hs
    simp only [BinaryLaw.endpointEvent,hc,not_false_eq_true,true_and,ite_false,clusterSize,
      ← Set.ncard_eq_toFinset_card'] at hh ⊢
    exact hh

variable [Fintype E]

def clusterDiscrepancy (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑ e, if e ∈ G.incidentEdges (G.cluster ω v) then (if ω e then -(1-p)/p else 1) else 0

def edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  (if ω e then -(1-p)/p else 1) * G.edgeClusterMass f ω e

lemma expect_edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    expect w (fun ω => G.edgeDiscrepancy f p ω e) =
      expect w (fun ω => if ¬ω e then
        G.edgeClusterMass f ω e - G.edgeClusterMass f (insert e ω) e else 0) := by
  let : DecidableEq E := Classical.decEq E
  have hflip := expect_closed_flip_decidable w hw e hp h0 h1 (fun ω => G.edgeClusterMass f ω e / p)
  have hu (ω : Set E) : {a | Function.update ω e True a} = insert e ω := by
    ext a
    change Function.update (fun a => ω a) e True a ↔ a=e ∨ a∈ω
    by_cases ha : a=e
    · subst a; simp [Function.update]
    · simp only [Function.update_of_ne ha,ha,false_or]; rfl
  have hleft : (fun ω : Set E => if ¬ω e then p*(G.edgeClusterMass f (Function.update ω e True) e / p) else 0) =
      (fun ω => if ¬ω e then G.edgeClusterMass f (insert e ω) e else 0) := by
    funext ω
    rw [show (Function.update ω e True : Set E) = insert e ω from hu ω]
    split_ifs <;> field_simp [hp.1.ne']
  erw [hleft] at hflip
  have heq (ω : Set E) : G.edgeDiscrepancy f p ω e =
      (if ¬ω e then G.edgeClusterMass f ω e else 0) -
        (if ω e then (1-p)*(G.edgeClusterMass f ω e / p) else 0) := by
    change (if ω e then -(1-p)/p else 1) * G.edgeClusterMass f ω e = _
    by_cases hb : ω e <;> simp only [hb,ite_true,ite_false,not_true_eq_false,not_false_eq_true,sub_zero,zero_sub,one_mul]
    ring
  have hfunc : (fun ω : Set E => G.edgeDiscrepancy f p ω e) =
      (fun ω => (if ¬ω e then G.edgeClusterMass f ω e else 0) -
        (if ω e then (1-p)*(G.edgeClusterMass f ω e / p) else 0)) := funext heq
  erw [hfunc]
  erw [expect_sub,← hflip,← expect_sub]
  congr 1
  funext ω
  by_cases hb : ω e <;> simp [hb]

lemma endpoint_prob_le_discrepancy (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (e : E) (x y : V) (he : G.ends e = s(x,y))
    (h0 : w e False=1-p) (h1 : w e True=p) (s : ℕ) (hs : 0<s) :
    prob w (BinaryLaw.endpointEvent G x y s) ≤
      expect w (fun ω => G.edgeDiscrepancy (cappedMass s) p ω e) := by
  rw [G.expect_edgeDiscrepancy _ p hp w hw e h0 h1]
  apply expect_mono hn
  intro ω
  by_cases hb : ω e
  · have hconn : (G.openGraph ω).Reachable x y := LazyDFS.prop_openEdge_reachable G ω hb he
    simp [hb,BinaryLaw.endpointEvent,hconn]
  · simp only [hb,not_false_eq_true,ite_true]
    exact G.capped_edge_gap ω e x y he s hs

lemma sum_edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) :
    (∑ e, G.edgeDiscrepancy f p ω e) =
      ∑ v, G.rootMass f ω v * G.clusterDiscrepancy p ω v := by
  simp only [edgeDiscrepancy,edgeClusterMass,clusterDiscrepancy,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

end BondGraph
end CriticalPercolation
end
end
end

end OAI
