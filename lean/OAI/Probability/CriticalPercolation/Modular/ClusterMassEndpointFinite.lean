import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure
import OAI.Probability.CriticalPercolation.Criticality.SharpnessPhi
import OAI.Probability.CriticalPercolation.Modular.ClusterMassInfinite

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.FiniteClusters
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma clusterTail_iff_size {ω : Set E} {v : V} (hC : (G.cluster ω v).Finite) (s : ℕ) :
    ω ∈ G.clusterTail v s ↔ s ≤ size G ω v := by
  constructor
  · rintro ⟨A,hA,hAC,hs⟩
    exact hs.trans (Set.ncard_le_ncard hAC hC)
  · intro hs
    exact ⟨G.cluster ω v,hC,Subset.rfl,hs⟩

lemma size_insert_disconnected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : ¬(G.openGraph ω).Reachable x y)
    (hx : (G.cluster ω x).Finite) (hy : (G.cluster ω y).Finite) :
    size G (insert e ω) x = size G ω x + size G ω y := by
  unfold size
  rw [G.cluster_insert_endpoint ω e x y he,
    Set.ncard_union_eq (G.cluster_disjoint_of_not_reachable hxy) hx hy]

lemma size_insert_connected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : (G.openGraph ω).Reachable x y) :
    size G (insert e ω) x = size G ω x := by
  unfold size
  rw [G.cluster_insert_endpoint ω e x y he,G.cluster_eq_of_reachable hxy,Set.union_self]

lemma edgeMass_gap (s : ℕ) (hs : 0<s) (ω : Set E) (e : E)
    (hx : (G.cluster ω (G.ends e).out.1).Finite)
    (hy : (G.cluster ω (G.ends e).out.2).Finite) :
    (if ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s then (1:ℝ) else 0) ≤
      edgeMass G s ω e - edgeMass G s (insert e ω) e := by
  have he : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) := (G.ends e).out_eq.symm
  have hopen := LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he
  unfold edgeMass
  rw [ite_eq_left hopen,add_zero]
  by_cases hc : (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2
  · rw [ite_eq_left hc,size_insert_connected G ω e _ _ he hc]
    simp [BondGraph.twoClusterEvent,hc]
  · rw [ite_eq_right hc,size_insert_disconnected G ω e _ _ he hc hx hy]
    have hh := cappedMass_gap s (size G ω (G.ends e).out.1) (size G ω (G.ends e).out.2) hs
    simpa only [BondGraph.twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
      clusterTail_iff_size G hx,clusterTail_iff_size G hy,hc,not_false_eq_true,and_true,true_and] using hh

variable [Fintype E]
lemma finite_expect_edgeDiscrepancy (s : ℕ) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    expect w (fun ω => edgeDiscrepancy G s p ω e) =
      expect w (fun ω => if ¬ω e then edgeMass G s ω e - edgeMass G s (insert e ω) e else 0) := by
  let : DecidableEq E := Classical.decEq E
  have hflip := expect_closed_flip_decidable w hw e hp h0 h1 (fun ω => edgeMass G s ω e / p)
  have hu (ω : Set E) : (Function.update ω e True : Set E) = insert e ω := by
    ext a
    change Function.update (fun a => ω a) e True a ↔ a=e ∨ a∈ω
    by_cases ha : a=e
    · subst a; simp [Function.update]
    · simp only [Function.update_of_ne ha,ha,false_or]; rfl
  have hleft : (fun ω : Set E => if ¬ω e then p*(edgeMass G s (Function.update ω e True) e / p) else 0) =
      (fun ω => if ¬ω e then edgeMass G s (insert e ω) e else 0) := by
    funext ω
    rw [hu]
    split_ifs <;> field_simp [hp.1.ne']
  erw [hleft] at hflip
  have heq (ω : Set E) : edgeDiscrepancy G s p ω e =
      (if ¬ω e then edgeMass G s ω e else 0) -
        (if ω e then (1-p)*(edgeMass G s ω e / p) else 0) := by
    unfold edgeDiscrepancy coefficient
    change (if ω e then -(1-p)/p else 1) * edgeMass G s ω e = _
    by_cases hb : ω e <;> simp only [hb,ite_true,ite_false,not_true_eq_false,not_false_eq_true,sub_zero,zero_sub,one_mul]
    ring
  have hfunc := funext heq
  erw [hfunc,expect_sub,← hflip,← expect_sub]
  congr 1
  funext ω
  by_cases hb : ω e <;> simp [hb]

lemma finite_endpoint_le_expect (s : ℕ) (hs : 0<s) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    prob w (fun ω => ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      expect w (fun ω => edgeDiscrepancy G s p ω e) := by
  rw [finite_expect_edgeDiscrepancy G s p hp w hw e h0 h1]
  apply expect_mono hn
  intro ω
  by_cases hb : ω e
  · have hconn := LazyDFS.prop_openEdge_reachable G ω hb (G.ends e).out_eq.symm
    have hno : ¬ (ω : Set E) ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s := by
      intro hh
      exact hh.1.1 hconn
    change (if (ω : Set E) ∈ G.twoClusterEvent _ _ s then (1:ℝ) else 0) ≤ _
    simp only [hno,ite_false,hb,not_true_eq_false,le_refl]
  · simp only [hb,not_false_eq_true,ite_true]
    exact edgeMass_gap G s hs ω e (G.finite_cluster_of_finite_bonds (Set.toFinite ω) _)
      (G.finite_cluster_of_finite_bonds (Set.toFinite ω) _)

lemma finite_endpoint_le_integral (s : ℕ) (hs : 0<s) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (e : E) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      ∫ ω, edgeDiscrepancy G s p ω e ∂G.law p := by
  have hh := finite_endpoint_le_expect G s hs p hp (fun _ => BernoulliProduct.bitWeight p)
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    e (by simp [BernoulliProduct.bitWeight]) (by simp [BernoulliProduct.bitWeight])
  rw [BondGraph.law,← BernoulliProduct.law_const,BernoulliProduct.integral_law_eq_expect]
  convert hh using 1
  · exact (Sharpness.probability_eq_real p
      (fun ω => ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)).symm
  · rfl

end CriticalPercolation.FiniteClusters
end
end

end OAI
