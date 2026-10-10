import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Growth.CosetSparseGrowth
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

structure Presentation (A : Type*) [Group A] where
  K : Subgroup A
  S : Set A
  one_mem : (1:A)∈S
  inv_eq : S⁻¹=S
  generates : Subgroup.closure S=⊤
  left_stable : (K:Set A)*S⊆S

namespace Presentation
variable (P : Presentation A)
abbrev X := A ⧸ P.K
abbrev projection (a : A) : P.X := QuotientGroup.mk a
abbrev root : P.X := P.projection 1

def graph : SimpleGraph P.X where
  Adj x y := x≠y ∧ ∃ g : A, ∃ s∈P.S, P.projection g=x ∧ P.projection (g*s)=y
  symm := ⟨by
    rintro x y ⟨hne,g,s,hs,rfl,rfl⟩
    refine ⟨hne.symm,g*s,s⁻¹,?_,rfl,?_⟩
    · rw [←P.inv_eq]; exact Set.inv_mem_inv.mpr hs
    · simp⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma adj_mk_iff (g : A) (y : P.X) :
    P.graph.Adj (P.projection g) y ↔ P.projection g≠y ∧ ∃ s∈P.S, P.projection (g*s)=y := by
  constructor
  · rintro ⟨hne,h,s,hs,hh,he⟩
    have hk : g⁻¹*h∈P.K := QuotientGroup.eq.mp hh.symm
    refine ⟨hne,(g⁻¹*h)*s,P.left_stable (Set.mul_mem_mul hk hs),?_⟩
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  · rintro ⟨hne,s,hs,he⟩; exact ⟨hne,g,s,hs,rfl,he⟩

lemma smul_adj_iff (a : A) (x y : P.X) :
    P.graph.Adj (a • x) (a • y) ↔ P.graph.Adj x y := by
  have hf (b : A) {x y : P.X} (h : P.graph.Adj x y) :
      P.graph.Adj (b • x) (b • y) := by
    obtain ⟨hne,g,s,hs,rfl,rfl⟩ := h
    refine ⟨fun he => hne (smul_left_cancel b he),b*g,s,hs,rfl,?_⟩
    change P.projection ((b*g)*s)=P.projection (b*(g*s))
    rw [mul_assoc]
  constructor
  · intro h; simpa using hf a⁻¹ h
  · exact hf a

def actionAut (a : A) : P.graph ≃g P.graph where
  toEquiv := MulAction.toPerm a
  map_rel_iff' := P.smul_adj_iff a _ _
def actionHom : A →* (P.graph ≃g P.graph) where
  toFun := P.actionAut
  map_one' := by ext x; exact one_smul A x
  map_mul' a b := by ext x; exact mul_smul a b x
@[simp] lemma actionAut_mk (a b : A) : P.actionAut a (P.projection b)=P.projection (a*b) := rfl

lemma reachable_mk (a : A) : P.graph.Reachable P.root (P.projection a) := by
  have ha : a∈Subgroup.closure P.S := P.generates.symm ▸ Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    by_cases he : P.root=P.projection a
    · rw [←he]
    · apply SimpleGraph.Adj.reachable
      exact ⟨he,1,a,ha,rfl,by simp⟩
  | one => exact .refl _
  | mul a b _ _ ha hb =>
    have hh := hb.map (P.actionAut a).toHom
    change P.graph.Reachable (P.projection (a*1)) (P.projection (a*b)) at hh
    simp only [mul_one] at hh
    exact ha.trans hh
  | inv a _ ha =>
    have hh := ha.symm.map (P.actionAut a⁻¹).toHom
    change P.graph.Reachable (P.projection (a⁻¹*a)) (P.projection (a⁻¹*1)) at hh
    simpa using hh
lemma connected : P.graph.Connected := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact (P.reachable_mk a).symm.trans (P.reachable_mk b)

lemma neighbors_subset (a : A) : P.graph.neighborSet (P.projection a)⊆
    (fun x : P.X => a • x) '' ball P.K P.S 1 := by
  intro y hy
  obtain ⟨hne,s,hs,rfl⟩ := (P.adj_mk_iff a y).mp hy
  exact ⟨P.projection s,⟨s,by simpa using hs,rfl⟩,rfl⟩
lemma locallyFinite (hf : (ball P.K P.S 1).Finite) : ∀ x, (P.graph.neighborSet x).Finite := by
  intro x
  induction x using Quotient.inductionOn with | _ a =>
    exact (hf.image (fun x : P.X => a • x)).subset (P.neighbors_subset a)
lemma transitive (x y : P.X) : ∃ g : P.graph ≃g P.graph, g x=y := by
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      exact ⟨P.actionAut (b*a⁻¹),by simp⟩
def geometry (hf : (ball P.K P.S 1).Finite) : HomogeneousAnalysis.Geometry P.X :=
  ⟨P.graph,P.connected,P.locallyFinite hf,P.transitive,P.root⟩

lemma walk_endpoint {x y : P.X} (p : P.graph.Walk x y) :
    ∀ g : A, P.projection g=x → ∃ h∈P.S^p.length, P.projection (g*h)=y := by
  induction p with
  | nil => intro g hg; exact ⟨1,by simp,by simpa using hg⟩
  | @cons x y z h p ih =>
    intro g hg
    obtain ⟨_,s,hs,he⟩ := (P.adj_mk_iff g y).mp (hg ▸ h)
    obtain ⟨t,ht,hz⟩ := ih (g*s) he
    refine ⟨s*t,?_,?_⟩
    · rw [SimpleGraph.Walk.length_cons,pow_succ']
      exact Set.mul_mem_mul hs ht
    · simpa only [mul_assoc] using hz
lemma reachBall_subset (n : ℕ) : GraphTopology.reachBall P.graph P.root n⊆ball P.K P.S n := by
  rintro y ⟨p,hp⟩
  obtain ⟨h,hh,he⟩ := P.walk_endpoint p 1 rfl
  exact ⟨h,Set.pow_subset_pow_right P.one_mem hp hh,by simpa using he⟩
lemma geometry_hasDegree (d : ℕ) (hg : HasDegree P.K P.S d) :
    (P.geometry (hg.1 1)).HasDegree d := by
  obtain ⟨hf,C,hC⟩ := hg
  refine ⟨C,?_⟩
  intro R
  obtain ⟨n,hn,hbound⟩ := hC R
  refine ⟨n,hn,?_⟩
  have hs : ((P.geometry (hf 1)).ball n : Set P.X)⊆ball P.K P.S n := by
    intro y hy
    exact P.reachBall_subset n ((P.geometry (hf 1)).mem_around.mp hy)
  have hc := Set.ncard_le_ncard hs (hf n)
  rw [Set.ncard_coe_finset] at hc
  exact hc.trans hbound

end Presentation
end CriticalPercolation.RelativeGrowth
end
end

end OAI
