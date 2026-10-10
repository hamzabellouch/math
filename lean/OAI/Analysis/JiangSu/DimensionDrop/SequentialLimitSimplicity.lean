import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.Limit
import OAI.Analysis.JiangSu.DimensionDrop.TraceExistence

namespace OAI


noncomputable section
namespace SequentialCStar
open Pureness Filter
open scoped Topology

variable {D : Type*} [CStarAlgebra D]

lemma selfAdjoint_span_star {g x : D} (hg : IsSelfAdjoint g)
    (hx : x∈TwoSidedIdeal.span {g}) : star x∈TwoSidedIdeal.span {g} := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx,hg.star_eq]
    exact TwoSidedIdeal.subset_span (Set.mem_singleton g)
  | zero => simp
  | add x y _ _ hx hy => simpa only [star_add] using (TwoSidedIdeal.span {g}).add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using (TwoSidedIdeal.span {g}).neg_mem hx
  | left_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_right (star x) (star a) hx
  | right_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_left (star a) (star x) hx

def generatedClosedStarIdeal {g : D} (hg : IsSelfAdjoint g) : ClosedStarIdeal D where
  ideal := closedTwoSidedIdeal (TwoSidedIdeal.span {g})
  isClosed := by rw [coe_closedTwoSidedIdeal]; exact isClosed_closure
  star_mem := by
    intro x hx
    rw [←SetLike.mem_coe,coe_closedTwoSidedIdeal] at hx ⊢
    obtain ⟨u,hu,hux⟩ := mem_closure_iff_seq_limit.mp hx
    exact isClosed_closure.mem_of_tendsto hux.star
      (Eventually.of_forall (fun n => subset_closure (selfAdjoint_span_star hg (hu n))))

lemma generatedClosedStarIdeal_mem {g : D} (hg : IsSelfAdjoint g) :
    g∈(generatedClosedStarIdeal hg).ideal := by
  change g∈closedTwoSidedIdeal (TwoSidedIdeal.span {g})
  rw [←SetLike.mem_coe,coe_closedTwoSidedIdeal]
  exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton g))

lemma generatedClosedStarIdeal_le {g : D} (hg : IsSelfAdjoint g)
    (I : TwoSidedIdeal D) (hI : IsClosed (I:Set D)) (hgI : g∈I) :
    (generatedClosedStarIdeal hg).ideal≤I := by
  change closedTwoSidedIdeal (TwoSidedIdeal.span {g})≤I
  rw [TwoSidedIdeal.le_iff,coe_closedTwoSidedIdeal]
  apply closure_minimal _ hI
  exact TwoSidedIdeal.span_le.mpr (by simpa)

namespace System
variable {C : ℕ → Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (S : System C)

def EventuallyFull : Prop := ∀ n (a : C n),a≠0 →
  ∃ (m : ℕ) (h : n≤ m),∀ I : TwoSidedIdeal (C m),S.map h a∈I → I=⊤

variable [PartialOrder S.Limit] [StarOrderedRing S.Limit]

lemma closedStarIdeal_trivial (hS : S.EventuallyFull) (J : ClosedStarIdeal S.Limit) :
    J.ideal=⊥ ∨ J.ideal=⊤ := by
  by_cases hJ : J.ideal=⊤
  · exact Or.inr hJ
  left
  let π : S.Limit →⋆ₐ[ℂ] J.Quotient :=
    { J.quotientMap with map_star' := J.quotientMap_star }
  have hker (x : S.Limit) : π x=0 ↔ x∈J.ideal := by
    change J.ideal.ringCon.mk' x=J.ideal.ringCon.mk' 0 ↔ x∈J.ideal
    exact ⟨Quotient.exact,Quotient.sound⟩
  have hπ1 : π 1≠0 := by
    intro h
    exact hJ (J.ideal.eq_top ((hker 1).mp h))
  have hinj (n : ℕ) : Function.Injective (π.comp (S.inclusion n)) := by
    apply (π.comp (S.inclusion n)).toLinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro a ha
    change a=0
    by_contra ha0
    obtain ⟨m,hnm,hfull⟩ := hS n a ha0
    let I := TwoSidedIdeal.ker (π.comp (S.inclusion m))
    have he : S.map hnm a∈I := by
      apply (TwoSidedIdeal.mem_ker _).mpr
      change π (S.inclusion m (S.map hnm a))=0
      rw [S.inclusion_compatible]
      exact ha
    have hI := hfull I he
    have h1 : (1:C m)∈I := I.one_mem hI
    apply hπ1
    have he1 := (TwoSidedIdeal.mem_ker _).mp h1
    change π (S.inclusion m 1)=0 at he1
    simpa using he1
  have hnorm (n : ℕ) (a : C n) : ‖π (S.inclusion n a)‖=‖a‖ :=
    NonUnitalStarAlgHom.norm_map (π.comp (S.inclusion n)).toNonUnitalStarAlgHom (hinj n) a
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n,a,ha⟩ := S.finite_stage_approximation x (half_pos hε)
  have hπx : π x=0 := (hker x).mpr hx
  have hA : ‖a‖<ε/2 := by
    rw [←hnorm n a]
    have h := NonUnitalStarAlgHom.norm_apply_le π (S.inclusion n a-x)
    rw [map_sub,hπx,sub_zero,norm_sub_rev] at h
    exact h.trans_lt ha
  have h := norm_add_le (x-S.inclusion n a) (S.inclusion n a)
  rw [sub_add_cancel,S.inclusion_norm] at h
  linarith

theorem limit_topologicallySimple (hS : S.EventuallyFull) : TopologicallySimple S.Limit := by
  intro I hI
  by_cases h0 : I=⊥
  · exact Or.inl h0
  right
  obtain ⟨x,hx,hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h0)
  have hxne : x≠0 := by simpa using hx0
  have hg : IsSelfAdjoint (star x*x) := IsSelfAdjoint.star_mul_self x
  let J := generatedClosedStarIdeal hg
  have hJI : J.ideal≤I := generatedClosedStarIdeal_le hg I hI (I.mul_mem_left _ _ hx)
  rcases S.closedStarIdeal_trivial hS J with hbot|htop
  · have hz := generatedClosedStarIdeal_mem hg
    change star x*x∈J.ideal at hz
    rw [hbot,TwoSidedIdeal.mem_bot] at hz
    have hn := CStarRing.norm_star_mul_self (x := x)
    rw [hz,norm_zero] at hn
    have : ‖x‖=0 := by nlinarith [norm_nonneg x]
    exact False.elim (hxne (norm_eq_zero.mp this))
  · exact top_unique (htop ▸ hJI)

end System
end SequentialCStar

end


noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction
open scoped ComplexOrder CStarAlgebra

lemma system_eventuallyFull : system.EventuallyFull := by
  intro n f hf
  obtain ⟨m,h,hf'⟩ := eventually_fiberwise_nonzero n f hf
  refine ⟨m,h,?_⟩
  intro I hI
  exact dimensionDrop_full_of_fiberwise_nonzero _ hf' I hI

theorem simple : Pureness.TopologicallySimple Algebra :=
  system.limit_topologicallySimple system_eventuallyFull

end OriginalJiangSu

end

end OAI
