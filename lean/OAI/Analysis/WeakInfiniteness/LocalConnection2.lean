import Mathlib
import OAI.Analysis.WeakInfiniteness.CyclicOrbit
import OAI.Analysis.WeakInfiniteness.ElementaryComparison
import OAI.Analysis.WeakInfiniteness.InnerSubalgebras
import OAI.Analysis.WeakInfiniteness.IrreducibleOrbits
import OAI.Analysis.WeakInfiniteness.LocalConnection

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma starLift_inr_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    (Unitization.starLift π) (a : Unitization ℂ A)=π a :=
  congrArg (fun f : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) => f a) (Equiv.symm_apply_apply Unitization.starLift π)

omit [PartialOrder A] [StarOrderedRing A] in
lemma irreducible_starLift {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) : RepresentationIrreducible (Unitization.starLift π) := by
  intro S hSc hS
  apply hπ S hSc
  intro a x hx
  simpa only [starLift_inr_apply] using hS (a : Unitization ℂ A) x hx

lemma exists_local_common_two {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) {h k : A}
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      ElementCuntzSubequiv c h ∧ ElementCuntzSubequiv c k := by
  let ρ := Unitization.starLift π
  obtain ⟨x,hx⟩ := (irreducible_starLift hπ).exists_mixed_nonzero
    (u := (h : Unitization ℂ A)) (v := (k : Unitization ℂ A)) (by simpa only [starLift_inr_apply] using hhn) (by simpa only [starLift_inr_apply] using hkn)
  let z : A := x.fst • (h*k)+h*x.snd*k
  have hz : π z ≠ 0 := by
    have he : (h : Unitization ℂ A)*x*(k : Unitization ℂ A)=(z : Unitization ℂ A) := by
      rw [← Unitization.inl_fst_add_inr_snd_eq x]
      simp only [mul_add,add_mul,Unitization.inr_mul_inl,← Unitization.inr_mul,smul_mul_assoc,← Unitization.inr_add]
      rfl
    rw [he] at hx
    simpa only [starLift_inr_apply] using hx
  have hzright : z ∈ principalRightIdeal h := by
    apply Submodule.le_topologicalClosure _
    refine ⟨x.fst • k+x.snd*k,?_⟩
    change h*(x.fst • k+x.snd*k)=z
    dsimp [z]
    rw [mul_add,mul_smul_comm,mul_assoc]
  have hzleft : star z ∈ principalRightIdeal k := by
    apply Submodule.le_topologicalClosure _
    refine ⟨star x.fst • h+star x.snd*h,?_⟩
    change k*(star x.fst • h+star x.snd*h)=star z
    simp only [z,star_add,star_smul,star_mul,hh.star_eq,hk.star_eq,mul_add,mul_smul_comm,mul_assoc]
  have hc : 0 ≤ z*star z := mul_star_self_nonneg z
  have hch := rightIdeal_square_mem_hereditary h z hh.isSelfAdjoint hzright
  have hck : star z*z ∈ hereditarySubalgebra k hk.isSelfAdjoint := by
    simpa only [star_star] using rightIdeal_square_mem_hereditary k (star z) hk.isSelfAdjoint hzleft
  refine ⟨z*star z,hc,hch,?_,elementCuntzSubequiv_of_hereditary hc hh hch,
    (element_range_cuntz_initial z).trans (elementCuntzSubequiv_of_hereditary (star_mul_self_nonneg z) hk hck)⟩
  intro he
  have he' : π z*star (π z)=0 := by simpa only [map_mul,map_star] using he
  exact hz ((CStarRing.mul_star_self_eq_zero_iff _).mp he')

lemma exists_local_common_family {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : NonUnitalRepresentationIrreducible π) {h : A}
    (hh : 0 ≤ h) (hhn : π h ≠ 0) {m : ℕ} (x : Fin m → A)
    (hx : ∀ i,0 ≤ x i ∧ π (x i) ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      ElementCuntzSubequiv c h ∧ ∀ i,ElementCuntzSubequiv c (x i) := by
  induction m generalizing h with
  | zero => exact ⟨h,hh,self_mem_hereditary h hh,hhn,cuntzSubequiv_refl _,by simp⟩
  | succ m ih =>
    obtain ⟨d,hd,hdh,hdn,hdch,hdx⟩ := exists_local_common_two hπ hh (hx 0).1 hhn (hx 0).2
    obtain ⟨c,hc,hcd,hcn,hccd,hct⟩ := ih hd hdn (fun i => x i.succ) (fun i => hx i.succ)
    refine ⟨c,hc,hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
      hd.isSelfAdjoint hdh hcd,hcn,hccd.trans hdch,?_⟩
    intro i
    exact Fin.cases (hccd.trans hdx) hct i

end

end WeakPureInfiniteness
end

end OAI
