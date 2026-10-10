import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialCoverSystem

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GenerationUpstairs
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem sourceAlignedGroup_univ_eq_top :
    sourceAlignedGroup a r m hm M B.t Finset.univ=⊤ := by
  classical
  let H := sourceAlignedGroup a r m hm M B.t Finset.univ
  have hx (b : SmallConditional m) : PresentedGroup.of (Sum.inl b) ∈ H :=
    alignedGroup_input B.t _ _ b (Finset.subset_univ _)
  have ht (u : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
      B.t u ∈ (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm)))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact alignedGroup_conjugate B.t _ _ u
    · intro hy
      have hh := alignedGroup_conjugate B.t _ _ u⁻¹ hy
      have he : B.t u⁻¹*(B.t u*y*(B.t u)⁻¹)*(B.t u⁻¹)⁻¹=y := by
        rw [map_inv]; group
      rw [he] at hh
      exact hh
  have hn : (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm))))=⊤ := by
    apply top_unique
    intro z _
    apply PresentedGroup.generated_by _ (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm)))) _ z
    intro j
    cases j with
    | inl b => exact H.le_normalizer (hx b)
    | inr k =>
      have hh := ht (Multiplicative.ofAdd (FreeAbelianGroup.of k))
      rw [B.t_base] at hh
      exact hh
  let : H.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  let q := QuotientGroup.mk' H
  let f := q.comp B.t
  have hgen (z : BoundedRelationCover M (alternatingGenerator a r m hm)) :
      q z ∈ f.range := by
    change z ∈ f.range.comap q
    apply PresentedGroup.generated_by _ (f.range.comap q) _ z
    intro j
    cases j with
    | inl b =>
      change q (PresentedGroup.of (Sum.inl b)) ∈ f.range
      have he : q (PresentedGroup.of (Sum.inl b))=1 := (QuotientGroup.eq_one_iff _).mpr (hx b)
      rw [he]
      exact f.range.one_mem
    | inr k =>
      change q (PresentedGroup.of (Sum.inr k)) ∈ f.range
      refine ⟨Multiplicative.ofAdd (FreeAbelianGroup.of k),?_⟩
      exact congrArg q (B.t_base k)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective H z
    exact hgen w
  let : Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm)) := B.perfect
  let : IsMulCommutative (BoundedRelationCover M (alternatingGenerator a r m hm) ⧸ H) :=
    IsMulCommutative.of_comm (by
      intro x y
      obtain ⟨u,rfl⟩ := hf x
      obtain ⟨v,rfl⟩ := hf y
      rw [← map_mul,← map_mul,mul_comm])
  apply top_unique
  intro z _
  exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim (q z) 1)

end InitialCoverSystem
end GenerationUpstairs

end SimpleAmenable
end
end

end OAI
