import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricFaces

namespace OAI

section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
noncomputable def tailEquiv (p n:ℕ) : Fin n ≃ {x:Fin (p+n) // p≤x.val} where
  toFun i := ⟨Fin.natAdd p i,by simp⟩
  invFun x := ⟨x.val.val-p,by omega⟩
  left_inv _ := by apply Fin.ext; simp
  right_inv _ := by apply Subtype.ext; apply Fin.ext; dsimp; omega
noncomputable def stabilize (p n:ℕ) : G n →* G (p+n) :=
  Equiv.Perm.ofSubtype.comp (Equiv.permCongrHom (tailEquiv p n)).toMonoidHom
lemma stabilize_apply_tail (p n:ℕ) (g:G n) (i:Fin n) :
    stabilize p n g (Fin.natAdd p i)=Fin.natAdd p (g i) := by
  change Equiv.Perm.ofSubtype ((Equiv.permCongrHom (tailEquiv p n)) g) _ = _
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp)]
  change ((tailEquiv p n) (g ((tailEquiv p n).symm ((tailEquiv p n) i)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl
lemma stabilize_apply_head (p n:ℕ) (g:G n) (i:Fin p) :
    stabilize p n g (Fin.castAdd n i)=Fin.castAdd n i := by
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  exact not_le.mpr i.isLt
lemma stabilize_injective (p n:ℕ) : Function.Injective (stabilize p n) := by
  intro _ _ gh
  apply Equiv.ext
  intro i
  have hi := congrArg (fun g:G (p+n)=>g (Fin.natAdd p i)) gh
  simpa only [stabilize_apply_tail,Fin.natAdd_inj] using hi
lemma stabilize_range (p n:ℕ) : (stabilize p n).range =
    MulAction.stabilizer (G (p+n)) (standard p n) := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩
    apply ext
    intro i
    exact stabilize_apply_head p n h i
  · intro hg
    have hfix (i:Fin p) : g (Fin.castAdd n i)=Fin.castAdd n i :=
      congrArg (fun f:Configuration (p+n) p=>f i) hg
    have hr : g ∈ (Equiv.Perm.ofSubtype : Equiv.Perm {x:Fin (p+n)//p≤x.val} →* G (p+n)).range := by
      rw [Equiv.Perm.mem_range_ofSubtype_iff]
      intro x hx
      change p≤x.val
      by_contra hp
      have he := hfix ⟨x.val,by omega⟩
      exact (Equiv.Perm.mem_support.mp hx) he
    obtain ⟨h,hh⟩ := hr
    refine ⟨(Equiv.permCongrHom (tailEquiv p n)).symm h,?_⟩
    change Equiv.Perm.ofSubtype ((Equiv.permCongrHom (tailEquiv p n)) ((Equiv.permCongrHom (tailEquiv p n)).symm h))=g
    rw [MulEquiv.apply_symm_apply]
    exact hh
noncomputable def standardStabilizerEquiv (p n:ℕ) : G n ≃*
    MulAction.stabilizer (G (p+n)) (standard p n) :=
  (MulEquiv.ofBijective (stabilize p n).rangeRestrict ⟨fun _ _ h=>stabilize_injective p n (congrArg Subtype.val h),
    fun x=>by obtain ⟨g,hg⟩:=x.property; exact ⟨g,Subtype.ext hg⟩⟩).trans
    (MulEquiv.subgroupCongr (stabilize_range p n))
lemma standardStabilizerEquiv_subtype (p n:ℕ) :
    (MulAction.stabilizer (G (p+n)) (standard p n)).subtype.comp
      (standardStabilizerEquiv p n).toMonoidHom = stabilize p n := rfl
lemma stabilize_one_H1_isIso (n:ℕ) (hn:32≤n) :
    IsIso (TrivialHomology.map (stabilize 1 n) 1) := by
  rw [← standardStabilizerEquiv_subtype,TrivialHomology.map_comp]
  have equivalenceIso := TrivialHomology.isIso_equiv (standardStabilizerEquiv 1 n) 1
  have stabilizerIso := stabilizer_H1_isIso (1+n) (by omega) (standard 1 n)
  infer_instance
end SimpleAmenable.SymmetricConfiguration

end

end OAI
