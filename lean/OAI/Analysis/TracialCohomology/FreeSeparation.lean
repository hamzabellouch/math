import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerComparison

namespace OAI

/-! Free separation for bounded Hochschild cohomology. -/

noncomputable section

namespace PopaFinite
open FreeGroup
variable {G : Type*} [Group G]

private def partialLeft (B : Finset G) (g : G) :
    {x : B // g*(x:G) ∈ B} ≃ {x : B // g⁻¹*(x:G) ∈ B} where
  toFun x := ⟨⟨g*(x.val:G),x.property⟩,by simp⟩
  invFun x := ⟨⟨g⁻¹*(x.val:G),x.property⟩,by simp⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; apply Subtype.ext; simp

def finiteLeft (B : Finset G) (g : G) : Equiv.Perm B := by
  classical
  exact (partialLeft B g).extendSubtype

lemma finiteLeft_apply (B : Finset G) (g : G) (x : B) (hx : g*(x:G) ∈ B) :
    (finiteLeft B g x : G)=g*(x:G) := by
  classical
  rw [finiteLeft,Equiv.extendSubtype_apply_of_mem _ x hx]
  rfl

lemma finiteLeft_inv_apply (B : Finset G) (g : G) (x : B) (hx : g⁻¹*(x:G) ∈ B) :
    ((finiteLeft B g)⁻¹ x : G)=g⁻¹*(x:G) := by
  let y : B := ⟨g⁻¹*(x:G),hx⟩
  have hy : finiteLeft B g y=x := by
    apply Subtype.ext
    rw [finiteLeft_apply _ _ y (by simp [y])]
    simp [y]
  calc
    ((finiteLeft B g)⁻¹ x : G) = ((finiteLeft B g)⁻¹ (finiteLeft B g y) : G) := by rw [hy]
    _ = (y:G) := by simp
    _ = _ := rfl

universe u
variable {A : Type u}
lemma mk_cons (a : A × Bool) (l : List (A × Bool)) :
    FreeGroup.mk (a::l)=(if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹)*FreeGroup.mk l := by
  have hh := FreeGroup.lift_mk (f:=FreeGroup.of) (L:=a::l)
  simp only [FreeGroup.lift_of_apply,List.map_cons,List.prod_cons,
    ←FreeGroup.lift_mk,FreeGroup.lift_of_apply] at hh
  cases ha : a.2 <;> simpa only [ha,Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true] using hh

lemma finiteLeft_word (B : Finset (FreeGroup A)) (h1 : (1:FreeGroup A) ∈ B)
    (l : List (A × Bool)) (hl : ∀ k ∈ l.tails, FreeGroup.mk k ∈ B) :
    (FreeGroup.lift (fun a => finiteLeft B (FreeGroup.of a)) (FreeGroup.mk l) ⟨1,h1⟩ : FreeGroup A)=FreeGroup.mk l := by
  induction l with
  | nil => simp only [←FreeGroup.one_eq_mk]; rfl
  | cons a l ih =>
    have hl' : ∀ k ∈ l.tails, FreeGroup.mk k ∈ B := by
      intro k hk; exact hl k (by simp only [List.tails_cons,List.mem_cons]; exact Or.inr hk)
    have hm : FreeGroup.mk (a::l) ∈ B := hl _ (by simp)
    rw [mk_cons,_root_.map_mul,Equiv.Perm.mul_apply]
    split_ifs with ha
    · rw [FreeGroup.lift_apply_of]
      rw [finiteLeft_apply]
      · rw [ih hl']
      · simpa only [ih hl',mk_cons,ite_eq_left ha] using hm
    · rw [_root_.map_inv,FreeGroup.lift_apply_of]
      rw [finiteLeft_inv_apply]
      · rw [ih hl']
      · simpa only [ih hl',mk_cons,ite_eq_right ha] using hm

theorem exists_finite_separation (S : Finset (FreeGroup A)) :
    ∃ (H : Type u) (_ : Group H) (_ : Fintype H) (π : FreeGroup A →* H),
      ∀ g ∈ S, g ≠ 1 → π g ≠ 1 := by
  classical
  let B : Finset (FreeGroup A) := insert 1 (S.biUnion (fun g => g.toWord.tails.toFinset.image FreeGroup.mk))
  have h1 : (1:FreeGroup A) ∈ B := Finset.mem_insert_self _ _
  let π : FreeGroup A →* Equiv.Perm B := FreeGroup.lift (fun a => finiteLeft B (FreeGroup.of a))
  refine ⟨Equiv.Perm B,inferInstance,inferInstance,π,?_⟩
  intro g hg hg1 hπ
  have hh := finiteLeft_word B h1 g.toWord (by
    intro k hk
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨g,hg,Finset.mem_image.mpr ⟨k,List.mem_toFinset.mpr hk,rfl⟩⟩)
  rw [FreeGroup.mk_toWord] at hh
  change (π g ⟨1,h1⟩ : FreeGroup A)=g at hh
  rw [hπ] at hh
  exact hg1 hh.symm
end PopaFinite

end

end OAI
