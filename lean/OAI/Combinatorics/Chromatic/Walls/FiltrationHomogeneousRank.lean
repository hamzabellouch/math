import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
variable (F G : Submodule ℚ M) (p : Module.End ℚ M)
variable (hp : ∀ x,p (p x)=p x)
variable (hF : ∀ x∈F,p x∈F) (hG : ∀ x∈G,p x∈G)

noncomputable def homogeneousMk : F.comap (LinearMap.range p).subtype →ₗ[ℚ] Grade F G :=
  (mk F G).comp
    ({ toFun := fun x=>⟨x.val.val,x.property⟩
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : F.comap (LinearMap.range p).subtype →ₗ[ℚ] F)

include hp in
lemma homogeneousMk_range :
    LinearMap.range (homogeneousMk F G p)=LinearMap.range (map F G F G p hF hG) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    refine ⟨mk F G ⟨x.val.val,x.property⟩,?_⟩
    change Submodule.Quotient.mk (⟨p x.val.val,hF _ x.property⟩ : F)=Submodule.Quotient.mk (⟨x.val.val,x.property⟩ : F)
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    obtain ⟨y,hy⟩:=x.val.property
    exact (congrArg p hy).symm.trans ((hp y).trans hy)
  · rintro _ ⟨x,rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H x => exact ⟨⟨⟨p x.val,⟨x.val,rfl⟩⟩,hF _ x.property⟩,rfl⟩

include hp in
lemma homogeneousMap_finite [Module.Finite ℚ (LinearMap.range p)] :
    Module.Finite ℚ (LinearMap.range (map F G F G p hF hG)) := by
  rw [←homogeneousMk_range F G p hp hF hG]
  exact Module.Finite.range (homogeneousMk F G p)

lemma homogeneousMk_ker :
    LinearMap.ker (homogeneousMk F G p)=
      next (F.comap (LinearMap.range p).subtype) (G.comap (LinearMap.range p).subtype) := by
  ext x
  change Submodule.Quotient.mk (⟨x.val.val,x.property⟩ : F)=0 ↔ _
  exact Submodule.Quotient.mk_eq_zero (next F G)

include hp hF hG in
lemma homogeneousGrade_rank [Module.Finite ℚ (LinearMap.range p)] (hGF : G≤F) :
    Module.finrank ℚ (LinearMap.range (map F G F G p hF hG))+
      Module.finrank ℚ (G.comap (LinearMap.range p).subtype)=
      Module.finrank ℚ (F.comap (LinearMap.range p).subtype) := by
  have H := (homogeneousMk F G p).finrank_range_add_finrank_ker
  rw [homogeneousMk_range F G p hp hF hG,homogeneousMk_ker] at H
  have E := (Submodule.comapSubtypeEquivOfLe
    (Submodule.comap_mono hGF : G.comap (LinearMap.range p).subtype≤F.comap (LinearMap.range p).subtype)).finrank_eq
  exact E ▸ H

include hp in
lemma homogeneousGrade_rank_eq [Module.Finite ℚ (LinearMap.range p)] (hGF : G≤F) :
    Module.finrank ℚ (LinearMap.range (map F G F G p hF hG))=
      Module.finrank ℚ (Grade (F.comap (LinearMap.range p).subtype)
        (G.comap (LinearMap.range p).subtype)) := by
  have H := homogeneousGrade_rank F G p hp hF hG hGF
  have H' := (next (F.comap (LinearMap.range p).subtype)
    (G.comap (LinearMap.range p).subtype)).finrank_quotient_add_finrank
  have E := (Submodule.comapSubtypeEquivOfLe
    (Submodule.comap_mono hGF : G.comap (LinearMap.range p).subtype≤F.comap (LinearMap.range p).subtype)).finrank_eq
  have H'' : Module.finrank ℚ (Grade (F.comap (LinearMap.range p).subtype)
      (G.comap (LinearMap.range p).subtype))+
      Module.finrank ℚ (G.comap (LinearMap.range p).subtype)=
      Module.finrank ℚ (F.comap (LinearMap.range p).subtype) := E ▸ H'
  omega
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity
variable {M : Type*} [AddCommGroup M] [Module ℚ M] [Module.Finite ℚ M]
variable (F : ℤ → Submodule ℚ M) (hF : Antitone F)

include hF
lemma finiteFiltration_rank_step (w : ℤ) :
    Module.finrank ℚ (LinearFiltration.Grade (F w) (F (w+1)))+Module.finrank ℚ (F (w+1))=
      Module.finrank ℚ (F w) := by
  have H := (LinearFiltration.next (F w) (F (w+1))).finrank_quotient_add_finrank
  have E := (Submodule.comapSubtypeEquivOfLe (hF (show w≤w+1 by omega))).finrank_eq
  exact E ▸ H

lemma finiteFiltration_rank_sum (L : ℤ) (n : ℕ) :
    (∑ j∈Finset.range n,Module.finrank ℚ (LinearFiltration.Grade (F (L+j)) (F (L+j+1))))+
      Module.finrank ℚ (F (L+n))=Module.finrank ℚ (F L) := by
  induction n with
  | zero =>
    change 0+Module.finrank ℚ (F (L+0))=Module.finrank ℚ (F L)
    rw [add_zero,zero_add]
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one,←add_assoc,add_assoc]
    rw [finiteFiltration_rank_step F hF (L+n)]
    exact ih

lemma finiteFiltration_rank_total (L : ℤ) (n : ℕ) (hL : F L=⊤) (hU : F (L+n)=⊥) :
    (∑ j∈Finset.range n,Module.finrank ℚ (LinearFiltration.Grade (F (L+j)) (F (L+j+1))))=
      Module.finrank ℚ M := by
  have H := finiteFiltration_rank_sum F hF L n
  rw [hL,hU,finrank_bot,add_zero,finrank_top] at H
  exact H
end ElementaryPositivity

end

end OAI
