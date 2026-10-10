import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalTensorGradeInclusion

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open ElementaryPositivity.LinearDetection
open scoped TensorProduct DirectSum
variable {M N M' N' X Y X' Y' : Type*}
  [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup M'] [Module ℚ M'] [AddCommGroup N'] [Module ℚ N']
  [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
  [AddCommGroup X'] [Module ℚ X'] [AddCommGroup Y'] [Module ℚ Y']

abbrev FGrade (F : ℤ → Submodule ℚ M) (u : ℤ) := Grade (F u) (F (u+1))

noncomputable def gradeMap (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (hf : ∀ w x,x∈F w → f x∈G w) (W : ℤ) :
    FGrade F W →ₗ[ℚ] FGrade G W :=
  map (F W) (F (W+1)) (G W) (G (W+1)) f (hf W) (hf (W+1))

lemma gradeMap_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (hf : ∀ w x,x∈F w → f x∈G w) (W : ℤ) (x : F W) :
    gradeMap F G f hf W (mk _ _ x)=mk _ _ ⟨f x.val,hf W x.val x.property⟩ := rfl

lemma gradeMap_id (F : ℤ → Submodule ℚ M)
    (hf : ∀ w x,x∈F w → LinearMap.id (R:=ℚ) (M:=M) x∈F w) (W : ℤ) :
    gradeMap F F LinearMap.id hf W=LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

noncomputable def tensorGradeMap (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w) (W : ℤ) :
    TensorGrade F G W →ₗ[ℚ] TensorGrade F' G' W :=
  gradeMap (additiveTensorFiltration F G) (additiveTensorFiltration F' G')
    (TensorProduct.map f g) (tensor_map_mem_filtration F G F' G' f g hf hg) W

lemma tensorGradeMap_part (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w) (W u : ℤ)
    (x : FGrade F u) (y : FGrade G (W-u)) :
    tensorGradeMap F G F' G' f g hf hg W (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))=
      tensorGradeInclusionW F' G' W u
        (gradeMap F F' f hf u x⊗ₜ[ℚ]gradeMap G G' g hg (W-u) y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

noncomputable def tensorGradeLift (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y) (W : ℤ) :
    TensorGrade F G W →ₗ[ℚ] X⊗[ℚ]Y :=
  (DirectSum.toModule ℚ ℤ (X⊗[ℚ]Y) (fun u=>TensorProduct.map (f u) (g (W-u)))).comp
    (tensorGradeEquiv F G hF hG W).symm.toLinearMap

lemma tensorGradeLift_part (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y) (W u : ℤ)
    (x : FGrade F u) (y : FGrade G (W-u)) :
    tensorGradeLift F G hF hG f g W (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))=
      f u x⊗ₜ[ℚ]g (W-u) y := by
  change DirectSum.toModule ℚ ℤ _ _ ((tensorGradeEquiv F G hF hG W).symm _) = _
  rw [tensorGradeEquiv_symm_inclusion,DirectSum.toModule_lof,TensorProduct.map_tmul]

lemma tensorGradeLift_map_natural (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (hF : Antitone F) (hG : Antitone G) (hF' : Antitone F') (hG' : Antitone G')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w)
    (l : ∀ u,FGrade F' u →ₗ[ℚ] X) (r : ∀ v,FGrade G' v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F' G' hF' hG' l r W (tensorGradeMap F G F' G' f g hf hg W x)=
      tensorGradeLift F G hF hG (fun u=>(l u).comp (gradeMap F F' f hf u))
        (fun v=>(r v).comp (gradeMap G G' g hg v)) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y => rw [tensorGradeMap_part,tensorGradeLift_part,tensorGradeLift_part]; rfl

lemma tensorGradeLift_comp (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (l : X →ₗ[ℚ] X') (r : Y →ₗ[ℚ] Y') (W : ℤ) (x : TensorGrade F G W) :
    TensorProduct.map l r (tensorGradeLift F G hF hG f g W x)=
      tensorGradeLift F G hF hG (fun u=>l.comp (f u)) (fun v=>r.comp (g v)) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y => rw [tensorGradeLift_part,tensorGradeLift_part,TensorProduct.map_tmul]; rfl

end ElementaryPositivity.LinearFiltration

end
section
namespace ElementaryPositivity.LinearFiltration
open ElementaryPositivity.LinearDetection
open scoped TensorProduct DirectSum
variable {M N P X Y Z : Type*}
  [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup P] [Module ℚ P] [AddCommGroup X] [Module ℚ X]
  [AddCommGroup Y] [Module ℚ Y] [AddCommGroup Z] [Module ℚ Z]

lemma tensorGradeLift_mk_tmul (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W u v : ℤ) (h : u+v=W) (x : F u) (y : G v) :
    tensorGradeLift F G hF hG f g W
      (mk _ _ ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration F G (by omega) x.property y.property⟩)=
      f u (mk _ _ x)⊗ₜ[ℚ]g v (mk _ _ y) := by
  have hv : v=W-u := by omega
  subst v
  exact tensorGradeLift_part F G hF hG f g W u (mk _ _ x) (mk _ _ y)

noncomputable def tensorGradeAssoc (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (H : ℤ → Submodule ℚ P) (W : ℤ) :
    TensorGrade (additiveTensorFiltration F G) H W →ₗ[ℚ]
      TensorGrade F (additiveTensorFiltration G H) W :=
  gradeMap (additiveTensorFiltration (additiveTensorFiltration F G) H)
    (additiveTensorFiltration F (additiveTensorFiltration G H))
    (TensorProduct.assoc ℚ M N P).toLinearMap (assoc_mem_tensorFiltration F G H) W

lemma tensorGradeAssoc_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (H : ℤ → Submodule ℚ P) (W : ℤ)
    (x : additiveTensorFiltration (additiveTensorFiltration F G) H W) :
    tensorGradeAssoc F G H W (mk _ _ x)=
      mk _ _ ⟨TensorProduct.assoc ℚ M N P x.val,assoc_mem_tensorFiltration F G H W x.val x.property⟩ := rfl

lemma tensorGradeLift_assoc (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (H : ℤ → Submodule ℚ P) (hF : Antitone F) (hG : Antitone G) (hH : Antitone H)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (h : ∀ w,FGrade H w →ₗ[ℚ] Z) (W : ℤ)
    (x : TensorGrade (additiveTensorFiltration F G) H W) :
    tensorGradeLift F (additiveTensorFiltration G H) hF (additiveTensorFiltration_antitone G H)
      f (tensorGradeLift G H hG hH g h) W (tensorGradeAssoc F G H W x)=
    TensorProduct.assoc ℚ X Y Z
      (tensorGradeLift (additiveTensorFiltration F G) H (additiveTensorFiltration_antitone F G) hH
        (tensorGradeLift F G hF hG f g) h W x) := by
  induction x using tensorGrade_induction (additiveTensorFiltration F G) H
    (additiveTensorFiltration_antitone F G) hH W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x z =>
    induction x using tensorGrade_induction F G hF hG u with
    | hz => simp only [TensorProduct.zero_tmul,map_zero]
    | ha x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
    | ht r x y =>
      rw [tensorGradeLift_part,tensorGradeLift_part,TensorProduct.assoc_tmul]
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y =>
          induction z using Submodule.Quotient.induction_on with
          | H z =>
            let yz : additiveTensorFiltration G H (W-r) :=
              ⟨y.val⊗ₜ[ℚ]z.val,tmul_mem_additiveTensorFiltration G H (by omega) y.property z.property⟩
            have houter := tensorGradeLift_mk_tmul F (additiveTensorFiltration G H)
              hF (additiveTensorFiltration_antitone G H) f (tensorGradeLift G H hG hH g h)
              W r (W-r) (by omega) x yz
            refine houter.trans ?_
            exact congrArg (fun t=>f r (mk _ _ x)⊗ₜ[ℚ]t)
              (tensorGradeLift_mk_tmul G H hG hH g h (W-r) (u-r) (W-u) (by omega) y z)

end ElementaryPositivity.LinearFiltration

end

end OAI
