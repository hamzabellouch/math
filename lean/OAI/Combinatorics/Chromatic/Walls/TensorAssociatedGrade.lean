import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LinearFiltrationBilinear

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open LinearDetection
open scoped TensorProduct DirectSum
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

noncomputable def gradeProjection (F : ℤ → Submodule ℚ M) (u : ℤ) :
    M →ₗ[ℚ] Grade (F u) (F (u+1)) :=
  (mk _ _).comp ((retract (F u)).codRestrict _ (retract_mem _))

lemma gradeProjection_mem (F : ℤ → Submodule ℚ M) (u : ℤ) (x : F u) :
    gradeProjection F u x.val=mk (F u) (F (u+1)) x := by
  apply congrArg (mk _ _)
  apply Subtype.ext
  exact retract_eq_self _ x.property

lemma gradeProjection_zero (F : ℤ → Submodule ℚ M) (hF : Antitone F) (u v : ℤ)
    (huv : u<v) (x : M) (hx : x∈F v) : gradeProjection F u x=0 := by
  have hx' : x∈F u:=hF (le_of_lt huv) hx
  rw [gradeProjection_mem F u ⟨x,hx'⟩]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hF (by omega) hx)

abbrev TensorGrade (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N) (W : ℤ) :=
  Grade (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1))

noncomputable def tensorGradeInclusion (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (u v : ℤ) : Grade (F u) (F (u+1)) ⊗[ℚ] Grade (G v) (G (v+1)) →ₗ[ℚ]
      TensorGrade F G (u+v) :=
  TensorProduct.lift (bilinear (F u) (F (u+1)) (G v) (G (v+1))
    (additiveTensorFiltration F G (u+v)) (additiveTensorFiltration F G (u+v+1))
    (TensorProduct.mk ℚ M N)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (le_refl _) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy))

lemma tensorGradeInclusion_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (u v : ℤ) (x : F u) (y : G v) :
    tensorGradeInclusion F G u v (mk _ _ x⊗ₜ[ℚ]mk _ _ y)=
      mk _ _ ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration F G (le_refl _) x.property y.property⟩ := rfl

lemma tensorProjection_kills (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (u v : ℤ) :
    additiveTensorFiltration F G (u+v+1)≤
      LinearMap.ker (TensorProduct.map (gradeProjection F u) (gradeProjection G v)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,b,x,y,hab,hx,hy,rfl⟩
  change TensorProduct.map _ _ (x⊗ₜ[ℚ]y)=0
  rw [TensorProduct.map_tmul]
  by_cases ha : u<a
  · rw [gradeProjection_zero F hF u a ha x hx,TensorProduct.zero_tmul]
  · have hb : v<b:=by omega
    rw [gradeProjection_zero G hG v b hb y hy,TensorProduct.tmul_zero]

noncomputable def tensorGradeProjection (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (u v : ℤ) :
    TensorGrade F G (u+v) →ₗ[ℚ] Grade (F u) (F (u+1)) ⊗[ℚ] Grade (G v) (G (v+1)) :=
  (next _ _).liftQ ((TensorProduct.map (gradeProjection F u) (gradeProjection G v)).comp
    (additiveTensorFiltration F G (u+v)).subtype) (by
      intro x hx
      exact tensorProjection_kills F G hF hG u v hx)

lemma tensorGradeProjection_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (u v : ℤ) (x : additiveTensorFiltration F G (u+v)) :
    tensorGradeProjection F G hF hG u v (mk _ _ x)=
      TensorProduct.map (gradeProjection F u) (gradeProjection G v) x.val := rfl

lemma tensorGradeProjection_inclusion_self (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (u v : ℤ) :
    (tensorGradeProjection F G hF hG u v).comp (tensorGradeInclusion F G u v)=LinearMap.id := by
  ext x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change tensorGradeProjection F G hF hG u v
        (tensorGradeInclusion F G u v (mk _ _ x⊗ₜ[ℚ]mk _ _ y))=mk _ _ x⊗ₜ[ℚ]mk _ _ y
      rw [tensorGradeInclusion_mk,tensorGradeProjection_mk,TensorProduct.map_tmul,
        gradeProjection_mem,gradeProjection_mem]

abbrev TensorGradePart (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N) (W u : ℤ) :=
  Grade (F u) (F (u+1)) ⊗[ℚ] Grade (G (W-u)) (G (W-u+1))

noncomputable def tensorGradeInclusionW (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W u : ℤ) : TensorGradePart F G W u →ₗ[ℚ] TensorGrade F G W :=
  TensorProduct.lift (bilinear (F u) (F (u+1)) (G (W-u)) (G (W-u+1))
    (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1))
    (TensorProduct.mk ℚ M N)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy)
    (fun _ hx _ hy=>tmul_mem_additiveTensorFiltration F G (by omega) hx hy))

lemma tensorGradeInclusionW_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W u : ℤ) (x : F u) (y : G (W-u)) :
    tensorGradeInclusionW F G W u (mk _ _ x⊗ₜ[ℚ]mk _ _ y)=
      mk _ _ ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration F G (by omega) x.property y.property⟩ := rfl

noncomputable def tensorGradeProjectionW (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    TensorGrade F G W →ₗ[ℚ] TensorGradePart F G W u :=
  (next _ _).liftQ ((TensorProduct.map (gradeProjection F u) (gradeProjection G (W-u))).comp
    (additiveTensorFiltration F G W).subtype) (by
      intro x hx
      apply tensorProjection_kills F G hF hG u (W-u)
      change x.val∈additiveTensorFiltration F G (W+1) at hx
      change x.val∈additiveTensorFiltration F G (u+(W-u)+1)
      simpa only [add_sub_cancel] using hx)

lemma tensorGradeProjectionW_mk (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) (x : additiveTensorFiltration F G W) :
    tensorGradeProjectionW F G hF hG W u (mk _ _ x)=
      TensorProduct.map (gradeProjection F u) (gradeProjection G (W-u)) x.val := rfl

lemma tensorGradeProjectionW_inclusion_self (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeInclusionW F G W u)=LinearMap.id := by
  ext x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change tensorGradeProjectionW F G hF hG W u
        (tensorGradeInclusionW F G W u (mk _ _ x⊗ₜ[ℚ]mk _ _ y))=mk _ _ x⊗ₜ[ℚ]mk _ _ y
      rw [tensorGradeInclusionW_mk,tensorGradeProjectionW_mk,TensorProduct.map_tmul,
        gradeProjection_mem,gradeProjection_mem]

lemma tensorGradeProjectionW_inclusion_ne (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u j : ℤ) (huj : u≠j) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeInclusionW F G W j)=0 := by
  ext x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change tensorGradeProjectionW F G hF hG W u
        (tensorGradeInclusionW F G W j (mk _ _ x⊗ₜ[ℚ]mk _ _ y))=0
      rw [tensorGradeInclusionW_mk,tensorGradeProjectionW_mk,TensorProduct.map_tmul]
      by_cases h : u<j
      · rw [gradeProjection_zero F hF u j h x.val x.property,TensorProduct.zero_tmul]
      · rw [gradeProjection_zero G hG (W-u) (W-j) (by omega) y.val y.property,TensorProduct.tmul_zero]

noncomputable def tensorGradeSum (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : (⨁ u : ℤ,TensorGradePart F G W u) →ₗ[ℚ] TensorGrade F G W :=
  DirectSum.toModule ℚ ℤ _ (tensorGradeInclusionW F G W)

lemma tensorGradeProjectionW_sum (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W u : ℤ) :
    (tensorGradeProjectionW F G hF hG W u).comp (tensorGradeSum F G W)=
      DirectSum.component ℚ ℤ (TensorGradePart F G W) u := by
  apply DirectSum.linearMap_ext
  intro j
  by_cases h : j=u
  · subst j
    apply LinearMap.ext
    intro x
    change tensorGradeProjectionW F G hF hG W u
      (tensorGradeSum F G W (DirectSum.lof ℚ ℤ _ u x))=_
    rw [tensorGradeSum,DirectSum.toModule_lof,LinearMap.comp_apply,DirectSum.component.lof_self]
    exact LinearMap.congr_fun (tensorGradeProjectionW_inclusion_self F G hF hG W u) x
  · apply LinearMap.ext
    intro x
    change tensorGradeProjectionW F G hF hG W u
      (tensorGradeSum F G W (DirectSum.lof ℚ ℤ _ j x))=_
    rw [tensorGradeSum,DirectSum.toModule_lof,LinearMap.comp_apply,DirectSum.component.of,dite_eq_right h]
    exact LinearMap.congr_fun (tensorGradeProjectionW_inclusion_ne F G hF hG W u j (Ne.symm h)) x

lemma tensorGradeSum_injective (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) : Function.Injective (tensorGradeSum F G W) := by
  intro x y hxy
  apply DirectSum.ext_component ℚ
  intro u
  rw [←tensorGradeProjectionW_sum F G hF hG W u]
  exact congrArg (tensorGradeProjectionW F G hF hG W u) hxy

lemma tensorGradeSum_surjective (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : Function.Surjective (tensorGradeSum F G W) := by
  rw [←LinearMap.range_eq_top,eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change mk _ _ x∈LinearMap.range (tensorGradeSum F G W)
    have h : ∀ (z : M⊗[ℚ]N) (hz : z∈additiveTensorFiltration F G W),
        mk _ _ ⟨z,hz⟩∈LinearMap.range (tensorGradeSum F G W) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        rcases hz with ⟨u,v,x,y,hw,hx,hy,rfl⟩
        by_cases he : W=u+v
        · have hv : v=W-u:=by omega
          subst v
          refine ⟨DirectSum.lof ℚ ℤ _ u (mk _ _ ⟨x,hx⟩⊗ₜ[ℚ]mk _ _ ⟨y,hy⟩),?_⟩
          rw [tensorGradeSum,DirectSum.toModule_lof,tensorGradeInclusionW_mk]
        · have hz' : x⊗ₜ[ℚ]y∈additiveTensorFiltration F G (W+1):=
            tmul_mem_additiveTensorFiltration F G (by omega) hx hy
          have he : (mk _ _ ⟨x⊗ₜ[ℚ]y,tmul_mem_additiveTensorFiltration F G hw hx hy⟩ : TensorGrade F G W)=0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hz'
          rw [he]
          exact Submodule.zero_mem _
      | zero => exact Submodule.zero_mem _
      | add x y hx hy hix hiy =>
        exact (LinearMap.range (tensorGradeSum F G W)).add_mem hix hiy
      | smul r x hx hix => exact (LinearMap.range (tensorGradeSum F G W)).smul_mem r hix
    exact h x.val x.property

noncomputable def tensorGradeEquiv (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G) (W : ℤ) :
    (⨁ u : ℤ,TensorGradePart F G W u) ≃ₗ[ℚ] TensorGrade F G W :=
  LinearEquiv.ofBijective (tensorGradeSum F G W)
    ⟨tensorGradeSum_injective F G hF hG W,tensorGradeSum_surjective F G W⟩

end ElementaryPositivity.LinearFiltration

end

end OAI
