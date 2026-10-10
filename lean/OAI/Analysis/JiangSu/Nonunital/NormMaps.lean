import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerToTracial

namespace OAI

section

noncomputable section
namespace NonunitalNormMaps
open Filter Topology NormUltra NormUltra.QuotientAlgebra NonunitalGamma
open scoped CStarAlgebra ENNReal

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def boundedMap (f : A →⋆ₙₐ[ℂ] B) : BoundedFamilies (fun _ : ℕ => A) →⋆ₙₐ[ℂ]
    BoundedFamilies (fun _ : ℕ => B) where
  toFun x := ⟨fun n => f (x n),memℓp_infty ⟨‖x‖,by
    rintro _ ⟨n,rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le f (x n)).trans (BoundedFamilies.norm_coordinate_le x n)⟩⟩
  map_zero' := by ext n; exact map_zero f
  map_add' x y := by ext n; exact map_add f (x n) (y n)
  map_mul' x y := by ext n; exact map_mul f (x n) (y n)
  map_star' x := by ext n; exact map_star f (x n)
  map_smul' c x := by ext n; exact map_smul f c (x n)

@[simp] lemma boundedMap_apply (hom : A →⋆ₙₐ[ℂ] B)
    (family : BoundedFamilies (fun _ : ℕ => A)) (index : ℕ) :
    boundedMap hom family index = hom (family index) := rfl

@[simp] lemma boundedMap_constant (f : A →⋆ₙₐ[ℂ] B) (a : A) :
    boundedMap f (boundedConstant (A := A) a)=boundedConstant (A := B) (f a) := by ext n; rfl

def quotientMap (U : Ultrafilter ℕ) (f : A →⋆ₙₐ[ℂ] B) :
    QuotientAlgebra (fun _ : ℕ => A) U →⋆ₙₐ[ℂ] QuotientAlgebra (fun _ : ℕ => B) U where
  toFun := Quotient.lift (fun x => mk U (boundedMap f x)) (by
    intro x y hxy
    apply (mk_eq_mk_iff _ _).mpr
    change (BoundedFamilies.vanishing (A := fun _ : ℕ => A) U).quotientRel x y at hxy
    rw [Submodule.quotientRel_def] at hxy
    change Tendsto (fun n => ‖f (x n)-f (y n)‖) (U : Filter ℕ) (𝓝 0)
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hxy
    rw [←map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le f _)
  map_zero' := by change mk U (boundedMap f 0)=0; rw [map_zero,mk_zero]
  map_add' x y := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    change mk U (boundedMap f (x+y))=mk U (boundedMap f x)+mk U (boundedMap f y)
    rw [map_add,mk_add]
  map_mul' x y := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    change mk U (boundedMap f (x*y))=mk U (boundedMap f x)*mk U (boundedMap f y)
    rw [map_mul,mk_mul]
  map_smul' c x := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    change mk U (boundedMap f (c • x))=c • mk U (boundedMap f x)
    rw [map_smul,mk_smul]
  map_star' x := by
    obtain ⟨x,rfl⟩ := mk_surjective x
    change mk U (boundedMap f (star x))=star (mk U (boundedMap f x))
    rw [map_star,mk_star]

@[simp] lemma quotientMap_mk (U : Ultrafilter ℕ) (f : A →⋆ₙₐ[ℂ] B)
    (x : BoundedFamilies (fun _ : ℕ => A)) : quotientMap U f (mk U x)=mk U (boundedMap f x) := rfl

@[simp] lemma quotientMap_inclusion (U : Ultrafilter ℕ) (f : A →⋆ₙₐ[ℂ] B) (a : A) :
    quotientMap U f (normInclusion U a)=normInclusion U (f a) := by
  change mk U (boundedMap f (boundedConstant (A := A) a))=mk U (boundedConstant (A := B) (f a))
  rw [boundedMap_constant]

lemma quotientMap_commute (U : Ultrafilter ℕ) (f : A →⋆ₙₐ[ℂ] B) (a : A)
    (x : QuotientAlgebra (fun _ : ℕ => A) U) (h : Commute x (normInclusion U a)) :
    Commute (quotientMap U f x) (normInclusion U (f a)) := by
  simpa only [quotientMap_inclusion] using h.map (quotientMap U f)

end NonunitalNormMaps

end
end

end OAI
