import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.UnitalTraceKernelSigma

namespace OAI

section

noncomputable section
namespace NormUltra
open Filter Topology DirectComparison
open scoped CStarAlgebra ENNReal

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

 def boundedMap (f : A →⋆ₐ[ℂ] B) : BoundedFamilies (fun _ : ℕ => A) →⋆ₙₐ[ℂ]
    BoundedFamilies (fun _ : ℕ => B) where
  toFun x := ⟨fun n => f (x n),memℓp_infty ⟨‖x‖,by
    rintro _ ⟨n,rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le f (x n)).trans (BoundedFamilies.norm_coordinate_le x n)⟩⟩
  map_zero' := by ext n; exact map_zero f
  map_add' x y := by ext n; exact map_add f (x n) (y n)
  map_mul' x y := by ext n; exact map_mul f (x n) (y n)
  map_star' x := by ext n; exact map_star f (x n)
  map_smul' c x := by ext n; exact map_smul f c (x n)

 lemma boundedMap_diagonal (f : A →⋆ₐ[ℂ] B) (a : A) :
    boundedMap f (boundedDiagonal a)=boundedDiagonal (f a) := by ext n; rfl

namespace QuotientAlgebra
 def mapNonUnital (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) :
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

 @[simp] lemma mapNonUnital_mk (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B)
    (x : BoundedFamilies (fun _ : ℕ => A)) : mapNonUnital U f (mk U x)=mk U (boundedMap f x) := rfl

 lemma mapNonUnital_one (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) : mapNonUnital U f 1=1 := by
  change mk U (boundedMap f (boundedDiagonal (1:A)))=1
  rw [boundedMap_diagonal,map_one,diagonal_one]

 def map (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) :
    QuotientAlgebra (fun _ : ℕ => A) U →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => B) U where
  toFun := mapNonUnital U f
  map_zero' := map_zero _
  map_one' := mapNonUnital_one U f
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,mapNonUnital_one,←Algebra.algebraMap_eq_smul_one]

 @[simp] lemma map_mk (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B)
    (x : BoundedFamilies (fun _ : ℕ => A)) : map U f (mk U x)=mk U (boundedMap f x) := rfl

 def diagonalHom (U : Ultrafilter ℕ) : A →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => A) U where
  toFun a := mk U (boundedDiagonal a)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

 @[simp] lemma map_diagonalHom (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) (a : A) :
    map U f (diagonalHom U a)=diagonalHom U (f a) := by
  change mk U (boundedMap f (boundedDiagonal a))=mk U (boundedDiagonal (f a))
  rw [boundedMap_diagonal]

 theorem map_commute_diagonal (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) (b : B)
    (h : ∀ a,Commute (f a) b) (x : QuotientAlgebra (fun _ : ℕ => A) U) :
    Commute (map U f x) (diagonalHom U b) := by
  obtain ⟨x,rfl⟩ := mk_surjective x
  change mk U (boundedMap f x*boundedDiagonal b)=mk U (boundedDiagonal b*boundedMap f x)
  congr 1
  ext n
  exact (h (x n)).eq

 theorem map_commute (U : Ultrafilter ℕ) (f : A →⋆ₐ[ℂ] B) (a : A)
    (x : QuotientAlgebra (fun _ : ℕ => A) U) (h : Commute x (diagonalHom U a)) :
    Commute (map U f x) (diagonalHom U (f a)) := by
  simpa only [map_diagonalHom] using h.map (map U f)

end QuotientAlgebra
end NormUltra

end
end

end OAI
