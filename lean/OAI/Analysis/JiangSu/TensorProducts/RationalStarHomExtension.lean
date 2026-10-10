import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI


noncomputable section
namespace RationalStarExtension
open scoped CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
local instance rationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
variable (S : StarSubalgebra ℚ A) (hS : Dense (S : Set A))
variable (f : S →⋆ₐ[ℚ] B) (hf : ∀ x,‖f x‖≤‖(x:A)‖)

 def linear : A →L[ℚ] B := f.toAlgHom.toLinearMap.extendOfNorm S.subtype.toAlgHom.toLinearMap

include hS hf in
 theorem linear_eq (x : S) : linear S f (x:A)=f x := by
   exact LinearMap.extendOfNorm_eq
     (f := f.toAlgHom.toLinearMap) (e := S.subtype.toAlgHom.toLinearMap)
     hS.denseRange_val ⟨1, fun element => by
       change ‖f element‖ ≤ (1 : ℝ) * ‖(element : A)‖
       simpa only [one_mul] using hf element⟩ x

include hS hf in
 theorem linear_one : linear S f 1=1 := by
   have h := linear_eq S hS f hf (1:S)
   change linear S f 1=f 1 at h
   simpa only [map_one] using h

include hS hf in
 theorem linear_mul (x y : A) : linear S f (x*y)=linear S f x*linear S f y := by
   refine hS.denseRange_val.induction_on₂ ?_ ?_ x y
   · exact isClosed_eq (by fun_prop) (by fun_prop)
   · intro a b
     change linear S f ((a*b:S):A)=_
     rw [linear_eq _ hS _ hf,map_mul,linear_eq _ hS _ hf,linear_eq _ hS _ hf]

include hS hf in
 theorem linear_star (x : A) : linear S f (star x)=star (linear S f x) := by
   refine hS.denseRange_val.induction_on x ?_ ?_
   · exact isClosed_eq (by fun_prop) (by fun_prop)
   · intro a
     change linear S f ((star a:S):A)=_
     rw [linear_eq _ hS _ hf,map_star,linear_eq _ hS _ hf]

include hS hf in
 theorem linear_real (r : ℝ) : linear S f (algebraMap ℂ A r)=algebraMap ℂ B r := by
   refine Rat.denseRange_cast.induction_on r ?_ ?_
   · exact isClosed_eq ((linear S f).continuous.comp ((algebraMapCLM ℂ A).continuous.comp Complex.continuous_ofReal))
       ((algebraMapCLM ℂ B).continuous.comp Complex.continuous_ofReal)
   · intro q
     have he := (linear S f).map_smul q (1:A)
     rw [linear_one _ hS _ hf] at he
     have hA : (q:ℚ) • (1:A) = algebraMap ℂ A (q:ℂ) := by
       rw [Algebra.smul_def, mul_one]
       rfl
     have hB : (q:ℚ) • (1:B) = algebraMap ℂ B (q:ℂ) := by
       rw [Algebra.smul_def, mul_one]
       rfl
     rw [hA,hB] at he
     simpa only [Complex.ofReal_ratCast] using he

variable (hI : algebraMap ℂ A Complex.I∈S)
variable (hfI : f ⟨algebraMap ℂ A Complex.I,hI⟩=algebraMap ℂ B Complex.I)

include hS hf hfI in
 theorem linear_complex (z : ℂ) : linear S f (algebraMap ℂ A z)=algebraMap ℂ B z := by
   have hi : linear S f (algebraMap ℂ A Complex.I)=algebraMap ℂ B Complex.I :=
     (linear_eq S hS f hf ⟨_,hI⟩).trans hfI
   conv_lhs => rw [←Complex.re_add_im z]
   rw [map_add,map_mul,map_add,linear_mul _ hS _ hf,linear_real _ hS _ hf,
     linear_real _ hS _ hf,hi,←map_mul,←map_add,Complex.re_add_im]

 def extension : A →⋆ₐ[ℂ] B where
   toFun := linear S f
   map_zero' := map_zero _
   map_one' := linear_one S hS f hf
   map_add' := map_add _
   map_mul' := linear_mul S hS f hf
   map_star' := linear_star S hS f hf
   commutes' := linear_complex S hS f hf hI hfI

 theorem extension_eq (x : S) : extension S hS f hf hI hfI (x:A)=f x := linear_eq S hS f hf x

end RationalStarExtension

end

end OAI
