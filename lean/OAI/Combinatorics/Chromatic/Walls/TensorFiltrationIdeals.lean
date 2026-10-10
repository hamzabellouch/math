import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RationalTensorDetection

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

lemma additiveTensorFiltration_mul_mem (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (hF : ∀ w x y,x∈F w → x*y∈F w) (hG : ∀ w x y,x∈G w → x*y∈G w)
    (W : ℤ) (x y : A⊗[K]B) (hx : x∈additiveTensorFiltration F G W) :
    x*y∈additiveTensorFiltration F G W := by
  have hgen {u v : ℤ} {a : A} {b : B} (hw : W≤u+v) (ha : a∈F u) (hb : b∈G v)
      (z : A⊗[K]B) : (a⊗ₜ[K]b)*z ∈ additiveTensorFiltration F G W := by
    induction z using TensorProduct.inductionOn with
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_additiveTensorFiltration F G hw (hF u a c ha) (hG v b d hb)
    | add z t hz ht =>
      rw [mul_add]
      exact (additiveTensorFiltration F G W).add_mem hz ht
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u,v,a,b,hw,ha,hb,rfl⟩:=hz
    exact hgen hw ha hb y
  | zero => simp only [zero_mul]; exact (additiveTensorFiltration F G W).zero_mem
  | add z t _ _ hz ht =>
    rw [add_mul]
    exact (additiveTensorFiltration F G W).add_mem hz ht
  | smul c z _ hz =>
    rw [smul_mul_assoc]
    exact (additiveTensorFiltration F G W).smul_mem c hz

noncomputable def additiveTensorFiltrationIdeal (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (hF : ∀ w x y,x∈F w → x*y∈F w) (hG : ∀ w x y,x∈G w → x*y∈G w)
    (W : ℤ) : Ideal (A⊗[K]B) where
  __ := (additiveTensorFiltration F G W).toAddSubmonoid
  smul_mem' c x hx := by
    change c*x∈additiveTensorFiltration F G W
    rw [mul_comm]
    exact additiveTensorFiltration_mul_mem F G hF hG W x c hx
end ElementaryPositivity.LinearDetection

end

end OAI
