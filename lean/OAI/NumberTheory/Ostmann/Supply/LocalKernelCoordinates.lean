import OAI.NumberTheory.Ostmann.Supply.BivariateTruncation
import OAI.NumberTheory.Ostmann.Supply.LocalBlockConstant
import OAI.NumberTheory.Ostmann.Supply.LocalKernelOperator

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "H" => EuclideanSpace ℂ ι

def localPoint (S : Finset ι) (x : ι) : LocalCoordinates S :=
  WithLp.toLp 2 (1,(centeredSpace S).orthogonalProjectionOnto (EuclideanSpace.single x (1:ℂ)))

@[simp] theorem localPoint_fst (S : Finset ι) (x : ι) : (localPoint S x).fst = 1 := rfl
@[simp] theorem localPoint_snd (S : Finset ι) (x : ι) :
    ((localPoint S x).snd:H) = centeredProjection S (EuclideanSpace.single x (1:ℂ)) := rfl

theorem coordinateLift_point (S : Finset ι) (x : ι) (hx : x∈S) :
    coordinateLift S (localPoint S x) = EuclideanSpace.single x (1:ℂ) := by
  rw [coordinateLift_apply,localPoint_fst,localPoint_snd,one_smul,centeredProjection_single S x hx]
  abel

theorem localPoint_extract_pairing (S : Finset ι) (x : ι) (hx : x∈S) (f : H) :
    inner ℂ (localPoint S x) (coordinateExtract S f) = f x := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (1:ℂ) (inner ℂ (uniformVector S) f) +
    inner ℂ ((centeredSpace S).orthogonalProjectionOnto (EuclideanSpace.single x (1:ℂ)))
      ((centeredSpace S).orthogonalProjectionOnto f) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change inner ℂ (1:ℂ) (inner ℂ (uniformVector S) f) +
    inner ℂ (centeredProjection S (EuclideanSpace.single x (1:ℂ))) f = _
  rw [centeredProjection_single S x hx,inner_sub_left,EuclideanSpace.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one]
  ring

theorem localPoint_gram (S : Finset ι) (x y : ι) :
    inner ℂ (localPoint S x) (localPoint S y) = 1+
      inner ℂ (centeredProjection S (EuclideanSpace.single x (1:ℂ)))
        (centeredProjection S (EuclideanSpace.single y (1:ℂ))) := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (1:ℂ) (1:ℂ) + _ = _
  simp only [RCLike.inner_apply,map_one,mul_one]
  rfl

theorem localBlock_point_pairing (S T : Finset ι) (K : H →L[ℂ] H)
    (x y : ι) (hx : x∈S) (hy : y∈T) :
    inner ℂ (localPoint S x) (localBlock S T K (localPoint T y)) =
      K (EuclideanSpace.single y (1:ℂ)) x := by
  unfold localBlock
  simp only [ContinuousLinearMap.comp_apply,coordinateLift_point T y hy]
  exact localPoint_extract_pairing S x hx _

section Cyclic
variable {p : ℕ} [NeZero p]

theorem localKernelBlock_point_pairing (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ)
    (x y : ZMod p) (hx : x∈S) (hy : y∈Sᶜ) :
    inner ℂ (localPoint S x) (localKernelBlock S t u v (localPoint Sᶜ y)) =
      (1+u*(localKernel S t (x-y):ℂ))*(1+v*(localKernel S t (x-y):ℂ)) := by
  rw [localKernelBlock,localBlock_point_pairing S Sᶜ _ x y hx hy]
  simp [localKernelOperator,convolutionOperator_matrix,PiLp.single_apply]

end Cyclic
end Ostmann.Supply

end

end OAI
