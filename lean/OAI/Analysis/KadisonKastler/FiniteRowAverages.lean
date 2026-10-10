import OAI.Analysis.KadisonKastler.FiniteMatrixBounds
import OAI.Analysis.KadisonKastler.MultiplicationNewtonStep

namespace OAI

/-! Finite row averages, their composition law, and the cochain identity.
These are the algebraic operations of Christensen--Sinclair row averaging.
No existence of an invariant averaging projection is assumed here. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Average a linear map by a finite row. -/
def finiteRightAverage (r : ι → A) : (A →ₗ[ℂ] A) →ₗ[ℂ] (A →ₗ[ℂ] A) where
  toFun F :=
    { toFun := fun x => ∑ i, F (x * r i) * star (r i)
      map_add' := by intros; simp [add_mul, map_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [map_smul, Finset.smul_sum] }
  map_add' := by intros; ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; ext x; simp [Finset.smul_sum]

@[simp] theorem finiteRightAverage_apply (r : ι → A) (F : A →ₗ[ℂ] A) (x : A) :
    finiteRightAverage r F x = ∑ i, F (x * r i) * star (r i) := rfl

/-- A normalized row fixes right module maps. -/
theorem finiteRightAverage_fixed (r : ι → A) (hr : ∑ i, r i * star (r i) = 1)
    (F : A →ₗ[ℂ] A) (hF : ∀ x y, F (x * y) = F x * y) :
    finiteRightAverage r F = F := by
  ext x
  simp only [finiteRightAverage_apply, hF, mul_assoc, ← Finset.mul_sum, hr, mul_one]

/-- Composition corresponds to the product row. -/
theorem finiteRightAverage_comp (r : ι → A) (s : κ → A) (F : A →ₗ[ℂ] A) :
    finiteRightAverage r (finiteRightAverage s F) =
      finiteRightAverage (fun ij : ι × κ => r ij.1 * s ij.2) F := by
  ext x
  simp only [finiteRightAverage_apply, Finset.sum_mul, Fintype.sum_prod_type,
    star_mul, mul_assoc]

/-- The product row is normalized whenever its factors are. -/
theorem finiteRow_product_normalized (r : ι → A) (s : κ → A)
    (hr : ∑ i, r i * star (r i) = 1) (hs : ∑ j, s j * star (s j) = 1) :
    ∑ ij : ι × κ, (r ij.1 * s ij.2) * star (r ij.1 * s ij.2) = 1 := by
  simp only [Fintype.sum_prod_type, star_mul]
  calc
    _ = ∑ i, r i * (∑ j, s j * star (s j)) * star (r i) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = 1 := by simp only [hs, mul_one, hr]

/-- Finite averaging commutes with precomposition by left multiplication. -/
theorem finiteRightAverage_left_input (r : ι → A) (F : A →ₗ[ℂ] A) (a x : A) :
    (∑ i, F (a * (x * r i)) * star (r i)) = finiteRightAverage r F (a * x) := by
  simp only [finiteRightAverage_apply, mul_assoc]

/-- The linear cochain obtained by averaging the last argument. -/
def finiteCochainAverage (r : ι → A) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) : A →ₗ[ℂ] A where
  toFun x := ∑ i, f x (r i) * star (r i)
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]

@[simp] theorem finiteCochainAverage_apply (r : ι → A)
    (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x : A) :
    finiteCochainAverage r f x = ∑ i, f x (r i) * star (r i) := rfl

/-- The scalar Hochschild differential of a bilinear cochain. -/
def cochainDifferential (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y z : A) : A :=
  x * f y z - f (x * y) z + f x (y * z) - f x y * z

/-- The cochain residual is exactly a module defect minus the averaged
Hochschild differential. The module defect vanishes at an invariant limit. -/
theorem finiteCochainAverage_residual (r : ι → A)
    (hr : ∑ i, r i * star (r i) = 1) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    f x y - linearCoboundary (finiteCochainAverage r f) x y =
      finiteRightAverage r (f x) y - finiteCochainAverage r f x * y -
        ∑ i, cochainDifferential f x y (r i) * star (r i) := by
  simp only [linearCoboundary_apply, finiteCochainAverage_apply, finiteRightAverage_apply,
    cochainDifferential, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hr, mul_one]
  abel

end

end KadisonKastler

end OAI
