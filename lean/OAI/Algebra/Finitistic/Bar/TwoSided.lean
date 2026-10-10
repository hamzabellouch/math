import OAI.Algebra.Finitistic.Bar.Bar

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
namespace FreeBaseChange
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Replace only the free leading algebra coefficient along f. -/
def coefficient : A ⊗[k] V →ₗ[k] D ⊗[k] V :=
  TensorProduct.map f.toLinearMap LinearMap.id

@[simp] theorem coefficient_tmul (a : A) (v : V) :
    coefficient f V (a ⊗ₜ[k] v) = f a ⊗ₜ[k] v := rfl

/-- Coefficient change intertwines the two regular left actions. -/
theorem coefficient_smul (a : A) (z : A ⊗[k] V) :
    coefficient f V (a • z) = f a • coefficient f V z := by
  induction z using TensorProduct.inductionOn with
  | tmul b v => simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => simp_all [smul_add]

/-- Scalar extension of a morphism between explicitly free A-modules. -/
def map (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) : D ⊗[k] V →ₗ[D] D ⊗[k] W :=
  (action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D
      ((coefficient f W).comp ((h.restrictScalars k).comp (TensorProduct.mk k A V 1))))

@[simp] theorem map_tmul (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (d : D) (v : V) :
    map f V W h (d ⊗ₜ[k] v) = d • coefficient f W (h (1 ⊗ₜ[k] v)) := rfl

/-- Extension commutes with the map on arbitrary free tensors, not just generators. -/
theorem map_coefficient (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (z : A ⊗[k] V) :
    map f V W h (coefficient f V z) = coefficient f W (h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    rw [coefficient_tmul, map_tmul]
    have hz : a ⊗ₜ[k] v = a • ((1 : A) ⊗ₜ[k] v) := by
      simp [TensorProduct.smul_tmul']
    rw [hz, h.map_smul, coefficient_smul]
  | add x y hx hy => simp_all

/-- Composition of actual free-module maps is preserved by extension. -/
theorem map_comp (h : A ⊗[k] V →ₗ[A] A ⊗[k] W)
    (g : A ⊗[k] W →ₗ[A] A ⊗[k] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply AlgebraTensorModule.ext
  intro d v
  change d • coefficient f U (g (h (1 ⊗ₜ[k] v))) =
    map f W U g (d • coefficient f W (h (1 ⊗ₜ[k] v)))
  rw [LinearMap.map_smul, map_coefficient]

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply AlgebraTensorModule.ext
  intro d v
  simp only [map_tmul, LinearMap.zero_apply, _root_.map_zero, smul_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d v
  simp [map_tmul, TensorProduct.smul_tmul']

end FreeBaseChange

universe u
variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The two-sided absolute bar differential after changing the free coefficient A to D. -/
def twoSidedDifferential (n : ℕ) :
    D ⊗[k] term k A N (n+1) →ₗ[D] D ⊗[k] term k A N n :=
  FreeBaseChange.map f _ _ (differential k A N (n+1))

/-- The endpoint face minus the remaining absolute bar faces, with their actual signs. -/
theorem twoSidedDifferential_tmul (n : ℕ) (d : D) (z : term k A N (n+1)) :
    twoSidedDifferential k A D N f n (d ⊗ₜ[k] z) =
      d • FreeBaseChange.coefficient f (term k A N n) z -
        d ⊗ₜ[k] differential k A N n z := by
  unfold twoSidedDifferential
  rw [FreeBaseChange.map_tmul, differential_succ_tmul k A N n 1 z,
    one_smul, map_sub, FreeBaseChange.coefficient_tmul, map_one, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem twoSidedDifferential_sq (n : ℕ) :
    (twoSidedDifferential k A D N f n).comp
      (twoSidedDifferential k A D N f (n+1)) = 0 := by
  unfold twoSidedDifferential
  rw [← FreeBaseChange.map_comp, differential_sq, FreeBaseChange.map_zero]

/-- Actual D-linear two-sided bar complex with degree-n term D ⊗_k A^⊗n ⊗_k N. -/
def twoSidedComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (D ⊗[k] term k A N n))
    (fun n => ModuleCat.ofHom (twoSidedDifferential k A D N f n))
    (fun n => ModuleCat.hom_ext (twoSidedDifferential_sq k A D N f n))
end DerivedBar

end

end OAI
