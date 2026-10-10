import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CellVars
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
namespace SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

def inverseExponent (a : I → I → ℕ) (i j : I) : ℤ :=
  (if i=j then 1 else 0)-(a i j:ℤ)

noncomputable def rawFactor (a : I → I → ℕ) (d e : I → ℕ)
    (i j : I) (x : Fin (d i)) (y : Fin (e j)) :
    (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ :=
  affineUnit (X (Sum.inr ⟨j,y⟩)-X (Sum.inl ⟨i,x⟩)) ^ inverseExponent a i j

noncomputable def renameSeries (d e : I → ℕ) (σ : CellGroup d e) :
    LaurentSeries (MvPolynomial (CellVars d e) ℚ) →+*
      LaurentSeries (MvPolynomial (CellVars d e) ℚ) :=
  mapRing (rename (cellAction d e σ)).toRingHom

omit [Fintype I] in
lemma rename_rawFactor (a : I → I → ℕ) (d e : I → ℕ)
    (σ : CellGroup d e) (i j : I) (x : Fin (d i)) (y : Fin (e j)) :
    Units.map (renameSeries d e σ).toMonoidHom (rawFactor a d e i j x y)=
      rawFactor a d e i j (σ.1 i x) (σ.2 j y) := by
  unfold rawFactor renameSeries
  rw [map_zpow,affineUnit_map]
  congr 2
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_sub,rename_X]
  rfl

noncomputable def rawInverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ :=
  ∏ i, ∏ j, ∏ x : Fin (d i), ∏ y : Fin (e j), rawFactor a d e i j x y

lemma rawInverseKernelUnit_symmetric (a : I → I → ℕ) (d e : I → ℕ)
    (σ : CellGroup d e) :
    Units.map (renameSeries d e σ).toMonoidHom
      (rawInverseKernelUnit a d e)=rawInverseKernelUnit a d e := by
  simp only [rawInverseKernelUnit,map_prod,rename_rawFactor]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  calc
    _ = ∏ x : Fin (d i), ∏ y : Fin (e j), rawFactor a d e i j (σ.1 i x) y := by
      exact Finset.prod_congr rfl (fun x hx=>Equiv.prod_comp (σ.2 j) _)
    _ = _ := Equiv.prod_comp (σ.1 i) (fun x : Fin (d i)=>∏ y : Fin (e j), rawFactor a d e i j x y)

def IsSeparate (d e : I → ℕ) (f : LaurentSeries (MvPolynomial (CellVars d e) ℚ)) : Prop :=
  ∀ σ : CellGroup d e, renameSeries d e σ f=f

noncomputable def separateSeries (d e : I → ℕ) :
    LaurentSeries (MvPolynomial (CellVars d e) ℚ) →ₗ[ℚ] LaurentSeries (S d ⊗[ℚ] S e) :=
  mapLinear (separateTensor d e)

lemma realize_separateSeries (d e : I → ℕ)
    (f : LaurentSeries (MvPolynomial (CellVars d e) ℚ)) (hf : IsSeparate d e f) :
    mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom (separateSeries d e f)=f := by
  apply HahnSeries.ext
  funext k
  apply tensorValue_separateTensor
  intro σ
  exact congrArg (fun p : LaurentSeries (MvPolynomial (CellVars d e) ℚ)=>p.coeff k) (hf σ)

lemma realize_injective (d e : I → ℕ) :
    Function.Injective (mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom) :=
  mapRing_injective _ (tensorValue_injective d e)

noncomputable def liftSeparateUnit (d e : I → ℕ)
    (f : (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ)
    (hf : ∀ σ : CellGroup d e, Units.map
      (renameSeries d e σ).toMonoidHom f=f) :
    (LaurentSeries (S d ⊗[ℚ] S e))ˣ where
  val := separateSeries d e f
  inv := separateSeries d e (↑f⁻¹)
  val_inv := by
    apply realize_injective d e
    rw [map_mul,map_one,realize_separateSeries,realize_separateSeries]
    · exact f.val_inv
    · intro σ
      exact congrArg Units.val (by simpa only [map_inv] using congrArg Inv.inv (hf σ))
    · intro σ
      exact congrArg Units.val (hf σ)
  inv_val := by
    apply realize_injective d e
    rw [map_mul,map_one,realize_separateSeries,realize_separateSeries]
    · exact f.inv_val
    · intro σ
      exact congrArg Units.val (hf σ)
    · intro σ
      exact congrArg Units.val (by simpa only [map_inv] using congrArg Inv.inv (hf σ))

noncomputable def inverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    (LaurentSeries (S d ⊗[ℚ] S e))ˣ :=
  liftSeparateUnit d e (rawInverseKernelUnit a d e) (rawInverseKernelUnit_symmetric a d e)

lemma realize_inverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom (inverseKernelUnit a d e).val=(rawInverseKernelUnit a d e).val := by
  exact realize_separateSeries d e (rawInverseKernelUnit a d e).val (fun σ=>
    congrArg Units.val (rawInverseKernelUnit_symmetric a d e σ))

noncomputable def quotientInverseKernelUnit (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (LaurentSeries (B a μ d ⊗[ℚ] B a μ e))ˣ :=
  Units.map (mapRing (R:=S d ⊗[ℚ] S e) (S:=B a μ d ⊗[ℚ] B a μ e) (Algebra.TensorProduct.map (quotientAlg a μ d)
    (quotientAlg a μ e)).toRingHom).toMonoidHom (inverseKernelUnit a d e)

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
