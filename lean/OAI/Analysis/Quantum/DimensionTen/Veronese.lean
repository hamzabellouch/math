import OAI.Analysis.Quantum.DimensionTen.PureMatrices

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma sqrtTwo_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

lemma sqrtTwo_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

def veronese (x : Fin 4 → ℂ) (i : Fin 10) : ℂ :=
  let p := (symmetricPairs i).1
  let q := (symmetricPairs i).2
  (if p = q then 1 else (Real.sqrt 2 : ℂ)) * x p * x q

lemma symmetric_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry *ᵥ veronese x = productVector x x := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, symmetricIsometry,
      symmetricPairs, veronese, productVector] <;>
      field_simp [sqrtTwo_ne]

lemma veronese_adjoint (x : Fin 4 → ℂ) :
    veronese x = symmetricIsometryᴴ *ᵥ productVector x x := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, symmetricIsometry, symmetricPairs, veronese,
      productVector] <;>
    field_simp [sqrtTwo_ne] <;> ring_nf <;> simp only [sqrtTwo_sq] <;> ring

lemma symmetric_pure_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry * pure (veronese x) * symmetricIsometryᴴ =
      pure x ⊗ₖ pure x := by
  rw [pure_conjugate, symmetric_veronese, pure_kronecker]

def symmetricIndex (i : Fin 10) : QuadraticIndex :=
  ⟨symmetricPairs i, by fin_cases i <;> decide⟩

lemma symmetricIndex_bijective : Function.Bijective symmetricIndex := by decide

def symmetricEquiv : Fin 10 ≃ QuadraticIndex :=
  Equiv.ofBijective symmetricIndex symmetricIndex_bijective

def veroneseCoeffs (u : Fin 10 → ℂ) (ij : QuadraticIndex) : ℂ :=
  star (u (symmetricEquiv.symm ij)) *
    (if ij.val.1 = ij.val.2 then 1 else (Real.sqrt 2 : ℂ))

lemma veronese_dot (u : Fin 10 → ℂ) (x : Fin 4 → ℂ) :
    star u ⬝ᵥ veronese x = quadraticEval (veroneseCoeffs u) x := by
  rw [quadraticEval, ← Equiv.sum_comp symmetricEquiv]
  simp only [veroneseCoeffs, Equiv.symm_apply_apply, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change star (u i) * veronese x i = star (u i) *
    (if (symmetricPairs i).1 = (symmetricPairs i).2 then 1 else (Real.sqrt 2 : ℂ)) *
      x (symmetricPairs i).1 * x (symmetricPairs i).2
  simp only [veronese]
  ring

lemma veroneseCoeffs_ne {u : Fin 10 → ℂ} (hu : u ≠ 0) : veroneseCoeffs u ≠ 0 := by
  intro hh
  apply hu
  ext i
  have hi := congrFun hh (symmetricEquiv i)
  simp only [veroneseCoeffs, Equiv.symm_apply_apply, Pi.zero_apply] at hi
  have hn : (if (symmetricEquiv i).val.1 = (symmetricEquiv i).val.2 then (1:ℂ)
    else (Real.sqrt 2 : ℂ)) ≠ 0 := by split_ifs <;> simp_all
  have : star (u i) = 0 := (mul_eq_zero.mp hi).resolve_right hn
  simpa only [star_eq_zero, Pi.zero_apply] using this

end DimensionTen

end
end

end OAI
