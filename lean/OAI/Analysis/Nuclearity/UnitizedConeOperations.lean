import OAI.Analysis.Nuclearity.UnitizedAbelianClosure

namespace OAI

/-! Padding and scaling finite coefficient arrays. These are the finite
operations used to combine rows in the actual abelian coefficient cone. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

lemma unitizedSandwich_zero_left (x : D) (b : Unitization ℂ D) :
    unitizedSandwich 0 x b = 0 := by
  simp [unitizedSandwich, unitizedLeftMul, unitizedRightMul]

lemma unitizedSandwich_zero_right (a : Unitization ℂ D) (x : D) :
    unitizedSandwich a x 0 = 0 := by
  simp [unitizedSandwich, unitizedRightMul]

lemma unitizedSandwich_real_smul (r : ℝ) (a b : Unitization ℂ D) (x : D) :
    unitizedSandwich (r • a) x (r • b) = (r * r) • unitizedSandwich a x b := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [inr_unitizedSandwich, Unitization.inr_smul, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul]

lemma unitizedCoefficientEnlargement_pad_right {m n : ℕ} (T : B → D)
    (a : Fin m → Unitization ℂ D) (c : Fin m → B) (b : B) :
    unitizedCoefficientEnlargement T (Fin.append a (0 : Fin n → Unitization ℂ D))
        (Fin.append c (0 : Fin n → B)) b = unitizedCoefficientEnlargement T a c b := by
  simp only [unitizedCoefficientEnlargement, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Pi.zero_apply, unitizedSandwich_zero_left,
    unitizedSandwich_zero_right, Finset.sum_const_zero, add_zero]

lemma unitizedCoefficientEnlargement_pad_left {m n : ℕ} (T : B → D)
    (a : Fin n → Unitization ℂ D) (c : Fin n → B) (b : B) :
    unitizedCoefficientEnlargement T (Fin.append (0 : Fin m → Unitization ℂ D) a)
        (Fin.append (0 : Fin m → B) c) b = unitizedCoefficientEnlargement T a c b := by
  simp only [unitizedCoefficientEnlargement, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Pi.zero_apply, unitizedSandwich_zero_left,
    unitizedSandwich_zero_right, Finset.sum_const_zero, zero_add]

lemma unitizedCoefficientEnlargement_nonneg_smul {I : Type*} [Fintype I]
    (T : B → D) (a : I → Unitization ℂ D) (c : I → B) (b : B) {r : ℝ} (hr : 0 ≤ r) :
    unitizedCoefficientEnlargement T (fun i => Real.sqrt r • a i) c b =
      r • unitizedCoefficientEnlargement T a c b := by
  simp only [unitizedCoefficientEnlargement, unitizedSandwich_real_smul,
    Real.mul_self_sqrt hr, Finset.smul_sum]

end WeakPureInfiniteness

end

end OAI
