import OAI.Analysis.Quantum.PPTSquare.Recurrence
import OAI.Analysis.Quantum.PPTSquare.EigenRows

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilEvaluation
open PencilAlgebra EigenRows
open scoped Matrix
variable {K : Type*} [Field K] [CharZero K]

def action (a : Fin 3) : Matrix (Fin 20) (Fin 20) K :=
  (NNum a).map (Int.castRingHom K)

def evaluation (t : Fin 20 → Fin 3 → K) : Matrix (Fin 20) (Fin 20) K :=
  fun i j => lowMon (t i) j

lemma denominator_ne : (denominator : K) ≠ 0 := by
  norm_num [denominator]

omit [CharZero K] in
lemma action_commute (a : Fin 3) :
    action (K := K) 0 * action a = action a * action 0 := by
  have h : NNum 0 * NNum a = NNum a * NNum 0 := by
    fin_cases a
    · rfl
    · exact N0_N1
    · exact N0_N2
  have hh := congrArg (fun T : Matrix (Fin 20) (Fin 20) ℤ => T.map (Int.castRingHom K)) h
  simpa only [Matrix.map_mul, action] using hh

omit [CharZero K] in
lemma low_vecMul (v : Fin 20 → K) (a : Fin 3) (j : Fin 10) :
    (v ᵥ* action a) (j.castLE (by decide)) = (denominator : K) * v (lowNext a j) := by
  classical
  simp only [Matrix.vecMul, dotProduct, action, Matrix.map_apply, low_col,
    Pi.single_apply]
  simp only [apply_ite, mul_one, mul_zero]
  simp [mul_comm]

omit [CharZero K] in
lemma high_vecMul (v : Fin 20 → K) (a : Fin 3) (j : Fin 10) :
    (v ᵥ* action a) (j.natAdd 10) =
      ((CNum.map (Int.castRingHom K)).mulVec v) (highNext a j) := by
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, action, Matrix.map_apply, high_col]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma eigen_low_recursion (v : Fin 20 → K) (μ : Fin 3 → K)
    (hv : ∀ a, v ᵥ* action a = μ a • v) :
    ∀ j, v j = lowMon (fun a => μ a / (denominator : K)) j * v 0 := by
  apply low_recursion
  intro a j
  have hh := congrFun (hv a) (j.castLE (by decide))
  rw [low_vecMul] at hh
  change (denominator : K) * v (lowNext a j) = μ a * v (j.castLE (by decide)) at hh
  apply (mul_left_cancel₀ (denominator_ne (K := K)))
  calc
    _ = μ a * v (j.castLE (by decide)) := hh
    _ = _ := by rw [← mul_assoc, mul_div_cancel₀ _ (denominator_ne (K := K))]

lemma exists_evaluations (r : Fin 20 → K) (hr : Function.Injective r)
    (hf : (action (K := K) 0).charpoly = ∏ i, (Polynomial.X - Polynomial.C (r i))) :
    ∃ t : Fin 20 → Fin 3 → K,
      IsUnit (evaluation t) ∧
      (∀ a, evaluation t * action a = Matrix.diagonal (fun i => (denominator : K) * t i a) * evaluation t) ∧
      (∀ i, (denominator : K) * t i 0 = r i) := by
  classical
  obtain ⟨S,hS,he⟩ := exists_eigenrows (action 0) r hr hf
  have hμ (a : Fin 3) : ∃ μ : Fin 20 → K, S * action a = Matrix.diagonal μ * S :=
    simultaneous _ _ _ r hr hS he (action_commute a)
  choose μ hμ using hμ
  let t : Fin 20 → Fin 3 → K := fun i a => μ a i / (denominator : K)
  have hd (i : Fin 20) (a : Fin 3) : (denominator : K) * t i a = μ a i := by
    dsimp [t]
    exact mul_div_cancel₀ _ (denominator_ne (K := K))
  have hv (i : Fin 20) (a : Fin 3) : S.row i ᵥ* action a = μ a i • S.row i := by
    ext j
    have hh := congrFun (congrFun (hμ a) i) j
    rw [Matrix.diagonal_mul] at hh
    simpa only [Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using hh
  have hrow (i j : Fin 20) : S i j = lowMon (t i) j * S i 0 :=
    eigen_low_recursion (S.row i) (fun a => μ a i) (hv i) j
  have hc (i : Fin 20) : S i 0 ≠ 0 := by
    intro hh
    apply (Matrix.linearIndependent_rows_iff_isUnit.mpr hS).ne_zero i
    ext j
    rw [Matrix.row_apply, hrow, hh, mul_zero]
    rfl
  have hfactor : S = Matrix.diagonal (fun i => S i 0) * evaluation t := by
    ext i j
    rw [Matrix.diagonal_mul, hrow]
    exact mul_comm _ _
  have hE : IsUnit (evaluation t) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hs := ((Matrix.isUnit_iff_isUnit_det _).mp hS).ne_zero
    apply hs
    rw [hfactor, Matrix.det_mul, hz, mul_zero]
  have hev (a : Fin 3) : evaluation t * action a = Matrix.diagonal (fun i => (denominator : K) * t i a) * evaluation t := by
    ext i j
    apply (mul_left_cancel₀ (hc i))
    have hh := congrFun (congrFun (hμ a) i) j
    rw [Matrix.diagonal_mul] at hh ⊢
    simp only [Matrix.mul_apply] at hh ⊢
    have hleft : (∑ k, S i k * action a k j) =
        ∑ k, (lowMon (t i) k * S i 0) * action a k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hrow i k]
    rw [hleft, hrow i j] at hh
    rw [Finset.mul_sum]
    calc
      _ = ∑ k, (lowMon (t i) k * S i 0) * action a k j := by
        apply Finset.sum_congr rfl
        intro k _
        change S i 0 * (lowMon (t i) k * action a k j) = _
        ring
      _ = μ a i * (lowMon (t i) j * S i 0) := hh
      _ = _ := by rw [hd]; change _ = S i 0 * (μ a i * lowMon (t i) j); ring
  refine ⟨t,hE,hev,?_⟩
  intro i
  have hh := congrFun (congrFun he i) 0
  have hh' := congrFun (congrFun (hμ 0) i) 0
  rw [Matrix.diagonal_mul] at hh hh'
  rw [hd]
  exact mul_right_cancel₀ (hc i) (hh'.symm.trans hh)

end PencilEvaluation

end

end OAI
