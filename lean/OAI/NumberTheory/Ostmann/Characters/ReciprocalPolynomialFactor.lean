import OAI.NumberTheory.Ostmann.Characters.NormalizedFourierProfile
import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

noncomputable def reciprocalPolynomialFactor (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) : ClippedPolynomialFactor where
  polynomial := P
  profile := fun z => Complex.ofReal (z⁻¹)
  lo := 1
  hi := hi
  bound := 1
  lip := 1
  lo_le_hi := hhi
  bound_nonneg := by norm_num
  lip_nonneg := by norm_num
  norm_le := by
    intro z hz
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hz.1))]
    exact inv_le_one_of_one_le₀ hz.1
  lipschitz := by
    intro x hx y hy
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact abs_inv_sub_inv_le_of_one_le x y hx.1 hy.1

theorem reciprocalPolynomialFactor_original (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) (x X M : ℝ) (hX : X ≠ 0) (hM : M ≠ 0)
    (hP : P.eval x = M / X) (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    (reciprocalPolynomialFactor P hi hhi).value x = Complex.ofReal (X / M) := by
  rw [ClippedPolynomialFactor.value_of_mem _ x (by
    change P.eval x ∈ Set.Icc (1 : ℝ) hi
    rw [hP]
    exact hrange)]
  change Complex.ofReal ((P.eval x)⁻¹) = _
  rw [hP]
  congr 1
  field_simp

theorem reciprocalPolynomialFactor_budget (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    2 * (reciprocalPolynomialFactor P hi hhi).bound +
      (reciprocalPolynomialFactor P hi hhi).lip *
        ((reciprocalPolynomialFactor P hi hhi).hi - (reciprocalPolynomialFactor P hi hhi).lo) =
      hi + 1 := by
  dsimp only [reciprocalPolynomialFactor]
  ring

noncomputable def appendReciprocalFactor {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) : Fin (n + 1) → ClippedPolynomialFactor :=
  Fin.append F (fun _ : Fin 1 => reciprocalPolynomialFactor P hi hhi)

theorem appendReciprocalFactor_weight {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) (x X M : ℝ)
    (hX : X ≠ 0) (hM : M ≠ 0) (hP : P.eval x = M / X)
    (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    smoothPolynomialWeight (appendReciprocalFactor F P hi hhi) x =
      smoothPolynomialWeight F x * Complex.ofReal (X / M) := by
  simp only [smoothPolynomialWeight, appendReciprocalFactor, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Fin.prod_univ_one]
  rw [reciprocalPolynomialFactor_original P hi hhi x X M hX hM hP hrange]

theorem appendReciprocalFactor_budget {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    smoothPolynomialBudget (appendReciprocalFactor F P hi hhi) =
      smoothPolynomialBudget F * (hi + 1) := by
  simp only [smoothPolynomialBudget, appendReciprocalFactor, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Fin.prod_univ_one, reciprocalPolynomialFactor_budget]

end Ostmann

end OAI
