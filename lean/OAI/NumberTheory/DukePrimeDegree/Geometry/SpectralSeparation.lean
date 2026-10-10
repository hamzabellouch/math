import OAI.NumberTheory.DukePrimeDegree.Geometry.SpectralPerturbation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-!
# The spectral estimate for exceptional returns

EKL (2006), Lemma 5.3, in the form needed for real diagonal return
matrices. A fixed neighborhood of the identity works for every set of
logarithmic diagonal weights separated by more than one.
-/

noncomputable section
open Set Matrix
open scoped BigOperators Classical

namespace DukePrimeDegree

/-- Uniform relative error allowed by half-unit logarithmic brackets. -/
def spectralRelativeRadius : ℝ := 1 - Real.exp (-(1 / 2 : ℝ))

lemma spectralRelativeRadius_pos : 0 < spectralRelativeRadius := by
  unfold spectralRelativeRadius
  have : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

lemma exp_gap_distance {x y : ℝ} (hxy : (1 / 2 : ℝ) ≤ |x - y|) :
    spectralRelativeRadius * Real.exp y ≤ ‖Real.exp x - Real.exp y‖ := by
  have he : 2 ≤ Real.exp (1 / 2 : ℝ) + Real.exp (-(1 / 2 : ℝ)) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ), Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have hy : 0 < Real.exp y := Real.exp_pos y
  rcases le_total x y with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hxy
    have hx : x ≤ y - 1 / 2 := by linarith
    have hexp := Real.exp_le_exp.mpr hx
    rw [Real.exp_sub] at hexp
    have hr : Real.exp y / Real.exp (1 / 2 : ℝ) =
        Real.exp y * Real.exp (-(1 / 2 : ℝ)) := by rw [Real.exp_neg, div_eq_mul_inv]
    rw [hr] at hexp
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hle))]
    unfold spectralRelativeRadius
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hxy
    have hx : y + 1 / 2 ≤ x := by linarith
    have hexp := Real.exp_le_exp.mpr hx
    rw [Real.exp_add] at hexp
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hle))]
    unfold spectralRelativeRadius
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hy.le]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma logarithmic_gap_brackets (ell : ι → ℝ)
    (hgap : ∀ i j, i ≠ j → 1 < |ell i - ell j|) :
    (∀ i j, j ≠ i → Real.exp (ell j) < Real.exp (ell i - 1 / 2) ∨
      Real.exp (ell i + 1 / 2) < Real.exp (ell j)) ∧
    (∀ i j, i ≠ j → Real.exp (ell i + 1 / 2) ≤ Real.exp (ell j - 1 / 2) ∨
      Real.exp (ell j + 1 / 2) ≤ Real.exp (ell i - 1 / 2)) ∧
    (∀ i k, spectralRelativeRadius * Real.exp (ell k) ≤
      ‖Real.exp (ell i - 1 / 2) - Real.exp (ell k)‖) ∧
    (∀ i k, spectralRelativeRadius * Real.exp (ell k) ≤
      ‖Real.exp (ell i + 1 / 2) - Real.exp (ell k)‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hji
    rcases lt_abs.mp (hgap i j hji.symm) with h | h
    · left
      apply Real.exp_lt_exp.mpr
      linarith
    · right
      apply Real.exp_lt_exp.mpr
      linarith
  · intro i j hij
    rcases lt_abs.mp (hgap i j hij) with h | h
    · right
      apply Real.exp_le_exp.mpr
      linarith
    · left
      apply Real.exp_le_exp.mpr
      linarith
  · intro i k
    apply exp_gap_distance
    by_cases hik : i = k
    · subst k
      norm_num
    · rcases lt_abs.mp (hgap i k hik) with h | h
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith
  · intro i k
    apply exp_gap_distance
    by_cases hik : i = k
    · subst k
      norm_num
    · rcases lt_abs.mp (hgap i k hik) with h | h
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith

/-- The roots of a small perturbation of a logarithmically separated positive
 diagonal matrix are real, distinct, and stay in their half-unit log brackets. -/
theorem real_spectrum_of_logarithmic_gaps (ell : ι → ℝ)
    (hgap : ∀ i j, i ≠ j → 1 < |ell i - ell j|)
    (H : Matrix ι ι ℝ)
    (hH : ∀ i, ∑ j, ‖(H - 1) i j‖ < spectralRelativeRadius) :
    ∃ r : ι → ℝ, Function.Injective r ∧
      (∀ i, 0 < r i ∧ |Real.log (r i) - ell i| < 1 / 2 ∧
        (H * diagonal (fun j => Real.exp (ell j))).charpoly.eval (r i) = 0) ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.roots =
        (Finset.univ.image r).val ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.Splits ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.Separable := by
  let D := diagonal (fun i => Real.exp (ell i))
  let E := D * (H - 1)
  have hrow (i : ι) : ∑ j, ‖E i j‖ < spectralRelativeRadius * Real.exp (ell i) := by
    have hs : (∑ j, ‖E i j‖) = Real.exp (ell i) * ∑ j, ‖(H - 1) i j‖ := by
      simp only [E, D, Matrix.diagonal_mul, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Finset.mul_sum]
    rw [hs, mul_comm spectralRelativeRadius]
    exact mul_lt_mul_of_pos_left (hH i) (Real.exp_pos _)
  obtain ⟨hout, hdis, ha, hb⟩ := logarithmic_gap_brackets ell hgap
  obtain ⟨r, hr, hinj, hroots, hsplit, hsep⟩ := charpoly_roots_of_separated_brackets
    (fun i => Real.exp (ell i)) E
    (fun i => Real.exp (ell i - 1 / 2)) (fun i => Real.exp (ell i + 1 / 2))
    (fun i => Real.exp_lt_exp.mpr (by linarith))
    (fun i => Real.exp_lt_exp.mpr (by linarith)) hout hdis
    (fun i k => (hrow k).trans_le (ha i k))
    (fun i k => (hrow k).trans_le (hb i k))
  have hmatrix : diagonal (fun i => Real.exp (ell i)) + E = D * H := by
    dsimp [E]
    rw [mul_sub, Matrix.mul_one, add_sub_cancel]
  have hpoly : (diagonal (fun i => Real.exp (ell i)) + E).charpoly = (H * D).charpoly := by
    rw [hmatrix, Matrix.charpoly_mul_comm]
  rw [hpoly] at hr hroots hsplit hsep
  refine ⟨r, hinj, ?_, hroots, hsplit, hsep⟩
  intro i
  have hpos : 0 < r i := (Real.exp_pos _).trans (hr i).1.1
  refine ⟨hpos, ?_, (hr i).2⟩
  rw [abs_lt]
  have hlo : ell i - 1 / 2 < Real.log (r i) := by
    exact (Real.lt_log_iff_exp_lt hpos).mpr (hr i).1.1
  have hhi : Real.log (r i) < ell i + 1 / 2 := by
    exact (Real.log_lt_iff_lt_exp hpos).mpr (hr i).1.2
  constructor <;> linarith

/-- The row bound defines a fixed neighborhood of the identity. -/
lemma eventually_spectral_row_bound :
    ∀ᶠ H : Matrix ι ι ℝ in nhds 1,
      ∀ i, ∑ j, ‖(H - 1) i j‖ < spectralRelativeRadius := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun H : Matrix ι ι ℝ => ∑ j, ‖(H - 1) i j‖) := by
    apply continuous_finsetSum
    intro j _
    fun_prop
  have hsmall : (∑ j, ‖((1 : Matrix ι ι ℝ) - 1) i j‖) < spectralRelativeRadius := by
    simpa using spectralRelativeRadius_pos
  exact hc.continuousAt.eventually (gt_mem_nhds hsmall)

/-- EKL Lemma 5.3: a single neighborhood works uniformly over the separated weights. -/
theorem eventually_real_spectrum_uniform :
    ∀ᶠ H : Matrix ι ι ℝ in nhds 1, ∀ ell : ι → ℝ,
      (∀ i j, i ≠ j → 1 < |ell i - ell j|) →
      ∃ r : ι → ℝ, Function.Injective r ∧
        (∀ i, 0 < r i ∧ |Real.log (r i) - ell i| < 1 / 2 ∧
          (H * diagonal (fun j => Real.exp (ell j))).charpoly.eval (r i) = 0) ∧
        (H * diagonal (fun j => Real.exp (ell j))).charpoly.roots =
          (Finset.univ.image r).val ∧
        (H * diagonal (fun j => Real.exp (ell j))).charpoly.Splits ∧
        (H * diagonal (fun j => Real.exp (ell j))).charpoly.Separable := by
  filter_upwards [eventually_spectral_row_bound (ι := ι)] with H hH ell hgap
  exact real_spectrum_of_logarithmic_gaps ell hgap H hH

end DukePrimeDegree

end

end OAI
