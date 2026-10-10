import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMassStability

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAtom_nonneg (n : ℕ) (m : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m) (j : Fin (n+1)) :
    0 ≤ hierarchyAtom n m u j := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hierarchyAtom, Fin.lastCases_last]
      exact sub_nonneg.mpr (hmu (Fin.last n))
    · simp only [hierarchyAtom, Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (hm (Fin.last n)) (fun i => hm i.castSucc)
        (fun i => hmono (Fin.le_last _))
        (fun _ _ h => hmono (Fin.castSucc_le_castSucc_iff.mpr h)) i

theorem hierarchyAtom_sum (n : ℕ) (m : Fin n → ℝ) (u : ℝ) :
    ∑ j, hierarchyAtom n m u j = u := by
  induction n generalizing u with
  | zero => simp [hierarchyAtom]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom, Fin.lastCases_castSucc, Fin.lastCases_last, ih]
    ring

theorem hierarchyLevel_uniform_nonexpansive (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {ε : ℝ}
    (hfg : ∀ z, |f z-g z| ≤ ε) (j : Fin (n+1)) (z : ParameterSpace n) :
    |hierarchyLevel n m f j z-hierarchyLevel n m g j z| ≤ ε := by
  induction n with
  | zero => exact hfg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hierarchyLevel, Fin.lastCases_last]
      exact hfg z
    · simp only [hierarchyLevel, Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (fun i => hm i.castSucc)
        (hf.gaussianStep _) (hg.gaussianStep _)
        (gaussianStep_uniform_nonexpansive hf hg (hm (Fin.last n)) hfg) i z.1

theorem hierarchyPenalty_uniform_nonexpansive (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u)
    (hmono : Monotone m) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {ε : ℝ}
    (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    |hierarchyPenalty n m u f z-hierarchyPenalty n m u g z| ≤ u*ε := by
  simp only [hierarchyPenalty_sum, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ j, |hierarchyAtom n m u j*(hierarchyLevel n m f j z-hierarchyLevel n m g j z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, hierarchyAtom n m u j*|hierarchyLevel n m f j z-hierarchyLevel n m g j z| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hierarchyAtom_nonneg n m hu hm hmu hmono j)]
    _ ≤ ∑ j, hierarchyAtom n m u j*ε := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hierarchyLevel_uniform_nonexpansive n m hm hf hg hfg j z)
        (hierarchyAtom_nonneg n m hu hm hmu hmono j))
    _ = u*ε := by rw [← Finset.sum_mul, hierarchyAtom_sum]

theorem hierarchyPathWeight_ratio_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z ≤ Real.exp (2*ε)*hierarchyPathWeight n m g z := by
  rw [hierarchyPathWeight_eq n m f 1, hierarchyPathWeight_eq n m g 1, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have H := hierarchyPenalty_uniform_nonexpansive n m zero_le_one (fun i => (hm i).1)
    (fun i => (hm i).2) hmono hf hg hfg z
  have Hf := hfg z
  simp only [one_mul] at *
  linarith [(abs_le.mp H).1,(abs_le.mp Hf).2]

theorem hierarchyPathWeight_abs_sub_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ≤
      (Real.exp (2*ε)-1)*(hierarchyPathWeight n m f z+hierarchyPathWeight n m g z) := by
  have H₁ := hierarchyPathWeight_ratio_bound n m hm hmono hf hg hfg z
  have H₂ := hierarchyPathWeight_ratio_bound n m hm hmono hg hf
    (fun z => by simpa only [abs_sub_comm] using hfg z) z
  have hC : 0 ≤ Real.exp (2*ε)-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hWf := (hierarchyPathWeight_pos n m f z).le
  have hWg := (hierarchyPathWeight_pos n m g z).le
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hC hWf]
  · nlinarith [mul_nonneg hC hWg]

end SK.Analytic

end
end

end OAI
