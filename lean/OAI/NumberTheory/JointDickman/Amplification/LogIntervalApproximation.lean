import OAI.NumberTheory.JointDickman.Amplification.RampCutoff
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace OAI

/-! # Polynomial approximation of fixed logarithmic interval tests -/
namespace JointDickman
open Finset Classical
open scoped Topology

noncomputable def logIntervalRamp (a b δ t : ℝ) : ℝ :=
  averagingRamp (Real.exp (-(b+δ))) (Real.exp (-b)) t -
    averagingRamp (Real.exp (-a)) (Real.exp (-(a-δ))) t

theorem logIntervalRamp_continuous (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (logIntervalRamp a b δ) := by
  exact ((averagingRamp_lipschitz (Real.exp_lt_exp.mpr (by linarith : -(b+δ) < -b))).continuous).sub
    ((averagingRamp_lipschitz (Real.exp_lt_exp.mpr (by linarith : -a < -(a-δ)))).continuous)

theorem logIntervalRamp_eq_one {a b δ s : ℝ} (hδ : 0 < δ)
    (hs : s ∈ Set.Ioc a b) : logIntervalRamp a b δ (Real.exp (-s)) = 1 := by
  unfold logIntervalRamp
  rw [averagingRamp_one (Real.exp_lt_exp.mpr (by linarith : -(b+δ) < -b))
    (Real.exp_le_exp.mpr (by linarith [hs.2])),
    averagingRamp_zero (Real.exp_lt_exp.mpr (by linarith : -a < -(a-δ)))
    (Real.exp_le_exp.mpr (by linarith [hs.1]))]
  ring

theorem logIntervalRamp_eq_zero_left {a b δ s : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hs : s ≤ a-δ) : logIntervalRamp a b δ (Real.exp (-s)) = 0 := by
  unfold logIntervalRamp
  rw [averagingRamp_one (Real.exp_lt_exp.mpr (by linarith : -(b+δ) < -b))
    (Real.exp_le_exp.mpr (by linarith)),
    averagingRamp_one (Real.exp_lt_exp.mpr (by linarith : -a < -(a-δ)))
    (Real.exp_le_exp.mpr (by linarith))]
  ring

theorem logIntervalRamp_eq_zero_right {a b δ s : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hs : b+δ ≤ s) : logIntervalRamp a b δ (Real.exp (-s)) = 0 := by
  unfold logIntervalRamp
  rw [averagingRamp_zero (Real.exp_lt_exp.mpr (by linarith : -(b+δ) < -b))
    (Real.exp_le_exp.mpr (by linarith)),
    averagingRamp_zero (Real.exp_lt_exp.mpr (by linarith : -a < -(a-δ)))
    (Real.exp_le_exp.mpr (by linarith))]
  ring

theorem logIntervalRamp_abs_le_one (a b t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |logIntervalRamp a b δ t| ≤ 1 := by
  have h₁ := averagingRamp_bounds (Real.exp_lt_exp.mpr (by linarith : -(b+δ) < -b)) t
  have h₂ := averagingRamp_bounds (Real.exp_lt_exp.mpr (by linarith : -a < -(a-δ))) t
  exact abs_le.mpr ⟨by dsimp [logIntervalRamp]; linarith,
    by dsimp [logIntervalRamp]; linarith⟩

theorem logIntervalRamp_square_error {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (s : ℝ) :
    ((if s ∈ Set.Ioc a b then (1 : ℝ) else 0)-logIntervalRamp a b δ (Real.exp (-s)))^2 ≤
      (if s ∈ Set.Ioc (a-δ) a then (1 : ℝ) else 0) +
        (if s ∈ Set.Ioc b (b+δ) then (1 : ℝ) else 0) := by
  have ha := logIntervalRamp_abs_le_one a b (Real.exp (-s)) hδ
  have hsq : (logIntervalRamp a b δ (Real.exp (-s)))^2 ≤ 1 := by
    rcases abs_le.mp ha with ⟨hl,hu⟩
    nlinarith [sq_nonneg (logIntervalRamp a b δ (Real.exp (-s)))]
  by_cases hi : s ∈ Set.Ioc a b
  · rw [ite_eq_left hi,logIntervalRamp_eq_one hδ hi]
    simp only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · rw [ite_eq_right hi]
    by_cases hl : s ≤ a-δ
    · rw [logIntervalRamp_eq_zero_left hab hδ hl]
      simp only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0)]
      positivity
    · by_cases hr : b+δ ≤ s
      · rw [logIntervalRamp_eq_zero_right hab hδ hr]
        simp only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0)]
        positivity
      · have hb : s ∈ Set.Ioc (a-δ) a ∨ s ∈ Set.Ioc b (b+δ) := by
          simp only [Set.mem_Ioc] at *
          by_cases hs : s ≤ a
          · exact Or.inl ⟨lt_of_not_ge hl,hs⟩
          · exact Or.inr ⟨lt_of_not_ge (fun h => hi ⟨lt_of_not_ge hs,h⟩),le_of_lt (lt_of_not_ge hr)⟩
        rcases hb with hb | hb
        · rw [ite_eq_left hb]
          split_ifs <;> nlinarith
        · rw [ite_eq_left hb]
          split_ifs <;> nlinarith

theorem interval_polynomial_approximation (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.eval t-f t| < ε := by
  let K := Set.Icc (0 : ℝ) 1
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact K)
  let F : C(K,ℝ) := ⟨fun x => f x,hf.domRestrict⟩
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (polynomialFunctions K) (polynomialFunctions_separatesPoints K) F F.continuous ε hε
  have hp : (g : C(K,ℝ)) ∈ Set.range (Polynomial.toContinuousMapOnAlgHom K) := by
    rw [← polynomialFunctions_coe]
    exact g.property
  obtain ⟨P,hP⟩ := hp
  refine ⟨P,fun t ht => ?_⟩
  have hh := hg ⟨t,ht⟩
  rw [← hP] at hh
  change ‖P.eval t-f t‖ < ε at hh
  simpa only [Real.norm_eq_abs] using hh

end JointDickman

end OAI
