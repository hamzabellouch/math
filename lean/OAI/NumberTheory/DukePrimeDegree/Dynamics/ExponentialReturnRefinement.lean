import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteTransverseCode
import OAI.NumberTheory.DukePrimeDegree.Entropy.RefinedReturnPartition

namespace OAI

/-! # Exponentially fine transverse return cells with finite entropy -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

lemma log_exponential_grid_bound {d K n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hK : (K:ℝ) ≤ 1+(2*R+2)^d/(Real.exp (-(n+1:ℝ)))^d) :
    Real.log K ≤ (Real.log (1+(2*R+2)^d)+d)*(n+1) := by
  let A := (2*R+2)^d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlog : 0 ≤ Real.log (1+A) := Real.log_nonneg (by linarith)
  have hn : 1 ≤ (n+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  by_cases hz : K=0
  · subst K
    simp only [Nat.cast_zero,Real.log_zero]
    exact mul_nonneg (add_nonneg hlog (Nat.cast_nonneg d)) (by positivity)
  have hKpos : (0:ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hz
  have he : 1 ≤ Real.exp ((d:ℝ)*(n+1)) := Real.one_le_exp_iff.mpr (by positivity)
  have hpow : (Real.exp (-(n+1:ℝ)))^d=Real.exp (-((d:ℝ)*(n+1))) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hbound : (K:ℝ) ≤ (1+A)*Real.exp ((d:ℝ)*(n+1)) := by
    rw [hpow,Real.exp_neg,div_inv_eq_mul] at hK
    dsimp only [A]
    nlinarith
  calc
    Real.log K ≤ Real.log ((1+A)*Real.exp ((d:ℝ)*(n+1))) :=
      Real.log_le_log hKpos hbound
    _ = Real.log (1+A)+(d:ℝ)*(n+1) := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]
    _ ≤ (Real.log (1+A)+d)*(n+1) := by nlinarith

theorem exists_exponential_return_refinement
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ S, ∀ i, |f x i| ≤ R) :
    ∃ (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)),
      (∀ n, Measurable (B n)) ∧
      Summable (fun z : Option (Σ n : ℕ, Fin (K n)) =>
        Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) ∧
      ∀ n x y, x ∈ firstReturnLevel T S n →
        returnRefinement T S B y=returnRefinement T S B x →
        ∀ i, |f y i-f x i| < 2*Real.exp (-(n+1:ℝ)) := by
  have hδ (n : ℕ) : Real.exp (-(n+1:ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose K B hB hcard hclose using fun n : ℕ =>
    exists_bounded_vector_code f hf hR (Real.exp_pos (-(n+1:ℝ))) (hδ n)
  refine ⟨K,B,hB,returnRefinement_information_summable μ hT hE hS K B hB
    (Real.log (1+(2*R+2)^d)+d)
    (fun n => log_exponential_grid_bound hR (hcard n)),?_⟩
  intro n x y hx hxy i
  have hlabel : returnRefinement T S B x=some ⟨n,B n x⟩ := by
    have hm : x ∈ returnRefinementAtom T S B (some ⟨n,B n x⟩) := ⟨hx,rfl⟩
    rw [←returnRefinement_fiber] at hm
    exact hm
  have hy : y ∈ returnRefinementAtom T S B (some ⟨n,B n x⟩) := by
    rw [←returnRefinement_fiber]
    exact hxy.trans hlabel
  exact hclose n x y (hbound x hx.1) hy.2 i

end DukePrimeDegree

end

end OAI
