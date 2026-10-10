import OAI.Probability.InvariantIsing.Cavity.CavityInnovationLeaves
import OAI.Probability.IsingPerceptron.RetainedDisplacement

namespace OAI

/-! The quadratic innovation change preserves shared Gaussian prefixes.
This is the deterministic part of transporting common-level spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix Classical

namespace InvariantIsing

def cavityCommonMarkDepth {A : Type} :
    (n : ℕ) → NoiseLeaf A n → NoiseLeaf A n → ℕ
  | 0, _, _ => 0
  | n + 1, v, w => if v.2.1 = w.2.1 then cavityCommonMarkDepth n v.2.2 w.2.2 + 1 else 0

lemma cavityCommonMarkDepth_le {A : Type}
    (n : ℕ) (v w : NoiseLeaf A n) : cavityCommonMarkDepth n v w ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [cavityCommonMarkDepth]
    split_ifs
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

lemma cavityCommonMarkDepth_measurable {d : ℕ} (n : ℕ) :
    Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n => cavityCommonMarkDepth n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [cavityCommonMarkDepth]
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    · have ht : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) ×
          NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) => (p.1.2.2, p.2.2.2)) := by fun_prop
      exact (ih.comp ht).add_const 1
    · exact measurable_const

theorem cavityInnovationLeaf_commonMarkDepth {d : ℕ} (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ∀ i s, Function.Injective (fun a => g i (s, a)))
    (s : EuclideanSpace ℝ (Fin d))
    (v w : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityCommonMarkDepth n (cavityInnovationLeaf n c g s v)
      (cavityInnovationLeaf n c g s w) = cavityCommonMarkDepth n v w := by
  classical
  induction n generalizing c g s with
  | zero => rfl
  | succ n ih =>
    by_cases h : v.2.1 = w.2.1
    · simp only [cavityInnovationLeaf, cavityCommonMarkDepth, h, ite_true]
      rw [ih _ _ (fun i => hg (i + 1))]
    · have hh : g 0 (s, v.2.1) ≠ g 0 (s, w.2.1) := (hg 0 s).ne h
      simp only [cavityInnovationLeaf, cavityCommonMarkDepth, h, hh, ite_false]

lemma cavityStepInnovation_injective {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (hC : IsUnit (1 - C * K).det)
    (s : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (fun a => cavityStepInnovation K P C (s, a)) := by
  have hi : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹) := by
    apply Function.LeftInverse.injective (g := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K))
    intro x
    rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_nonsing_inv _ hC,
      map_one, one_apply_eq_self]
  intro a b hab
  apply add_left_cancel (a := s)
  apply hi
  exact (sub_left_inj).mp hab

theorem cavityQuadraticInnovation_commonMarkDepth {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (hdet : ∀ i, IsUnit (1 - H i * K).det) (s : EuclideanSpace ℝ (Fin d))
    (v w : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityCommonMarkDepth n
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s v)
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s w) =
        cavityCommonMarkDepth n v w := by
  classical
  exact cavityInnovationLeaf_commonMarkDepth n c _
    (fun i => cavityStepInnovation_injective K (H i) (H (i + 1)) (hdet (i + 1))) s v w

end InvariantIsing

end

end OAI
