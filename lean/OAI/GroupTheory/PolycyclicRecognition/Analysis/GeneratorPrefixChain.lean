import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes

namespace OAI

/-! # Fixed-length chains of actual generator prefixes

Words of length at most N are padded by zero-amplitude switches. This
identifies the adjacent pairs to which the interior-switch theorem applies,
while leaving the actual endpoint unchanged.
-/

noncomputable section
namespace PolycyclicRecognition

variable {I L G : Type*} [AddCommGroup L] [Module ℝ L] [Group G]

def generatorStepOrZero (i₀ : I) (w : List (I × ℝ)) (m : ℕ) : I × ℝ :=
  w[m]?.getD (i₀, 0)

theorem generatorStepOrZero_bound (i₀ : I) (w : List (I × ℝ)) (m : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ z ∈ w, |z.2| ≤ C) :
    |(generatorStepOrZero i₀ w m).2| ≤ C := by
  by_cases hm : m < w.length
  · simpa only [generatorStepOrZero, List.getElem?_eq_getElem hm, Option.getD_some]
      using hw (w[m]) (List.getElem_mem hm)
  · simpa only [generatorStepOrZero, List.getElem?_eq_none (Nat.le_of_not_gt hm),
      Option.getD_none, abs_zero] using hC

theorem generatorGroupWord_prefix_step
    (X : I → L) (Exp : L → G) (hzero : Exp 0 = 1)
    (i₀ : I) (w : List (I × ℝ)) (m : ℕ) :
    generatorGroupWord X Exp (w.take (m + 1)) =
      generatorGroupWord X Exp (w.take m) *
        Exp ((generatorStepOrZero i₀ w m).2 • X (generatorStepOrZero i₀ w m).1) := by
  by_cases hm : m < w.length
  · rw [List.take_succ_eq_append_getElem hm]
    simp only [generatorStepOrZero, List.getElem?_eq_getElem hm, Option.getD_some,
      generatorGroupWord, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  · have hm' : w.length ≤ m := Nat.le_of_not_gt hm
    rw [List.take_of_length_le (hm'.trans (Nat.le_succ m)), List.take_of_length_le hm']
    simp only [generatorStepOrZero, List.getElem?_eq_none hm', Option.getD_none,
      zero_smul, hzero, mul_one]

theorem generatorGroupWord_prefix_last
    (X : I → L) (Exp : L → G) (w : List (I × ℝ)) (N : ℕ) (hN : w.length ≤ N) :
    generatorGroupWord X Exp (w.take N) = generatorGroupWord X Exp w := by
  rw [List.take_of_length_le hN]

end PolycyclicRecognition

end

end OAI
