import OAI.Probability.InvariantIsing.Fields.MarkPairRecursion
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorAncestorInput

namespace OAI

/-! Indexing the general finite mark recursion at the actual tensor ancestor kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem tensor_mark_pair_recursion {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (d q i : ℕ) (z₁ z₂ : SpinTensorIndex I degree → ℝ)
    (F : (Fin q → (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) → ℝ) :
    markPairPathMean q (fun j => tensorAncestorMarkKernel eig U c I degree amplitude n b v (j+i))
      (d-i) z₁ z₂ F = tensorAncestorPairPathMean eig U c I degree amplitude n b v d q i z₁ z₂ F := by
  induction q generalizing i z₁ z₂ with
  | zero => rfl
  | succ q ih =>
    by_cases hid : i < d
    · have hd : d-i = (d-(i+1))+1 := by omega
      rw [hd,markPairPathMean,tensorAncestorPairPathMean,ite_eq_left hid]
      simp only [Nat.zero_add]
      apply integral_congr_ae
      apply ae_of_all
      intro a
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using ih (i+1) (z₁+a) (z₂+a) (fun w => F (Fin.cons (a,a) w))
    · have hd : d-i = 0 := by omega
      have hd' : d-(i+1) = 0 := by omega
      rw [hd,markPairPathMean,tensorAncestorPairPathMean,ite_eq_right hid]
      simp only [Nat.zero_add]
      apply integral_congr_ae
      apply ae_of_all
      intro a₁
      apply integral_congr_ae
      apply ae_of_all
      intro a₂
      simpa only [Nat.add_assoc,Nat.add_comm 1 i,hd'] using ih (i+1) (z₁+a₁) (z₂+a₂) (fun w => F (Fin.cons (a₁,a₂) w))

end InvariantIsing

end

end OAI
