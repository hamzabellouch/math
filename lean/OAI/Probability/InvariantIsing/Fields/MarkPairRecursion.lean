import OAI.Probability.InvariantIsing.Fields.SeedPairRecursion

namespace OAI

/-! The finite conditional-mark recursion needed by the tensor and scalar terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def markPairPathMean : (n : ℕ) → (ℕ → Kernel (ι → ℝ) (ι → ℝ)) →
    ℕ → (ι → ℝ) → (ι → ℝ) → ((Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) → ℝ
  | 0, _, _, _, _, F => F Fin.elim0
  | n+1, κ, 0, z₁, z₂, F =>
      ∫ a₁, ∫ a₂,
        markPairPathMean n (fun i => κ (i+1)) 0 (z₁+a₁) (z₂+a₂)
          (fun w => F (Fin.cons (a₁,a₂) w)) ∂κ 0 z₂ ∂κ 0 z₁
  | n+1, κ, d+1, z₁, z₂, F =>
      ∫ a, markPairPathMean n (fun i => κ (i+1)) d (z₁+a) (z₂+a)
        (fun w => F (Fin.cons (a,a) w)) ∂κ 0 z₁

end InvariantIsing

end

end OAI
