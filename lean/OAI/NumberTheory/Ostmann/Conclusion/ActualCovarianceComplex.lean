import OAI.NumberTheory.Ostmann.Conclusion.ActualCovariance

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Conclusion
open Construction

def actualComplexPermutationCovariance {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    (a b : Γ) : ℂ :=
  (amplitudePrior sources seed giant spectator m l).cmean (fun y =>
    ∑s : AllowedFrequency V l,
      actualCoefficientRow sources seed V giant spectator m X G g bins l
        (amplitudeSamplePermutation sources seed giant spectator m l (σ a) (hσ a) y) s *
      conj (actualCoefficientRow sources seed V giant spectator m X G g bins l
        (amplitudeSamplePermutation sources seed giant spectator m l (σ b) (hσ b) y) s))

theorem actualComplexPermutationCovariance_re {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length)) (hσ) (a b : Γ) :
    (actualComplexPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b).re =
      actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b := by
  simp only [actualComplexPermutationCovariance,actualPermutationCovariance,pairCovariance,
    FinitePrior.cmean,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Fintype.sum_prod_type,Finset.mul_sum]

theorem actualPermutationCovariance_le_of_complex_norm {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length)) (hσ) (a b : Γ)
    {B : ℝ} (hB : ‖actualComplexPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b‖≤B) :
    actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b≤B := by
  rw [←actualComplexPermutationCovariance_re]
  exact (Complex.re_le_norm _).trans hB

end Ostmann.Conclusion

end

end OAI
