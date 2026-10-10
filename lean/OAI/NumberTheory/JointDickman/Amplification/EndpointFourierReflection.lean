import OAI.NumberTheory.JointDickman.Probability.EndpointFourierMoments

namespace OAI

/-! # Reflecting the second endpoint in the Fourier integral -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem finiteAdditiveSum_neg_real (s : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    finiteAdditiveSum s (fun n => (c n : ℂ)) (-θ) =
      conj (finiteAdditiveSum s (fun n => (c n : ℂ)) θ) := by
  unfold finiteAdditiveSum
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

theorem endpointFourierSum_neg_norm (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    ‖endpointFourierSum B a b X g w (-θ)‖ = ‖endpointFourierSum B a b X g w θ‖ := by
  unfold endpointFourierSum
  rw [finiteAdditiveSum_neg_real]
  exact Complex.norm_conj _

theorem endpointFourierSum_continuous (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Continuous (endpointFourierSum B a b X g w) :=
  finiteAdditiveSum_continuous _ _

end JointDickman

end OAI
