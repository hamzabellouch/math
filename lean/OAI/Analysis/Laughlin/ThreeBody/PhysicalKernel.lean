import OAI.Analysis.Laughlin.ThreeBody.SpinCovariance

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def threeWedge (Q : ℕ) (u : Spin.PairOrbitalIndex Q → ℂ) : Space Q :=
  ∑ a, u a • threeBodyColumn Q a.1.val a.2

noncomputable def complexThreeGram (Q : ℕ) :
    Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ :=
  fun a b => (Spin.threeGram Q a b : ℂ)

theorem threeWedge_inner (Q : ℕ) (hQ : 2 ≤ Q) (u v : Spin.PairOrbitalIndex Q → ℂ) :
    occupationInner Q (threeWedge Q u) (threeWedge Q v) =
      ∑ a, star (u a)*(complexThreeGram Q *ᵥ v) a := by
  unfold threeWedge
  rw [occupationInner_sum_left]
  simp_rw [occupationInner_smul_left,occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,complexThreeGram]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Spin.threeGram_physical Q hQ a b]
  ring

theorem threeWedge_zero_of_gram_zero (Q : ℕ) (hQ : 2 ≤ Q) (u : Spin.PairOrbitalIndex Q → ℂ)
    (hu : complexThreeGram Q *ᵥ u=0) : threeWedge Q u=0 := by
  apply (occupationNormSq_eq_zero Q _).mp
  apply Complex.ofReal_injective
  rw [← occupationInner_self,threeWedge_inner Q hQ,hu]
  simp

theorem complexThreeGram_apply (Q : ℕ) (hQ : 2 ≤ Q) (u : Spin.PairOrbitalIndex Q → ℂ)
    (a : Spin.PairOrbitalIndex Q) :
    (complexThreeGram Q *ᵥ u) a = occupationInner Q (threeBodyColumn Q a.1.val a.2) (threeWedge Q u) := by
  unfold threeWedge
  rw [occupationInner_sum_right]
  simp only [occupationInner_smul_right,Matrix.mulVec,dotProduct,complexThreeGram]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Spin.threeGram_physical Q hQ a b]
  ring

theorem threeWedge_kernel_iff (Q : ℕ) (hQ : 2 ≤ Q) (u : Spin.PairOrbitalIndex Q → ℂ) :
    threeWedge Q u=0 ↔ complexThreeGram Q *ᵥ u=0 := by
  constructor
  · intro hu
    funext a
    rw [complexThreeGram_apply Q hQ,hu]
    simp [occupationInner]
  · exact threeWedge_zero_of_gram_zero Q hQ u

end Laughlin.Fock

end OAI
