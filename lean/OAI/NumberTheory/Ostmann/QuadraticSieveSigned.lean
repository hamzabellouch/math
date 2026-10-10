import OAI.NumberTheory.Ostmann.QuadraticSieveSignedSupport

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def signedJacobiEnergy (U : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ u ∈ signedSquarefreeUpTo U, ‖∑ s ∈ S, a s * (jacobiSym u s : ℂ)‖ ^ 2

private theorem nonneg_sum_biUnion_le {ι κ : Type*} [DecidableEq κ] (C : Finset ι) (V : ι → Finset κ)
    (f : κ → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ v ∈ C.biUnion V, f v) ≤ ∑ c ∈ C, ∑ v ∈ V c, f v := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | @insert c C hc ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hc]
    have hunion : (∑ v ∈ V c ∪ C.biUnion V, f v) +
        (∑ v ∈ V c ∩ C.biUnion V, f v) =
        (∑ v ∈ V c, f v) + (∑ v ∈ C.biUnion V, f v) := Finset.sum_union_inter
    have hinter : 0 ≤ ∑ v ∈ V c ∩ C.biUnion V, f v :=
      Finset.sum_nonneg (fun v _ => hf v)
    linarith

theorem signedJacobiEnergy_le_four_numeratorEnergies (U : ℕ) (S : Finset ℕ)
    (a : ℕ → ℂ) :
    signedJacobiEnergy U S a ≤
      ∑ c ∈ signedSquarefreeMultipliers, numeratorEnergy c (oddSquarefreeUpTo U) S a := by
  classical
  let F : ℤ → ℝ := fun u => ‖∑ s ∈ S, a s * (jacobiSym u s : ℂ)‖ ^ 2
  calc
    signedJacobiEnergy U S a ≤
        ∑ u ∈ signedSquarefreeMultipliers.biUnion
          (fun c => (oddSquarefreeUpTo U).image (fun v : ℕ => c * (v : ℤ))), F u :=
      Finset.sum_le_sum_of_subset_of_nonneg (signedSquarefreeUpTo_subset_biUnion U)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ c ∈ signedSquarefreeMultipliers,
        ∑ u ∈ (oddSquarefreeUpTo U).image (fun v : ℕ => c * (v : ℤ)), F u :=
      nonneg_sum_biUnion_le _ _ F (fun _ => sq_nonneg _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_image (signedSquarefreeMultiplier_injective hc).injOn]
      rfl

theorem signedJacobiEnergy_le_of_unsigned (U : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ s ∈ S, Odd s) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ b : ℕ → ℂ,
      jacobiEnergy (oddSquarefreeUpTo U) S b ≤ K * coefficientEnergy S b) :
    signedJacobiEnergy U S a ≤ 8 * K * coefficientEnergy S a := by
  calc
    signedJacobiEnergy U S a ≤
        ∑ c ∈ signedSquarefreeMultipliers, numeratorEnergy c (oddSquarefreeUpTo U) S a :=
      signedJacobiEnergy_le_four_numeratorEnergies U S a
    _ ≤ ∑ c ∈ signedSquarefreeMultipliers, 2 * K * coefficientEnergy S a := by
      apply Finset.sum_le_sum
      intro c hc
      exact numeratorEnergy_le_of_unsigned _ S a c
        (fun v hv => (mem_oddSquarefreeUpTo.mp hv).2.2.1) hS hK hbound
    _ = _ := by simp only [Finset.sum_const, card_signedSquarefreeMultipliers, nsmul_eq_mul]; ring

end Ostmann.QuadraticSieve

end OAI
