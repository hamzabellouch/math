import OAI.NumberTheory.CubicMoment.Estimates.RepeatedPrimeCutoffEnergy
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionEnergy
import OAI.NumberTheory.CubicMoment.Estimates.PrimarySparseMoment
import OAI.NumberTheory.CubicMoment.Estimates.FirstShapeErrorMoment

namespace OAI

/-! The repeated-prime replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem repeatedPrime_first_shape_cutoff_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primaryPrime a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P Q : Finset Eisenstein),
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/32)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/32)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ B,
        (squarefreeConvolutionError S w b*χ b)*mixedCubic p q b‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*Y^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := first_shape_sparse_mixed_moment
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_cutoff_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P Q hP hQ χ hχ
  have hH : ∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1.1) (hB hb)),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖squarefreeConvolutionError S w b*χ b‖^2) ≤
      (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2)*Y^(1-c/2) :=
    ((coefficient_twist_energy_le B
      (squarefreeConvolutionError S w) χ hχ).trans
      (henergy S w M Y c (by linarith) hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2) hY (by positivity) P Q
    B hP hQ hH (fun b => squarefreeConvolutionError S w b*χ b)
    hE).trans_eq (by ring)


theorem repeatedPrime_balanced_cutoff_moment (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primaryPrime a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+c/32) ∧
        norm p.2 ≤ Y^(1/3+c/32)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ B,
        (squarefreeConvolutionError S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*Y^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := primary_balanced_sparse_moment hHuxley
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_cutoff_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P hP χ hχ
  have hH : ∀ b ∈ B, primary b ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1.1) (hB hb),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖squarefreeConvolutionError S w b*χ b‖^2) ≤
      (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2)*Y^(1-c/2) :=
    ((coefficient_twist_energy_le B
      (squarefreeConvolutionError S w) χ hχ).trans
      (henergy S w M Y c (by linarith) hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2) hY (by positivity) B hH P hP
    (fun b => squarefreeConvolutionError S w b*χ b) hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
