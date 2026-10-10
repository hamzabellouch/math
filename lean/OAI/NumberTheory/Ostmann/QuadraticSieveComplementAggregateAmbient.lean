import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateAmbientPower

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem complementary_corrections_aggregate_ambient (W : 𝓢(ℝ,ℂ)) (I : ℂ) {ξ : ℝ}
    (hξ1 : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ ε/16 → ∀ (P M T : ℝ) (K Δ N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ P → 1 ≤ M → (N:ℝ) ≤ P → 0 < K → 0 < Δ → 0 < N →
      (K:ℝ) ≤ P^3 → T = P^η → S ⊆ oddSquarefreeUpTo N →
      ‖complementaryLargeCorrection M I K Δ N S a (complementWindowUpper M T)‖ ≤
        C*P^ε*(Δ:ℝ)^2*
          ((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a ∧
      ‖complementaryFourierCorrection W M K Δ N S a (complementWindowLower M T)
        (complementWindowUpper M T) (fun _ => 16*T^2)‖ ≤
        C*P^ε*(Δ:ℝ)^2*
          ((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  obtain ⟨Cr,hCr,hbound⟩ := complement_kernel_power_bound_ambient hξ1 hξ2 hξ ε hε
  let C : ℝ := (‖I‖+33*complementFourierBound W+1)*Cr
  have hCW := complementFourierBound_pos W
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro η hη hηδ P M T K Δ N S a hP hM hNP hK hΔ hN hKbound hT hS
  have hMp : 0 < M := by linarith
  have hP1 := hP
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_rpow hP1 hη.le
  have hT2 : 1 ≤ T^2 := by nlinarith
  have hE := coefficientEnergy_nonneg S a
  have hlarge := hbound η hη hηδ P M T 1 K Δ N S a (complementLargeScalar M T Δ) hP hM hNP (by norm_num)
    hK hΔ hN hKbound hT hS
    (fun r hr d v hv => (complementLargeScalar_norm_le M T Δ r d v).trans (by simpa using hT2))
    (fun r hr d v hv hnz => complementLargeScalar_support hMp hT1 (mem_oddSquarefreeUpTo.mp hv).1 hnz)
  have hfourier := hbound η hη hηδ P M T (33*complementFourierBound W) K Δ N S a
    (complementFourierScalar W M T Δ) hP hM hNP (by positivity) hK hΔ hN hKbound hT hS
    (fun r hr d v hv => complementFourierScalar_norm_le_window W M T hT1 Δ r d v)
    (fun r hr d v hv hnz => complementFourierScalar_support W hnz)
  have hcI : ‖I‖*Cr ≤ C := by dsimp [C]; nlinarith
  have hcW : Cr*(33*complementFourierBound W) ≤ C := by
    dsimp [C]
    nlinarith [norm_nonneg I]
  constructor
  · rw [complementaryLargeCorrection_eq_scalar]
    change ‖-I*complementKernelSum M K Δ N S a (complementLargeScalar M T Δ)‖ ≤ _
    rw [norm_mul,norm_neg]
    refine (mul_le_mul_of_nonneg_left hlarge (norm_nonneg I)).trans ?_
    have hh := mul_le_mul_of_nonneg_right hcI
      (show 0 ≤ P^ε*(Δ:ℝ)^2*
        ((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a by positivity)
    convert hh using 1 <;> ring
  · rw [complementaryFourierCorrection_eq_scalar]
    change ‖(1/2:ℂ)*complementKernelSum M K Δ N S a (complementFourierScalar W M T Δ)‖ ≤ _
    have hh : ‖(1/2:ℂ)*complementKernelSum M K Δ N S a (complementFourierScalar W M T Δ)‖ ≤
        ‖complementKernelSum M K Δ N S a (complementFourierScalar W M T Δ)‖ := by
      rw [norm_mul]
      have hc : ‖(1/2:ℂ)‖ ≤ 1 := by norm_num
      exact mul_le_of_le_one_left (norm_nonneg _) hc
    refine (hh.trans hfourier).trans ?_
    have hb := mul_le_mul_of_nonneg_right hcW
      (show 0 ≤ P^ε*(Δ:ℝ)^2*
        ((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a by positivity)
    convert hb using 1 <;> ring

end Ostmann.QuadraticSieve

end

end OAI
