import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateAmbient
import OAI.NumberTheory.Ostmann.QuadraticSieveCorrelationComparison
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierAmbient
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLarge

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap

theorem correlation_difference_bootstrap (W : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P H : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ M → M ≤ P → 1 ≤ P → 0 < H → 0 < K → 0 < Δ → 0 < N →
      (K : ℝ) ≤ P^3 → (Δ : ℝ) ≤ P → (N : ℝ) ≤ M → (N : ℝ) ≤ 2*H →
      Odd Δ → Δ ≤ N → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, Nat.Coprime n Δ) →
      (∀ n ∈ S, 1 < n) → (∀ n ∈ S, H ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*H) →
      ((2*Δ : ℕ) : ℝ)*(N : ℝ)^2/M*P^η ≤ K → Real.sqrt (M/K)*N ≤ M →
      ‖dualCorrelation W M Δ S a - complementaryCorrelation W M K Δ S a‖ ≤
        C*P^ε*(Δ : ℝ)^4*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  let I : ℂ := ∫ x : ℝ in Ioi 0, W (x^2)
  obtain ⟨Cl,hCl,hleading⟩ := leading_correlations_bootstrap hξ1 hξ2 hξ ε hε
  obtain ⟨Cz,hCz,hzero⟩ := dual_zero_correction_ambient W hξ1 hξ2 hξ ε hε
  obtain ⟨Cg,hCg,hlarge⟩ := dual_large_correction_ambient W hξ1 hξ2 hξ ε hε
  obtain ⟨Cf,hCf,hfourier⟩ := dual_fourier_correction_aggregate_ambient W hξ1 hξ2 hξ ε hε
  obtain ⟨Cc,hCc,hcomplement⟩ := complementary_corrections_aggregate_ambient W I hξ1.le hξ2 hξ ε hε
  obtain ⟨Cr,hCr,hremainder⟩ := dualCorrelationRemainder_negligible W η hη
  obtain ⟨Ct,hCt,htail⟩ := dualCorrelationTail_negligible W η hη
  obtain ⟨Ce,hCe,herror⟩ := complementaryCorrelation_negligible_ambient W η hη
  refine ⟨Cl*‖I‖+Cz+Cg+Cf+2*Cc+Cr+Ct+Ce,by positivity,?_⟩
  intro M P H K Δ N S a hM hMP hP hH hK hΔ hN hKP hΔP hNM hNH hodd hΔN hS hcop hS1 hSH hcut hsqrt
  have hMp : 0 < M := by linarith
  have hNP : (N : ℝ) ≤ P := hNM.trans hMP
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔ24 : (Δ : ℝ)^2 ≤ (Δ : ℝ)^4 := by
    have hh : 1 ≤ (Δ : ℝ)^2 := one_le_pow₀ hΔ1
    nlinarith [sq_nonneg ((Δ : ℝ)^2-1)]
  have hE := coefficientEnergy_nonneg S a
  let B : ℝ := P^ε*(Δ : ℝ)^4*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))
  have hB : 1 ≤ B := by
    dsimp [B]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hP hε.le) (one_le_pow₀ hΔ1))
      (hM.trans (le_add_of_nonneg_right (by positivity)))
  have hsmall (c : ℝ) (hc : 0 ≤ c) : c*coefficientEnergy S a ≤ c*B*coefficientEnergy S a :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc hB) hE
  have hadapt (c : ℝ) (hc : 0 ≤ c) :
      c*P^ε*(Δ : ℝ)^2*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a ≤
        c*B*coefficientEnergy S a := by
    dsimp [B]
    simp only [← mul_assoc]
    gcongr
  have hadaptN (c : ℝ) (hc : 0 ≤ c) :
      c*P^ε*(Δ : ℝ)^2*((N : ℝ)+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a ≤
        c*B*coefficientEnergy S a := by
    dsimp [B]
    simp only [← mul_assoc]
    gcongr
  have hl := hleading M P I K Δ N hM hP hK hΔ hN hKP hΔP hNP hodd hΔN S a hS hcop hsqrt
  have hl' : ‖dualLeadingCorrelation M I K Δ S a - complementLeadingCorrelation M I K Δ S a‖ ≤
      (Cl*‖I‖)*B*coefficientEnergy S a := by simpa only [B,mul_assoc] using hl
  have hz := (hzero M H P η Δ K N S a hM hH hP hη hηε hΔ hK hN hNP hKP hNH hS
    (fun n hn => (hSH n hn).1)).trans (hadapt Cz hCz.le)
  have hg := (hlarge M H P η Δ K N S a hM hH hP hη hηε hΔ hK hN hNP hKP hNH hS
    (fun n hn => (hSH n hn).1)).trans (hadapt Cg hCg.le)
  have hf := (hfourier η hη hηε P M H (P^η) K Δ N S a hP hM hMP hH hK hΔ hN hNP hKP
    rfl hNH hS (fun n hn => (hSH n hn).1)).trans (hadapt Cf hCf.le)
  have hη16 : η ≤ ε/16 := by linarith
  obtain ⟨hcg,hcf⟩ := hcomplement η hη hη16 P M (P^η) K Δ N S a hP hM hNP hK hΔ hN hKP rfl hS
  have hcg' := hcg.trans (hadaptN Cc hCc.le)
  have hcf' := hcf.trans (hadaptN Cc hCc.le)
  have hr := (hremainder M P H Δ K N S a hM hMP hP hH hΔP hNP hKP hS hS1 hSH).trans
    (hsmall Cr hCr.le)
  have ht := (htail M P K Δ N S a hM hP hΔ hN hΔP hNP hcut hS).trans (hsmall Ct hCt.le)
  have he := (herror M P K Δ N S a hM hMP hP hNP hKP hΔ.ne'
    (fun n hn => ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1,(mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩)).trans
      (hsmall Ce hCe.le)
  have hcomparison := correlation_difference_le_components W hc hs M hMp Δ K N hΔ.ne' hodd S a
    (dualWindowLower M H (P^η)) (dualWindowUpper M H (P^η)) (fun _ _ => 16*(P^η)^2)
    (complementWindowLower M (P^η)) (complementWindowUpper M (P^η)) (fun _ => 16*(P^η)^2)
    hS hS1 hcop
  have hfinal : ‖dualCorrelation W M Δ S a - complementaryCorrelation W M K Δ S a‖ ≤
      (Cl*‖I‖+Cz+Cg+Cf+2*Cc+Cr+Ct+Ce)*B*coefficientEnergy S a := by
    dsimp only [I] at hl' hcg' hcomparison ⊢
    linarith
  simpa only [B,mul_assoc] using hfinal

end Ostmann.QuadraticSieve

end OAI
