import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateKernels
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem complement_frequency_card_le {L : ℝ} (hL : 0 ≤ L) :
    ((nonzeroIntegerCutoff L).card:ℝ) ≤ 2*L+1 := by
  have hf : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
  have hc : ⌈-L⌉ ≤ ⌊L⌋+1 := by rw [Int.ceil_neg]; omega
  have hi := Int.card_Icc_of_le _ _ hc
  rw [Int.ceil_neg] at hi
  have hir : ((Finset.Icc ⌈-L⌉ ⌊L⌋).card:ℝ) = 2*(⌊L⌋:ℝ)+1 := by
    rw [Int.ceil_neg]
    have hh : ((Finset.Icc (-⌊L⌋) ⌊L⌋).card:ℝ) = (⌊L⌋:ℝ)+1-(-(⌊L⌋:ℝ)) := by
      exact_mod_cast hi
    linarith
  have he : (nonzeroIntegerCutoff L).card ≤ (Finset.Icc ⌈-L⌉ ⌊L⌋).card := Finset.card_erase_le
  calc
    _ ≤ ((Finset.Icc ⌈-L⌉ ⌊L⌋).card:ℝ) := by exact_mod_cast he
    _ ≤ 2*L+1 := by rw [hir]; linarith [Int.floor_le L]

theorem complement_frequency_card_window {T : ℝ} (hT : 1 ≤ T) :
    ((nonzeroIntegerCutoff (16*T^2)).card:ℝ) ≤ 33*T^2 := by
  have hh := complement_frequency_card_le (show 0 ≤ 16*T^2 by positivity)
  nlinarith

theorem complementFourierScalar_norm_le_window (W : 𝓢(ℝ,ℂ)) (M T : ℝ)
    (hT : 1 ≤ T) (Δ r d v : ℕ) :
    ‖complementFourierScalar W M T Δ r d v‖ ≤ (33*complementFourierBound W)*T^2 := by
  refine (complementFourierScalar_norm_le W M T Δ r d v).trans ?_
  have hh := mul_le_mul_of_nonneg_left (complement_frequency_card_window hT)
    (complementFourierBound_pos W).le
  convert hh using 1
  ring

theorem complement_aggregate_growth (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (K N : ℕ), 1 ≤ P → 0 < K → 0 < N →
      (N:ℝ) ≤ P → (K:ℝ) ≤ P^3 →
      (Nat.log 2 K+1:ℕ)*(Nat.log 2 (N^2)+2:ℕ)*(2*(K:ℝ)*N)^δ*(N:ℝ)^δ*(P^δ)^3 ≤
        C*P^(13*δ) := by
  obtain ⟨C,hC,hdepth⟩ := squarefree_dyadic_depth_le_rpow δ hδ
  refine ⟨2*C^2*(2:ℝ)^δ,by positivity,?_⟩
  intro P K N hP hK hN hNP hKP
  have hPp : 0 < P := by linarith
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hdk := hdepth K hK
  have hdn := hdepth (N^2) (by positivity)
  have hdn' : (Nat.log 2 (N^2)+2:ℕ) ≤ 2*C*(N:ℝ)^(2*δ) := by
    have hdle : (Nat.log 2 (N^2)+2:ℕ) ≤ 2*(Nat.log 2 (N^2)+1) := by omega
    have hcast : ((Nat.log 2 (N^2)+2:ℕ):ℝ) ≤ 2*((Nat.log 2 (N^2)+1:ℕ):ℝ) := by exact_mod_cast hdle
    have hp : ((N^2:ℕ):ℝ)^δ = (N:ℝ)^(2*δ) := by
      rw [Nat.cast_pow,← Real.rpow_natCast (N:ℝ) 2,← Real.rpow_mul hNp.le]
      norm_num
    rw [hp] at hdn
    nlinarith
  have hKpow : (K:ℝ)^δ ≤ P^(3*δ) := by
    have hh := Real.rpow_le_rpow hKr.le hKP hδ.le
    rwa [← Real.rpow_natCast P 3,← Real.rpow_mul hPp.le] at hh
  have hNpow : (N:ℝ)^δ ≤ P^δ := Real.rpow_le_rpow hNp.le hNP hδ.le
  have hN2pow : (N:ℝ)^(2*δ) ≤ P^(2*δ) := Real.rpow_le_rpow hNp.le hNP (by positivity)
  have hprod : (2*(K:ℝ)*N)^δ ≤ (2:ℝ)^δ*P^(4*δ) := by
    have hb : 2*(K:ℝ)*N ≤ 2*P^4 := by nlinarith [mul_le_mul hKP hNP hNp.le (by positivity)]
    have hh := Real.rpow_le_rpow (by positivity) hb hδ.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),
      ← Real.rpow_natCast P 4,← Real.rpow_mul hPp.le] at hh
    exact hh
  have hdK : (Nat.log 2 K+1:ℕ) ≤ C*P^(3*δ) := hdk.trans (mul_le_mul_of_nonneg_left hKpow hC.le)
  have hdN : (Nat.log 2 (N^2)+2:ℕ) ≤ 2*C*P^(2*δ) :=
    hdn'.trans (mul_le_mul_of_nonneg_left hN2pow (by positivity))
  calc
    _ ≤ (C*P^(3*δ))*(2*C*P^(2*δ))*((2:ℝ)^δ*P^(4*δ))*P^δ*(P^δ)^3 := by
      gcongr
    _ = (2*C^2*(2:ℝ)^δ)*(P^(3*δ)*P^(2*δ)*P^(4*δ)*P^δ*P^(3*δ)) := by
      rw [← Real.rpow_mul_natCast hPp.le]
      norm_num
      ring_nf
    _ = _ := by
      rw [← Real.rpow_add hPp,← Real.rpow_add hPp,← Real.rpow_add hPp,← Real.rpow_add hPp]
      congr 2
      ring

end Ostmann.QuadraticSieve

end

end OAI
