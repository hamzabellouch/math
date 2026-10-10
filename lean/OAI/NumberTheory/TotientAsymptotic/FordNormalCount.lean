import OAI.NumberTheory.TotientAsymptotic.NormalBandExponent
import OAI.NumberTheory.TotientAsymptotic.SmallIntervalPart

namespace OAI

/-! The normal-value upper count, with the exponent in Ford's coefficient form. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem ford_normal_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℕ),2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    1 ≤ B X → Real.log z ≤ Real.log X/(20*B X) →
    (∀ j < k,Y (j+1) ≤ Y j) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
      ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*Real.exp
      (-(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := normal_preimage_band_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y hS hSz hY0 hYS hBX hcut hY Q hQ
  have hX : 0 < X := by
    by_contra! hh
    have hz : X=0 := Nat.eq_zero_of_le_zero hh
    subst X
    norm_num [B] at hBX
  have hb := hbound S X z k Y hS hSz hY0 hYS hY Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnormal,hprefix⟩ := hQ v hv
    exact ⟨n,hn,hφ,hvX,ford_interval_part_sieve_size hSz (by omega) hBX hΩ hcut hX,
      hsqv,hsqn,hnormal,hprefix⟩)
  have he := normal_band_count_scale hS (hS.trans hSz) D k Y hY0 hYS
  calc
    _ ≤ C*X*Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y) := hb
    _ = C*X*(Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y)) := by ring
    _ = _ := by rw [he]

end TotientAsymptotic

end

end OAI
