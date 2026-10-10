import OAI.NumberTheory.TotientAsymptotic.FullCoordinateCount
import OAI.NumberTheory.TotientAsymptotic.UniformRegularity
import OAI.NumberTheory.TotientAsymptotic.BootstrapNormalityDecay

namespace OAI

/-! Actual weighted-coordinate violations, with the regularity exceptions included. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem coordinate_violation_count : ∃ C D A F : ℝ,
    0 < C ∧ 0 < D ∧ 0 < A ∧ 0 < F ∧
    ∀ X k K L J : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X → 1 ≤ B X →
    3 ≤ L → L ≤ K → (K:ℝ) ≤ B X+2 → Real.exp K ≤ Real.log X/(20*B X) →
    1 ≤ J → (X:ℝ) ≤ (2:ℝ)^J → ∀ T : ℝ,((L:ℝ)+1)*(k:ℝ)^2 < T →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*B X)/(loglogCutoff L+1:ℕ)+
      A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*
        (Real.log (loglogCutoff L))^(-1/6:ℝ)+
      F*X*k*(K+1:ℕ)^k*Real.exp
        (-T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
          F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
  classical
  obtain ⟨C,D,A,hC,hD,hA,hreg⟩ := uniform_regularity_exception
  obtain ⟨E,F,hE,hF,hcount⟩ := full_coordinate_count
  refine ⟨C,D,A,max E F,hC,hD,hA,lt_max_of_lt_left hE,?_⟩
  intro X k K L J hX hx hBX hL hLK hK hbudget hJ hxJ T hT Q hQ
  let S := loglogCutoff L
  let R := Q.filter (fun v => ¬CountingRegular S X v)
  let G := Q\R
  have hcut := loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
  have hS : 2 < S := by
    have hh := loglogCutoff_ge_four (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
    omega
  have hBS : 0 ≤ B S := by
    have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hcut.2.1]
  have hR := hreg S X J hS hBS hX hx hJ hxJ R (by
    intro v hv
    obtain ⟨hv,hh⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hh⟩)
  have hG := hcount X k K L (by omega) hBX hL hLK hK hbudget T hT G (by
    intro v hv
    obtain ⟨hv,hnR⟩ := Finset.mem_sdiff.mp hv
    have hr : CountingRegular S X v := by
      by_contra hh
      exact hnR (Finset.mem_filter.mpr ⟨hv,hh⟩)
    obtain ⟨n,hn,hφ,hscore⟩ := (hQ v hv).2.2
    exact ⟨n,hn,hφ,(hQ v hv).2.1,hr.1,hr.2.1,(hr.2.2 n hn hφ).1,
      (hr.2.2 n hn hφ).2,hscore⟩)
  have hG' : (G.card:ℝ) ≤ max E F*X*k*(K+1:ℕ)^k*Real.exp
      (-T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
        max E F*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
    apply hG.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left E F) (Nat.cast_nonneg X)) (Nat.cast_nonneg k)) (by positivity)
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right E F) (sq_nonneg ((k:ℝ)+2))]
    · positivity
    · positivity
  have hc : (Q.card:ℝ)=(R.card:ℝ)+(G.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show R ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=R.card+G.card by dsimp [G]; omega)
  rw [hc]
  exact add_le_add hR hG'

end TotientAsymptotic

end

end OAI
