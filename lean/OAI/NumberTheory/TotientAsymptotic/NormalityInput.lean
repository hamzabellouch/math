import OAI.NumberTheory.TotientAsymptotic.NormalityComplement
import OAI.NumberTheory.TotientAsymptotic.NormalityLargeScale
import OAI.NumberTheory.TotientAsymptotic.NormalityBoundedEndpoint
import OAI.NumberTheory.TotientAsymptotic.NormalityThreshold

namespace OAI

/-! Unconditional proof of the precise exceptional-prime estimate used from
Ford, The distribution of totients, Lemma 2.6. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

 theorem fordLemma26Input : FordLemma26Input := by
  obtain ⟨C,hC,hsmall⟩ := normality_small_parameter
  obtain ⟨D,hD,hmiddle⟩ := normality_middle_parameter
  obtain ⟨E,hE,hlarge⟩ := normality_large_scale
  have hevent : ∀ᶠ N : ℕ in atTop, 400 ≤ B N :=
    (B_tendsto.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 400)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  obtain ⟨F,hF,hfinite⟩ := normality_bounded_endpoint (max M 4) (le_max_right _ _)
  refine ⟨C+D+E+F,by positivity,?_⟩
  intro S hS N hN
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hB : 0 < B N := doubleLog_nat_pos hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let W := (N:ℝ)/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have liftBound (K : ℝ) (hK : K ≤ C+D+E+F)
      (hk : ((nonNormalPrimes S N).card:ℝ) ≤ K*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ)) :
      ((nonNormalPrimes S N).card:ℝ) ≤
        (C+D+E+F)*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
    have hmono := mul_le_mul_of_nonneg_right hK hW
    calc
      _ ≤ K*W := by
        convert hk using 1
        dsimp [W]
        ring
      _ ≤ (C+D+E+F)*W := hmono
      _ = _ := by dsimp [W]; ring
  by_cases hNM : N ≤ max M 4
  · exact liftBound F (by linarith) (hfinite S hS N hN hNM)
  · have hBN : 400 ≤ B N := hM N (by omega)
    by_cases hs : Real.log S ≤ (B N)^30
    · exact liftBound C (by linarith) (hsmall S hS N hN hs)
    · have hBS := normality_large_S_threshold hBN (le_of_not_ge hs)
      obtain ⟨hx,hb,hl⟩ := normality_threshold_conditions hN hBN
      by_cases hm : Real.log S ≤ (Real.log N)^6
      · exact liftBound D (by linarith) (hmiddle S hS hBS N hx hb hl hm)
      · exact liftBound E (by linarith) (hlarge S hS N hN hb (le_of_not_ge hm))

end TotientAsymptotic

end

end OAI
