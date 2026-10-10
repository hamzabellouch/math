import OAI.NumberTheory.TotientAsymptotic.BootstrapNormalized
import OAI.NumberTheory.TotientAsymptotic.BootstrapMajorant
import OAI.NumberTheory.TotientAsymptotic.DyadicEnvelopeMaximum

namespace OAI

/-! The global counting bootstrap from the finite dyadic recurrence. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_envelope_bound : ∃ C : ℝ,0 < C ∧ ∀ J : ℕ,
    dyadicTotientEnvelope J ≤ C*Real.exp (9*(Real.log (1+Real.log ((J:ℝ)+1)))^2) := by
  obtain ⟨A,hA,δ,hδ,hrec⟩ := bootstrap_normalized
  have hsmall := hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and (hsmall.and (bootstrap_majorant_contraction A)))
  let C := max 4 (dyadicTotientEnvelope N)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hC : 0 < C := by linarith
  refine ⟨C,hC,?_⟩
  have hbound : ∀ J : ℕ,dyadicTotientEnvelope J ≤ C*bootstrapMajorant J := by
    intro J
    induction J using Nat.strong_induction_on with
    | h J ih =>
      by_cases hJN : J ≤ N
      · calc
          _ ≤ dyadicTotientEnvelope N := dyadicTotientEnvelope_mono hJN
          _ ≤ C := le_max_right _ _
          _ ≤ _ := by nlinarith [bootstrapMajorant_one_le J]
      · have hNJ : N ≤ J := by omega
        obtain ⟨⟨hK,hKJ,hpoint⟩,hδJ,hcontract⟩ := hN J hNJ
        rcases dyadicTotientEnvelope_maximum J with he|⟨k,hk,he⟩
        · rw [he]
          nlinarith [bootstrapMajorant_one_le J]
        · by_cases hkJ : k < J
          · calc
              _ = V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k := he
              _ ≤ dyadicTotientEnvelope k := dyadicTotientEnvelope_term_le le_rfl
              _ ≤ C*bootstrapMajorant k := ih k hkJ
              _ ≤ _ := mul_le_mul_of_nonneg_left (bootstrapMajorant_mono hk) hC.le
          · have hkEq : k=J := by omega
            subst k
            rw [← he] at hpoint
            have hterm : A*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) ≤
                C*bootstrapMajorant J/4 := by
              calc
                _ ≤ A*(1+Real.log J)^2*(C*bootstrapMajorant (bootstrapIndex J)) :=
                  mul_le_mul_of_nonneg_left (ih _ hKJ) (by positivity)
                _ = C*(A*(1+Real.log J)^2*bootstrapMajorant (bootstrapIndex J)) := by ring
                _ ≤ C*(bootstrapMajorant J/4) := mul_le_mul_of_nonneg_left hcontract hC.le
                _ = _ := by ring
            have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
            have herror := mul_le_mul_of_nonneg_right hδJ.le hE
            have hG := bootstrapMajorant_one_le J
            nlinarith
  intro J
  exact hbound J

end TotientAsymptotic

end

end OAI
