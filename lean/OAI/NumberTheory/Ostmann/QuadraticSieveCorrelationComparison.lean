import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelations
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementNegligibleAmbient
import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsTransform
import OAI.NumberTheory.Ostmann.QuadraticSieveDualRemainderNegligible
import OAI.NumberTheory.Ostmann.QuadraticSieveDualTailNegligible
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingBootstrap

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap

theorem correlation_difference_le_components (W : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ)
    (hΔ0 : Δ ≠ 0) (hΔ : Odd Δ) (S : Finset ℕ) (a : ℕ → ℂ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) (Y₁ Y₂ J : ℕ → ℝ)
    (hS : S ⊆ oddSquarefreeUpTo N) (hS1 : ∀ n ∈ S, 1 < n)
    (hcop : ∀ n ∈ S, Nat.Coprime n Δ) :
    ‖dualCorrelation W M Δ S a - complementaryCorrelation W M K Δ S a‖ ≤
      ‖dualLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a -
        complementLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a‖ +
      ‖dualCorrelationZeroCorrection W M Δ K S a X₂‖ +
      ‖dualCorrelationLargeCorrection W M Δ K S a X₂‖ +
      ‖dualCorrelationFourierCorrection W M Δ K S a X₁ X₂ L‖ +
      ‖complementaryLargeCorrection M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ N S a Y₂‖ +
      ‖complementaryFourierCorrection W M K Δ N S a Y₁ Y₂ J‖ +
      ‖dualCorrelationRemainder W M Δ K S a X₁ X₂ L‖ +
      ‖dualCorrelationTail W M Δ K S a‖ +
      ‖complementaryCorrelation W M K Δ S a -
        complementaryCorrelationMain W M K Δ S a Y₁ Y₂ J‖ := by
  have hd := dualCorrelation_full_transform W hc hs M hM Δ K N hΔ0 hΔ S a X₁ X₂ L hS hS1
  have he := complementaryCorrelationMain_eq_of_oddSquarefree W hs M K Δ N S a Y₁ Y₂ J hS hcop
  let dL := dualLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a
  let cL := complementLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a
  let dZ := dualCorrelationZeroCorrection W M Δ K S a X₂
  let dG := dualCorrelationLargeCorrection W M Δ K S a X₂
  let dF := dualCorrelationFourierCorrection W M Δ K S a X₁ X₂ L
  let cG := complementaryLargeCorrection M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ N S a Y₂
  let cF := complementaryFourierCorrection W M K Δ N S a Y₁ Y₂ J
  let dR := dualCorrelationRemainder W M Δ K S a X₁ X₂ L
  let dT := dualCorrelationTail W M Δ K S a
  let cR := complementaryCorrelation W M K Δ S a - complementaryCorrelationMain W M K Δ S a Y₁ Y₂ J
  have hx : dualCorrelation W M Δ S a - complementaryCorrelation W M K Δ S a =
      ((((((((dL-cL)+dZ)+dG)+dF)-cG)-cF)+dR)+dT)-cR := by
    dsimp [dL,cL,dZ,dG,dF,cG,cF,dR,dT,cR]
    rw [hd,he]
    ring
  rw [hx]
  change ‖((((((((dL-cL)+dZ)+dG)+dF)-cG)-cF)+dR)+dT)-cR‖ ≤
    ‖dL-cL‖+‖dZ‖+‖dG‖+‖dF‖+‖cG‖+‖cF‖+‖dR‖+‖dT‖+‖cR‖
  calc
    _ ≤ ‖(((((((dL-cL)+dZ)+dG)+dF)-cG)-cF)+dR)+dT‖+‖cR‖ := norm_sub_le _ _
    _ ≤ (‖((((((dL-cL)+dZ)+dG)+dF)-cG)-cF)+dR‖+‖dT‖)+‖cR‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖(((((dL-cL)+dZ)+dG)+dF)-cG)-cF‖+‖dR‖)+‖dT‖)+‖cR‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖((((dL-cL)+dZ)+dG)+dF)-cG‖+‖cF‖)+‖dR‖)+‖dT‖)+‖cR‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((((‖(((dL-cL)+dZ)+dG)+dF‖+‖cG‖)+‖cF‖)+‖dR‖)+‖dT‖)+‖cR‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (((((‖((dL-cL)+dZ)+dG‖+‖dF‖)+‖cG‖)+‖cF‖)+‖dR‖)+‖dT‖)+‖cR‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((((((‖(dL-cL)+dZ‖+‖dG‖)+‖dF‖)+‖cG‖)+‖cF‖)+‖dR‖)+‖dT‖)+‖cR‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

end Ostmann.QuadraticSieve

end OAI
