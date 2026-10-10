import OAI.NumberTheory.CubicMoment.Estimates.SievedFullModel
import OAI.NumberTheory.CubicMoment.Estimates.CubeMassLogSaving

namespace OAI

/-! The actual positive square-divisor variance has the true squarefree
model mass. This is the positive term of the corrected-square argument. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem sieved_squarefree_model_asymptotic (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ι → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 0)
    (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ (η σ : ℝ) (b G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖sievedDispersionVariance (squarefreeDivisorTruncation ((1+Real.log (L r))^b))
          (fullSquarefreePrimeSupport R (W r) X e) (fullPrimeCoefficient R (W r) X) u V A-
        ((cStar^2*‖dispersionModel (fullSquarefreePrimeSupport R (W r) X e)
            (fullPrimeCoefficient R (W r) X) u‖^2:ℝ):ℂ)*squarefreeModelMass V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨b,K₁,T₁,hK₁,hmass⟩ := cube_mass_fullPrime_log_saving hW hR hlo hhi V hV hVpos hV' k
  obtain ⟨η,σ,hη,hη1,hσ,hfull⟩ := sieved_full_model_asymptotic
    (γ := γ) (ι := ι) hSW hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ V hV hV' k U b
  obtain ⟨G,K₂,T₂,hK₂,hfull⟩ := hfull L W hL hW hlo hhi
  refine ⟨η,σ,b,G,K₁+K₂,max T₁ T₂,hη,hη1,hσ,by positivity,?_⟩
  intro r X A e u hT hprod hrough hAlo hAhi he heN hu
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hAlow : (L r)^(1/2:ℝ) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith)).trans hAlo
  have hm := hmass r X e u A ((le_max_left _ _).trans hT) (hL r) hX hprod hAlow
  have hf := hfull r X A e u ((le_max_right _ _).trans hT) hprod hrough hAlo hAhi he heN hu
  have htri : ∀ a b c : ℂ, ‖a-c‖ ≤ ‖a-b‖+‖b-c‖ := by
    intro a b c
    calc
      _ = ‖(a-b)+(b-c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact (htri _ _ _).trans ((add_le_add hf hm).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
