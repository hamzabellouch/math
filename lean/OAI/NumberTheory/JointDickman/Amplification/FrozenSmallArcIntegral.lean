import OAI.NumberTheory.JointDickman.Amplification.SmallArcModel
import OAI.NumberTheory.JointDickman.Counting.CoefficientFourierContinuity
import OAI.NumberTheory.JointDickman.Counting.FrozenCoefficientLaw
import OAI.NumberTheory.JointDickman.Amplification.SchwartzFourierProfile

namespace OAI

/-! # The coefficient expansion integrated on the retained arcs -/

namespace JointDickman
open Filter MeasureTheory Function
open scoped Topology ArithmeticFunction.Moebius SchwartzMap FourierTransform

theorem schwartz_testFourier_continuous (w : 𝓢(ℝ,ℝ)) : Continuous (testFourierTransform w) := by
  let f : 𝓢(ℝ,ℂ) := w.postcompCLM Complex.ofRealCLM
  have he : testFourierTransform w = (⇑(𝓕 f : 𝓢(ℝ,ℂ))) := by
    rw [testFourierTransform_eq_fourier,SchwartzMap.fourier_coe]
    rfl
  rw [he]
  exact (𝓕 f : 𝓢(ℝ,ℂ)).continuous

theorem coefficient_frozen_smallMajorArc_integral_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) →
      ∀ F G : ℝ → ℂ, Continuous F → Continuous G → Periodic F 1 → Periodic G 1 →
      ‖(∫ x in smallMajorArcRegion B j X Q,
          F x*G x*smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)-
        smallMajorArcModel B j X Q (fun x => F x*G x) ((fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ))
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        (X*((K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*(B : ℝ)^(-50 : ℝ)+C*M/B))/2*
          ((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2)) := by
  obtain ⟨c,hc,hcpos,H,K,hK,hcoeff⟩ := coefficient_frozen_majorArc_law hSD hSW hM hMP
  refine ⟨c,hc,hcpos,H,K,hK,?_⟩
  intro a b ha hab
  obtain ⟨C,hC,hcoeff⟩ := hcoeff a b ha hab
  refine ⟨C,hC,?_⟩
  filter_upwards [hcoeff,smallMajorArc_energy_approximation,eventually_ge_atTop 1]
    with B hcoeffB happrox hB
  intro X hX hlog j hj Q w w' M N hM0 hN0 hw hw' hwb hw'b hsupp F G hF hG hpF hpG
  let : NeZero j := hj
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hCoeff : Continuous (fun x => smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w) :=
    (smoothCoefficientAdditiveSum_continuous B ha.le hab hX hsupp).comp
      (continuous_const.mul continuous_id)
  have hW : Continuous (fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ) :=
    continuous_const.mul (schwartz_testFourier_continuous w)
  let D : ℝ := K*b*(2*M+(N+2*Real.pi*M)*(b-a))
  have hD : 0 ≤ D := by dsimp [D]; have hb := ha.trans_le hab; positivity
  have hbound := happrox X hX hlog.1 j hj Q F G
    (fun x => smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)
    ((fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ)) hF hG hCoeff hW hpF hpG
    ((hpF.mul hpG).mul (smoothCoefficientAdditiveSum_periodic B j X w))
    (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))
    (X*(D*(B : ℝ)^(-50 : ℝ)+C*M/B)) (by positivity) (by
      intro q hq _hqQ h hh ξ hξ
      have hq12 : (q : ℝ) ≤ (B : ℝ)^12 := by
        exact_mod_cast (mem_positiveDenominators (B^12) q).mp hq
      have hq15 : (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) := by
        rw [Real.rpow_ofNat]
        exact hq12.trans (pow_le_pow_right₀ hB1 (by norm_num : 12 ≤ 15))
      have hξ14 : |ξ| ≤ (B : ℝ)^(14 : ℝ) := by
        rw [Real.rpow_ofNat]
        exact hξ.trans (pow_le_pow_right₀ hB1 (by norm_num : 13 ≤ 14))
      let p := (arcLiftEquiv j (q : ℕ)).symm h
      have he : arcLiftEquiv j (q : ℕ) p = h := (arcLiftEquiv j (q : ℕ)).apply_symm_apply h
      have hr : p.2.val.Coprime (q : ℕ) :=
        (arcLiftEquiv_coprime p.1 p.2).mp (by rw [he]; exact hh)
      have ht := hcoeffB X hX hlog j (q : ℕ) hq15 p.1 p.2 hr
        w w' M N ξ hM0 hN0 hw hw' hwb hw'b hsupp hξ14
      rw [he] at ht
      exact ht)
  exact hbound

end JointDickman

end OAI
