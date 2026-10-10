import OAI.NumberTheory.JointDickman.Amplification.EndpointFullArcLaw
import OAI.NumberTheory.JointDickman.Counting.CoefficientArcErrorScale
import OAI.NumberTheory.JointDickman.Amplification.GeometricDiscardedArcs
import OAI.NumberTheory.JointDickman.Amplification.FullSpatialComparison

namespace OAI

/-! # The actual retained coefficient integrals, summed over geometric boxes -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

noncomputable def geometricSmallArcSum (B j Q : ℕ) (a b T t : ℝ)
    (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ w : ℝ → ℝ) : ℂ :=
  (B : ℂ)*∑ k ∈ S, ∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ

theorem geometric_coefficient_law_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) {M M₀ D₀ : ℝ}
    (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → η*T ≤ B → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      T*‖geometricSmallArcSum B j Q a b T t S g h w₁ w₂ w-
        geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨c,hc,hcpos,H,K,C,C₁,C₂,hK,hC,hC₁,hC₂,he⟩ :=
    endpoint_fullArc_coefficient_law hSD hSW hM hMP ha hab hl hlu
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  let A := K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l))
  let G := D*(∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)
  let Cerror := (C₂*M^2)*(A+C*M₀)+2*(C₁*M)^2*G/η
  have hA : 0 ≤ A := by dsimp [A]; have hu := hl.trans_le hlu; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp [Cerror]; positivity
  let ε := fun B : ℕ => ((8/(5*t)+1)*Cerror)*(B : ℝ)^((-(3/2 : ℝ))+1)
  refine ⟨c,hc,hcpos,H,ε,geometric_box_error_vanishing ht (by norm_num),?_⟩
  filter_upwards [he,hden,eventually_ge_atTop 1] with B heB hdenB hB
  intro T hT hscale S hbox hlog j _ Q g h hg hh
  dsimp only
  let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
  let I := fun k : ℤ => ∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ
  let P := fun k : ℤ => fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
    (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
      endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
    (fun ξ => (d k : ℂ)*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))
  let E := fun k : ℤ => (B : ℂ)*(I k-P k)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hBr
  have hN (k : ℤ) : T*(Real.exp ((k : ℝ)*t)/T) = Real.exp ((k : ℝ)*t) := by field_simp
  have hlocal : ∀ k ∈ S, T*‖E k‖ ≤ Cerror*(B : ℝ)^(-(3/2 : ℝ)) := by
    intro k hk
    have hdk : |d k| ≤ D := by
      apply hdenB.1
      apply (le_div_iff₀ hBpos).mpr
      nlinarith [(hlog k hk).1]
    have hNk : Real.log (T*(Real.exp ((k : ℝ)*t)/T)) ∈
        Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) := by
      rw [hN,Real.log_exp]
      exact hbox k hk
    have hh := heB T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk) hNk j Q g h hg hh w₁ w₂ w w' M M₀ D₀ hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
    simp only [hN,Nat.cast_pow] at hh
    have hraw : ‖I k-P k‖ ≤ (Real.exp ((k : ℝ)*t)/T)*
        (A*(B : ℝ)^(-50 : ℝ)+(C*M₀)/B)*((C₂*M^2)*(B : ℝ)^(-(3/2 : ℝ))/(T*(Real.exp ((k : ℝ)*t)/T)))+
        (B : ℝ)^12*((B : ℝ)^12+1)*((C₁*M/B)^2*(((B : ℝ)^13)^10)⁻¹*G) := by
      rw [hN]
      refine hh.trans ?_
      apply add_le_add le_rfl
      have hmul := mul_le_mul_of_nonneg_left hdk (show 0 ≤
        (B : ℝ)^12*((B : ℝ)^12+1)*(C₁*M/B)^2*(((B : ℝ)^13)^10)⁻¹*
          (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖) by positivity)
      convert hmul using 1 <;> dsimp [d,G] <;> ring
    have hh' := coefficient_arc_error_scale hBr hT (div_pos (Real.exp_pos _) hT) hη hscale
      hA (mul_nonneg hC hM₀) (mul_nonneg hC₂ (sq_nonneg M)) (mul_nonneg hC₁ hM0) hG hraw
    simpa only [E,norm_mul,Complex.norm_natCast,mul_assoc,Cerror] using hh'
  have hsum := geometric_box_error_sum hB ht S hbox E hT.le hCerror hlocal
  have hid : geometricSmallArcSum B j Q a b T t S g h w₁ w₂ w-
      geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w = ∑ k ∈ S, E k := by
    simp only [geometricSmallArcSum,geometricFullArcSum,← mul_sub,← sum_sub_distrib,mul_sum]
    rfl
  rw [hid]
  exact hsum

end JointDickman

end OAI
