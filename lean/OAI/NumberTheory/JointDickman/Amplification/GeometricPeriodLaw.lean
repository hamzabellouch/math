import OAI.NumberTheory.JointDickman.Counting.GeometricCoefficientLaw

namespace OAI

/-! # The original separated Fourier expression and the retained full-arc model -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

noncomputable def geometricPeriodSum (B j : ℕ) (a b T t : ℝ)
    (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ) : ℂ :=
  (B : ℂ)*∑ k ∈ S, ∫ θ in (0 : ℝ)..1,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ

theorem geometric_period_split (B j Q : ℕ) {a b T t l u : ℝ} (hT : 0 < T)
    (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hl : 0 < l) (hlu : l ≤ u) (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    geometricPeriodSum B j a b T t S g h w₁ w₂ w-
      geometricSmallArcSum B j Q a b T t S g h w₁ w₂ w =
      (B : ℂ)*∑ k ∈ S,
        ((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)+
        (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)) := by
  unfold geometricPeriodSum geometricSmallArcSum
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  have hc : Continuous (geometricBoxIntegrand B j a b T t g h w₁ w₂ w k) :=
    ((endpointFourierSum_continuous _ _ _ _ _ _).mul
      ((endpointFourierSum_continuous _ _ _ _ _ _).comp continuous_neg)).mul
      ((smoothCoefficientAdditiveSum_continuous B hl.le hlu (div_pos (Real.exp_pos _) hT) hsupp).comp
        (continuous_const.mul continuous_id))
  rw [majorMinor_integral B j _ hc,majorArc_truncated_integral B j Q _ hc]
  ring

theorem geometric_period_model_vanishing
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
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      T*‖geometricPeriodSum B j a b T t S g h w₁ w₂ w-
        geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨c,hc,hcpos,H,ε₁,hε₁,hcoef⟩ := geometric_coefficient_law_vanishing hSD hSW hM hMP
    ha hab hl hlu ht hη w₁ w₂ w w' hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
  obtain ⟨ε₂,hε₂,hdiscard⟩ := geometric_discarded_arcs_vanishing hSD hSW hM hMP
    ha hab hl hlu ht w₁ w₂ w w' hM0 hM₀ hD₀ hw₁ hw₂ hw hw' hwb hwd hsupp
  refine ⟨c,hc,hcpos,H,fun B => ε₂ B+ε₁ B,by simpa using hε₂.add hε₁,?_⟩
  filter_upwards [hcoef,hdiscard] with B hcoefB hdiscardB
  intro T hT hscale S hbox hlog j _ Q hQ g h hg hh
  dsimp only
  have hfirst := hdiscardB T hT S hbox hlog Q hQ j g h hg hh
  rw [← geometric_period_split B j Q hT S g h w₁ w₂ w hl hlu hsupp] at hfirst
  have hsecond := hcoefB T hT hscale S hbox hlog j Q g h hg hh
  exact ((mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) hT.le).trans_eq
    (mul_add _ _ _)).trans (add_le_add hfirst hsecond)

end JointDickman

end OAI
