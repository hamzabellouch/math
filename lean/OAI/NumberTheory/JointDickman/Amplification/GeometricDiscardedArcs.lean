import OAI.NumberTheory.JointDickman.Amplification.DischargedMinorArcBox
import OAI.NumberTheory.JointDickman.Amplification.GeometricBoxErrors
import OAI.NumberTheory.JointDickman.Amplification.MinorArcBoxBound
import OAI.NumberTheory.JointDickman.Amplification.LargeMajorBoxBound
import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass

namespace OAI

/-! # The original geometric sum loses only o(1/T) outside the retained arcs -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

/-- The lag is displayed separately from the geometric endpoint scale. -/
noncomputable def geometricBoxIntegrand (B j : ℕ) (a b T t : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w₃ : ℝ → ℝ)
    (k : ℤ) (θ : ℝ) : ℂ :=
  endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
    endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)*
    smoothCoefficientAdditiveSum B (Real.exp ((k : ℝ)*t)/T) (-(j : ℝ)*θ) w₃

theorem geometric_discarded_arcs_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u) (ht : 0 < t)
    (w₁ w₂ w₃ w₃' : ℝ → ℝ) {M M₃ N₃ : ℝ}
    (hM0 : 0 ≤ M) (hM₃ : 0 ≤ M₃) (hN₃ : 0 ≤ N₃)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw₃ : ∀ x, HasDerivAt w₃ (w₃' x) x) (hw₃' : Continuous w₃')
    (hwb₃ : ∀ x, |w₃ x| ≤ M₃) (hwd₃ : ∀ x, |w₃' x| ≤ N₃)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w₃ x = 0) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖(B : ℂ)*∑ k ∈ S,
        ((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
            geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)+
          (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
            geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ))‖ ≤ ε B := by
  obtain ⟨C₁,hC₁,hminor⟩ := minorArc_box_bound_bounded_log hSD hM hMP ha hab hl hlu
    (by norm_num : (0 : ℝ) < 1/20)
  obtain ⟨C₂,D,K,hC₂,hD,hK,hmajor⟩ := largeMajorArc_box_bound hSD hSW hM hMP ha hab hl hlu
    (by norm_num : (0 : ℝ) < 1/20)
  let A := C₁*M^2*(2*M₃+N₃*(u-l))
  let C := C₂*M^2*(D*M₃*(u-l)+K*u*(2*M₃+(N₃+2*Real.pi*M₃)*(u-l)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; have hu := hl.trans_le hlu; positivity
  let ε₁ := fun B : ℕ => ((8/(5*t)+1)*A)*(B : ℝ)^((-(6/5 : ℝ))+1)
  let ε₂ := fun B : ℕ => ((8/(5*t)+1)*C)*(B : ℝ)^((-(11/10 : ℝ))+1)
  refine ⟨fun B => ε₁ B+ε₂ B,?_,?_⟩
  · simpa using (geometric_box_error_vanishing (C := A) (r := -(6/5 : ℝ)) ht (by norm_num)).add
      (geometric_box_error_vanishing (C := C) (r := -(11/10 : ℝ)) ht (by norm_num))
  filter_upwards [hminor,hmajor,eventually_ge_atTop 1] with B hmin hmaj hB
  intro T hT S hbox hlog Q hQ j g h hg hh
  have hN (k : ℤ) : T*(Real.exp ((k : ℝ)*t)/T) = Real.exp ((k : ℝ)*t) := by field_simp
  have hNlog (k : ℤ) (hk : k ∈ S) : Real.log (T*(Real.exp ((k : ℝ)*t)/T)) ∈
      Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) := by rw [hN,Real.log_exp]; exact hbox k hk
  let E₁ := fun k : ℤ => (B : ℂ)*(∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)
  let E₂ := fun k : ℤ => (B : ℂ)*(∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)
  have he₁ : ∀ k ∈ S, T*‖E₁ k‖ ≤ A*(B : ℝ)^(-(6/5 : ℝ)) := by
    intro k hk
    have he := hmin T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk).1 (hlog k hk).2 (hNlog k hk) j (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hg _) (fun _ _ => hh _)
      w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hwb₃ hwd₃ hsupp
    rw [hN] at he
    norm_num only [show (-5/4+(1/20 : ℝ)) = -6/5 by norm_num] at he
    simpa only [E₁,E₂,geometricBoxIntegrand,A,C,mul_comm T] using (le_div_iff₀ hT).mp he
  have he₂ : ∀ k ∈ S, T*‖E₂ k‖ ≤ C*(B : ℝ)^(-(11/10 : ℝ)) := by
    intro k hk
    have he := hmaj T (Real.exp ((k : ℝ)*t)/T) hT (div_pos (Real.exp_pos _) hT)
      (hlog k hk) (hNlog k hk) Q hQ j (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hg _) (fun _ _ => hh _)
      w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hwb₃ hwd₃ hsupp
    rw [hN] at he
    norm_num only [show (-23/20+(1/20 : ℝ)) = -11/10 by norm_num] at he
    simpa only [E₁,E₂,geometricBoxIntegrand,A,C,mul_comm T] using (le_div_iff₀ hT).mp he
  have hsum₁ := geometric_box_error_sum hB ht S hbox E₁ hT.le hA he₁
  have hsum₂ := geometric_box_error_sum hB ht S hbox E₂ hT.le hC he₂
  have heq : (B : ℂ)*∑ k ∈ S,
      ((∫ θ in minorArcRegion B j (Real.exp ((k : ℝ)*t)/T),
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)+
        (∫ θ in largeMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w₃ k θ)) =
      (∑ k ∈ S, E₁ k)+(∑ k ∈ S, E₂ k) := by simp only [mul_sum,mul_add,sum_add_distrib,E₁,E₂]
  rw [heq]
  exact ((mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le).trans_eq (mul_add _ _ _)).trans
    (add_le_add hsum₁ hsum₂)

end JointDickman

end OAI
