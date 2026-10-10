import OAI.NumberTheory.JointDickman.Probability.TensorBoxRegularity
import OAI.NumberTheory.JointDickman.Probability.AmplificationTensorProfile

namespace OAI

/-! # Regularity loss for the manuscript's concrete dyadic amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem dyadic_tensor_box_conditions {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlog : Real.log T ≤ (B : ℝ)/10) {k : ℤ}
    (hk : k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)) :
    let N := Real.exp ((k : ℝ)*Real.log 2)
    1 ≤ N ∧ 1 ≤ N/T ∧ Real.exp ((1/2 : ℝ)*B) ≤ 3*N ∧
      Real.exp ((1/2 : ℝ)*B) ≤ 3*(N/T) ∧
      (17/4 : ℝ)*N ≤ Real.exp ((16/5 : ℝ)*B) := by
  dsimp only
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hwin := (dyadic_scale_window hB hT hlog).2.1 k hk
  have hmin : Real.exp ((9/10 : ℝ)*B) ≤ Real.exp ((k : ℝ)*Real.log 2) :=
    Real.exp_le_exp.mpr hwin.1.1
  have hmax : Real.exp ((k : ℝ)*Real.log 2) ≤ Real.exp ((5/2 : ℝ)*B) :=
    Real.exp_le_exp.mpr hwin.1.2
  have hdiv : Real.exp ((9/10 : ℝ)*B) ≤ Real.exp ((k : ℝ)*Real.log 2)/T := by
    have he := Real.exp_le_exp.mpr hwin.2.1
    rwa [Real.exp_log (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hT))] at he
  have hone : 1 ≤ Real.exp ((9/10 : ℝ)*B) := Real.one_le_exp_iff.mpr (by linarith)
  have hmid : Real.exp ((1/2 : ℝ)*B) ≤ Real.exp ((9/10 : ℝ)*B) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfactor : (17/4 : ℝ) ≤ Real.exp ((7/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((7/10 : ℝ)*B)
    linarith
  refine ⟨hone.trans hmin,hone.trans hdiv,by linarith,by linarith,?_⟩
  calc
    _ ≤ Real.exp ((7/10 : ℝ)*B)*Real.exp ((5/2 : ℝ)*B) :=
      mul_le_mul hfactor hmax (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

open Classical in
/-- The actual smooth summand loses only a vanishing error plus the explicit
regularity tail, with the uniform 1/(B*T) normalization on each dyadic box. -/
theorem dyadicBox_signed_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 →
          ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ∀ (C : ℝ) (j : ℕ), 0 ≤ C → j ≠ 0 →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          let N := Real.exp ((k : ℝ)*Real.log 2)
          signedLocalRegularityError B L j τ C
            (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
            (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h
            (fun a b c => amplificationBoxWeight B (Real.log (N/T)/B)
              (a/N) (b/N) (c/(N/T))) ≤
            K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hbox⟩ := tensorBox_signed_regularity_loss hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hbox,eventually_ge_atTop 30] with B hb hB
  intro T hT hlog k hk C j hC hj g h hg hh
  have hs := dyadic_tensor_box_conditions hB hT hlog hk
  dsimp only at hs ⊢
  apply hb C _ T j hC hs.1 (lt_of_lt_of_le zero_lt_one hT) hs.2.1 hj
    hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 g h hg hh
  intro a _ b _ c _
  unfold amplificationBoxWeight
  have h1 := amplificationBump_bounds
    (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B+
      Real.log (c/(Real.exp ((k : ℝ)*Real.log 2)/T))/B)
  have h2 := amplificationSpatialProfile_bounds (a/Real.exp ((k : ℝ)*Real.log 2))
    (b/Real.exp ((k : ℝ)*Real.log 2)) (c/(Real.exp ((k : ℝ)*Real.log 2)/T))
  rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
  exact (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans_eq (mul_one 1)

end JointDickman

end OAI
