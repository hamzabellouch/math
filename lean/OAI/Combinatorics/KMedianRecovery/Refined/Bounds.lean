import OAI.Combinatorics.KMedianRecovery.Refined.Charges

namespace OAI

/-! Explicit charge coefficients, finite probability bounds, and conditional extraction. -/

namespace MetricKMedianRecovery.RefinedRecovery.Analysis

lemma inverse_e_lt_half : 1 / Real.exp 1 < (1/2 : ℝ) := by
  rw [div_lt_iff₀ (Real.exp_pos 1)]
  linarith [Real.exp_one_gt_two]

lemma third_lt_inverse_e : (1/3 : ℝ) < 1 / Real.exp 1 := by
  rw [lt_div_iff₀ (Real.exp_pos 1)]
  linarith [Real.exp_one_lt_three]

lemma rational_theta {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1/4) :
    ∃ θ : ℚ, 1 / Real.exp 1 < (θ : ℝ) ∧ (θ : ℝ) ≤ 1 / Real.exp 1 + μ ∧
      0 < (θ : ℝ) ∧ (θ : ℝ) < 1 := by
  obtain ⟨θ, ht0, ht1⟩ := exists_rat_btwn (show 1 / Real.exp 1 < 1 / Real.exp 1 + μ by linarith)
  refine ⟨θ, ht0, ht1.le, ?_, ?_⟩
  · exact (one_div_pos.mpr (Real.exp_pos 1)).trans ht0
  · linarith [inverse_e_lt_half]

lemma cube_div_q {μ : ℝ} (hμ : 0 < μ) : μ^3 / q μ = μ^2 + μ^3 := by
  unfold q
  field_simp

lemma quadratic_cubic_error {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) :
    3*μ^2 + 12*μ^3 ≤ (3/2 : ℝ)*μ := by
  have hs : μ^2 ≤ μ/4 := by nlinarith
  have hc : μ^3 ≤ μ/16 := by
    have hh := mul_le_mul_of_nonneg_left hs hμ
    nlinarith
  linarith

lemma explicit_coefficient {μ θ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1/4)
    (hθ : θ ≤ 1 / Real.exp 1 + μ) :
    1 + 2*θ*(1+μ) + μ + 11*μ^3 + μ^3/q μ ≤ 1 + 2/Real.exp 1 + 6*μ := by
  rw [cube_div_q hμ]
  have ht := mul_le_mul_of_nonneg_right hθ (show 0 ≤ 2*(1+μ) by linarith)
  have he := mul_le_mul_of_nonneg_right inverse_e_lt_half.le hμ.le
  have herr := quadratic_cubic_error hμ.le hμ1
  simp only [div_eq_mul_inv] at ht he ⊢
  nlinarith

lemma sum_five_charges
    (μ θ κ q P Pg P₁ P₂ Ph Pl X₂ R₁ R₂ T₂ Th Tl Eh El I Cg C₁ C₂ Ch Cl : ℝ)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (ht0 : (1/3 : ℝ) ≤ θ) (ht1 : θ ≤ 1)
    (hk : 0 ≤ κ) (hq : 0 < q)
    (hg : 0 ≤ Pg) (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂) (hh : 0 ≤ Ph) (hl : 0 ≤ Pl)
    (hsum : Pg+P₁+P₂+Ph+Pl = P) (hX : X₂ ≤ P₂)
    (hR : R₁+R₂ ≤ (11/2 : ℝ)*P) (hT : T₂+Th+Tl ≤ κ*P)
    (hEh : Eh ≤ κ*P) (hEl : El ≤ κ*P) (hI : I ≤ κ*P)
    (hCg : Cg ≤ Pg+μ*P)
    (hC1 : C₁ ≤ (1+2*θ*(1+μ))*P₁ + θ*κ*(1+μ)*P₁ + θ*κ*R₁)
    (hC2 : C₂ ≤ (1+2*θ)*P₂ + θ*κ*(3/2)*X₂ + θ*κ*R₂ + T₂/q)
    (hCh : Ch ≤ (1+(2/3 : ℝ)*(1+μ))*Ph + Th/q + Eh)
    (hCl : Cl ≤ (1+(2/3 : ℝ)*(1+μ))*Pl + Tl/q + El) :
    2*I + Cg+C₁+C₂+Ch+Cl ≤
      (1+2*θ*(1+μ)+μ+11*κ+κ/q)*P := by
  let B := 1+2*θ*(1+μ)
  have hθ : 0 ≤ θ := by linarith
  have hP : 0 ≤ P := by linarith
  have hBg : 1 ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hθ (show 0 ≤ 1+μ by linarith)]
  have hB2 : 1+2*θ ≤ B := by dsimp [B]; nlinarith [mul_nonneg hθ hμ]
  have hBh : 1+(2/3 : ℝ)*(1+μ) ≤ B := by
    have hh := mul_le_mul_of_nonneg_right ht0 (show 0 ≤ 2*(1+μ) by linarith)
    dsimp [B]; linarith
  have hCg' : Cg ≤ B*Pg+μ*P := by
    have he := mul_le_mul_of_nonneg_right hBg hg
    linarith
  have hC2' : C₂ ≤ B*P₂ + θ*κ*(3/2)*X₂ + θ*κ*R₂ + T₂/q := by
    have he := mul_le_mul_of_nonneg_right hB2 h2
    linarith
  have hCh' : Ch ≤ B*Ph + Th/q + Eh := by
    have he := mul_le_mul_of_nonneg_right hBh hh
    linarith
  have hCl' : Cl ≤ B*Pl + Tl/q + El := by
    have he := mul_le_mul_of_nonneg_right hBh hl
    linarith
  have hcluster : (1+μ)*P₁+(3/2 : ℝ)*X₂ ≤ (3/2 : ℝ)*P := by
    have he := mul_le_mul_of_nonneg_right hμ1 h1
    linarith
  have hr : θ*κ*((1+μ)*P₁+(3/2 : ℝ)*X₂+R₁+R₂) ≤ 7*κ*P := by
    calc
      _ ≤ θ*κ*(7*P) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ hk)
        linarith
      _ ≤ 7*κ*P := by nlinarith [mul_le_mul_of_nonneg_right ht1 (mul_nonneg hk hP)]
  have hterr : (T₂+Th+Tl)/q ≤ (κ/q)*P := by
    have he := div_le_div_of_nonneg_right hT hq.le
    simpa only [mul_div_right_comm] using he
  have hsum' : B*Pg+B*P₁+B*P₂+B*Ph+B*Pl = B*P := by rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, hsum]
  change C₁ ≤ B*P₁ + θ*κ*(1+μ)*P₁ + θ*κ*R₁ at hC1
  have total : 2*I+Cg+C₁+C₂+Ch+Cl ≤ B*P+μ*P+11*κ*P+(κ/q)*P := by
    rw [add_div, add_div] at hterr
    nlinarith only [hCg', hC1, hC2', hCh', hCl', hsum', hr, hterr, hEh, hEl, hI]
  calc
    _ ≤ B*P+μ*P+11*κ*P+(κ/q)*P := total
    _ = _ := by dsimp [B]; ring

lemma expectation_slack {μ ε P : ℝ} (hP : 0 ≤ P) (hμ : μ ≤ ε/12) :
    (1+2/Real.exp 1+6*μ)*P ≤ (1+2/Real.exp 1+ε/2)*P := by
  apply mul_le_mul_of_nonneg_right _ hP
  linarith

noncomputable def finiteAverage {Ω : Type*} (S : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ S, f ω) / S.card

noncomputable def finiteProbability {Ω : Type*} (S : Finset Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact ((S.filter event).card : ℝ) / S.card

lemma finite_markov {Ω : Type*} [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty)
    (f : Ω → ℝ) (hf : ∀ ω ∈ S, 0 ≤ f ω) (target K : ℝ) (ht : 0 < target)
    (havg : finiteAverage S f ≤ K) :
    1-K/target ≤ finiteProbability S (fun ω => f ω ≤ target) := by
  classical
  let Good := S.filter (fun ω => f ω ≤ target)
  let Bad := S \ Good
  have hc : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hsum : (Bad.card : ℝ)*target ≤ ∑ ω ∈ S, f ω := by
    calc
      _ = ∑ _ω ∈ Bad, target := by simp
      _ ≤ ∑ ω ∈ Bad, f ω := by
        apply Finset.sum_le_sum
        intro ω hω
        have hωS := (Finset.mem_sdiff.mp hω).1
        have hh := (Finset.mem_sdiff.mp hω).2
        exact le_of_not_ge (fun he => hh (Finset.mem_filter.mpr ⟨hωS, he⟩))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun ω hω _ => hf ω hω)
  have hcount : (Bad.card : ℝ) + Good.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun ω => f ω ≤ target) S)
  have hsum' := (div_le_iff₀ hc).mp havg
  change 1-K/target ≤ (Good.card : ℝ)/S.card
  apply (le_div_iff₀ hc).mpr
  apply (le_of_mul_le_mul_right ?_ ht)
  field_simp
  nlinarith

lemma conditional_extraction {Ω : Type*} [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty)
    (f : Ω → ℝ) (hf : ∀ ω ∈ S, 0 ≤ f ω) (P ε : ℝ) (hP : 0 < P) (hε : 0 < ε)
    (havg : finiteAverage S f ≤ (1+2/Real.exp 1+ε/2)*P) :
    ε/(2*(1+2/Real.exp 1+ε)) ≤
      finiteProbability S (fun ω => f ω ≤ (1+2/Real.exp 1+ε)*P) := by
  have he : 0 < 1+2/Real.exp 1+ε := by positivity
  have hh := finite_markov S hS f hf ((1+2/Real.exp 1+ε)*P)
    ((1+2/Real.exp 1+ε/2)*P) (mul_pos he hP) havg
  have heq : 1-((1+2/Real.exp 1+ε/2)*P)/((1+2/Real.exp 1+ε)*P) =
      ε/(2*(1+2/Real.exp 1+ε)) := by field_simp; ring
  rwa [heq] at hh

end MetricKMedianRecovery.RefinedRecovery.Analysis

end OAI
