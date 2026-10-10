import OAI.NumberTheory.JointDickman.Counting.CoefficientViolationBounds

namespace OAI

/-! # Summing the actual prefix failures on a fixed grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def prefixGridError (B L : ℕ) (c τ s : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 L,
    (prefixLowerFactor B c ((i : ℝ) / L) τ s +
      prefixUpperFactor B c ((i : ℝ) / L) τ s)

theorem prefixGridError_nonneg (B L : ℕ) (c τ s : ℝ) :
    0 ≤ prefixGridError B L c τ s := by
  apply sum_nonneg
  intro i _
  exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem prefixGridError_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ (L : ℕ) (c : ℝ), 0 < L → 0 < c → c ≤ 4 →
        Tendsto (fun B => prefixGridError B L c τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, hs1, he, hen, hdec⟩ := actual_prefix_chernoff_decay hM hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro L c hL hc hc4
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlim := tendsto_finsetSum (Icc 1 L) (f := fun (i : ℕ) B =>
    prefixLowerFactor B c ((i : ℝ) / L) τ s +
      prefixUpperFactor B c ((i : ℝ) / L) τ s) (a := fun _ => (0 : ℝ)) (fun i hi => by
        have hi' := mem_Icc.mp hi
        have hip : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
        have hil : (i : ℝ) ≤ L := by exact_mod_cast hi'.2
        have hh := hdec c ((i : ℝ) / L) hc hc4 (div_pos hip hL')
          ((div_le_one hL').mpr hil)
        simpa using hh.2.add hh.1)
  simpa only [prefixGridError, sum_const_zero] using hlim

/-- Finite summation of a common main factor and uniformly bounded remainders. -/
theorem sum_le_linear_remainder {ι : Type*} (S : Finset ι)
    (f t r : ι → ℝ) {A E R : ℝ} (hE : 0 ≤ E)
    (hf : ∀ i ∈ S, f i ≤ A * t i + r i * E)
    (hr : ∀ i ∈ S, r i ≤ R) :
    (∑ i ∈ S, f i) ≤ A * (∑ i ∈ S, t i) + (S.card : ℝ) * R * E := by
  calc
    _ ≤ ∑ i ∈ S, (A * t i + R * E) := sum_le_sum (fun i hi =>
      (hf i hi).trans (add_le_add_right (mul_le_mul_of_nonneg_right (hr i hi) hE) _))
    _ = _ := by simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring

theorem coefficient_prefix_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (L : ℕ) (τ s : ℝ), 0 < L → 0 ≤ τ → 0 < s → s ≤ 1 →
      Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      0 ≤ auxiliaryLogLength B → auxiliaryLogLength B ≤ Real.log B →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        prefixGridError B L (δ / 8) τ s +
      2 * L * B * coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hbound⟩ := coefficient_prefix_pair_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k L τ s hL hτ hs hs1 he hen hℓ hℓlog
  let f := fun i b d =>
    ((if ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ) <
      (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b d else 0) +
    (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
      ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ)
      then tripleCoefficientWeight B j b d else 0))
  have hswap : (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ Icc 1 L, f i b d) =
      ∑ i ∈ Icc 1 L, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d := by
    calc
      _ = ∑ b ∈ Ico l₁ r₁, ∑ i ∈ Icc 1 L, ∑ d ∈ Ico l₂ r₂, f i b d :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  change (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ Icc 1 L, f i b d) ≤ _
  rw [hswap]
  have hE := coefficientRectangleRemainder_nonneg B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ hI hJ
  have hsum := sum_le_linear_remainder (Icc 1 L)
    (fun i => ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d)
    (fun i => prefixLowerFactor B (δ / 8) ((i : ℝ) / L) τ s +
      prefixUpperFactor B (δ / 8) ((i : ℝ) / L) τ s)
    (fun i => Real.exp (s * ((((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B)) +
      Real.exp (-s * ((((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B)))
    (R := 2 * B) hE
    (fun i _ => hbound B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k ((i : ℝ) / L) τ s hs he hen)
    (fun i hi => by
      have hi' := mem_Icc.mp hi
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hg : 0 ≤ (i : ℝ) / L := div_nonneg (Nat.cast_nonneg _) hL'.le
      have hg1 : (i : ℝ) / L ≤ 1 := (div_le_one hL').mpr (by exact_mod_cast hi'.2)
      have hh := prefix_markov_multiplier_bounds (by omega : 1 ≤ B) hg hg1 hτ hs.le hs1 hℓ hℓlog
      linarith)
  convert hsum using 1
  simp only [prefixGridError, Nat.card_Icc, Nat.add_sub_cancel]
  ring

end JointDickman

end OAI
