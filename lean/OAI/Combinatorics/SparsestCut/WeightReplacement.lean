import OAI.Combinatorics.SparsestCut.FiniteWeights

namespace OAI

/-!
# Replacing vertices of zero retained demand

The replacement coupling of Section 7 of OpenAI's
*Constant-factor hardness of uniform sparsest cut* keeps a draw of positive
retained demand and replaces every other draw by an independent retained-demand
draw. Its color-change probability controls the change in Boolean variance.
-/

namespace UniformSparsestCut.FiniteWeights

variable {ι : Type*} [Fintype ι]

/-- The original law restricted to keys with zero retained demand. -/
noncomputable def auxiliaryWeights (w retained : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if retained i = 0 then w i else 0

/-- The original law restricted to keys with nonzero retained demand. -/
noncomputable def supportedWeights (w retained : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if retained i = 0 then 0 else w i

/-- Retain supported draws and replace all others by an independent retained-demand draw. -/
noncomputable def replacementWeights (w retained : ι → ℝ) : ι → ℝ :=
  fun i => supportedWeights w retained i + total (auxiliaryWeights w retained) * retained i

omit [Fintype ι] in
theorem weights_decomposition (w retained : ι → ℝ) (i : ι) :
    supportedWeights w retained i + auxiliaryWeights w retained i = w i := by
  classical
  by_cases hi : retained i = 0 <;> simp [supportedWeights, auxiliaryWeights, hi]

theorem total_decomposition (w retained : ι → ℝ) :
    total (supportedWeights w retained) + total (auxiliaryWeights w retained) = total w := by
  rw [← total_add]
  congr 1
  funext i
  exact weights_decomposition w retained i

theorem mass_decomposition (w retained : ι → ℝ) (h : ι → Bool) :
    mass (supportedWeights w retained) h + mass (auxiliaryWeights w retained) h = mass w h := by
  rw [← mass_add]
  congr 1
  funext i
  exact weights_decomposition w retained i

omit [Fintype ι] in
theorem auxiliary_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (retained : ι → ℝ) :
    ∀ i, 0 ≤ auxiliaryWeights w retained i := by
  classical
  intro i
  dsimp [auxiliaryWeights]
  split
  · exact hw i
  · exact le_rfl

omit [Fintype ι] in
theorem supported_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (retained : ι → ℝ) :
    ∀ i, 0 ≤ supportedWeights w retained i := by
  classical
  intro i
  dsimp [supportedWeights]
  split
  · exact le_rfl
  · exact hw i

omit [Fintype ι] in
theorem auxiliary_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (retained : ι → ℝ) :
    ∀ i, auxiliaryWeights w retained i ≤ w i := by
  classical
  intro i
  dsimp [auxiliaryWeights]
  split
  · exact le_rfl
  · exact hw i

theorem auxiliary_total_le_one {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw₁ : total w = 1) (retained : ι → ℝ) : total (auxiliaryWeights w retained) ≤ 1 := by
  simpa [hw₁] using total_mono (auxiliary_le hw retained)

theorem replacement_nonneg {w retained : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, 0 ≤ retained i) : ∀ i, 0 ≤ replacementWeights w retained i := by
  intro i
  exact add_nonneg (supported_nonneg hw retained i)
    (mul_nonneg (total_nonneg (auxiliary_nonneg hw retained)) (hr i))

theorem replacement_total {w retained : ι → ℝ} (hw₁ : total w = 1)
    (hr₁ : total retained = 1) : total (replacementWeights w retained) = 1 := by
  change total (fun i => supportedWeights w retained i +
    total (auxiliaryWeights w retained) * retained i) = 1
  rw [total_add, total_smul, hr₁, mul_one,
    total_decomposition, hw₁]

theorem replacement_mass (w retained : ι → ℝ) (h : ι → Bool) :
    mass (replacementWeights w retained) h = mass (supportedWeights w retained) h +
      total (auxiliaryWeights w retained) * mass retained h := by
  change mass (fun i => supportedWeights w retained i +
    total (auxiliaryWeights w retained) * retained i) h = _
  rw [mass_add, mass_smul]

/-- Domination of the replacement law before comparison with the original score law. -/
theorem replacement_le_three {w retained : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw₁ : total w = 1) (hr : ∀ i, 0 ≤ retained i)
    (hrep : ∀ i, 0 < retained i → w i ≤ 2 * retained i) :
    ∀ i, replacementWeights w retained i ≤ 3 * retained i := by
  classical
  intro i
  have hs : supportedWeights w retained i ≤ 2 * retained i := by
    by_cases hi : retained i = 0
    · simp [supportedWeights, hi]
    · simpa [supportedWeights, hi] using hrep i (lt_of_le_of_ne (hr i) (Ne.symm hi))
  have ha : total (auxiliaryWeights w retained) * retained i ≤ retained i := by
    simpa using mul_le_mul_of_nonneg_right (auxiliary_total_le_one hw hw₁ retained) (hr i)
  dsimp [replacementWeights]
  linarith only [hs, ha]

/-- The actual color-change cost of the replacement experiment bounds both signed
changes in the probability of color one. -/
theorem replacement_mass_change {w retained : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, 0 ≤ retained i) (hr₁ : total retained = 1) (h : ι → Bool) :
    mass w h - mass (replacementWeights w retained) h ≤
        disagreement (auxiliaryWeights w retained) retained h ∧
    mass (replacementWeights w retained) h - mass w h ≤
        disagreement (auxiliaryWeights w retained) retained h := by
  rw [replacement_mass, disagreement_eq, hr₁]
  have hdec := mass_decomposition w retained h
  have haux := auxiliary_nonneg hw retained
  have ht : 0 ≤ 1 - mass retained h := sub_nonneg.mpr (hr₁ ▸ mass_le_total hr h)
  have hp := mul_nonneg (mass_nonneg haux h) ht
  have hq := mul_nonneg (sub_nonneg.mpr (mass_le_total haux h)) (mass_nonneg hr h)
  constructor <;> nlinarith only [hdec, hp, hq]

/-- Variance transfer for the replacement coupling in Section 7 of
*Constant-factor hardness of uniform sparsest cut*.

Here `w` is the counting law on clusters, `μ` the original score demand law, and
`retained` the normalized retained demand.  Zero retained mass is allowed.
The final term is the probability that replacement changes the color, denoted
`L_aux` in the paper.
-/
theorem variance_transfer {w μ retained : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hμ : ∀ i, 0 ≤ μ i) (hr : ∀ i, 0 ≤ retained i)
    (hw₁ : total w = 1) (hμ₁ : total μ = 1) (hr₁ : total retained = 1)
    (hret : ∀ i, retained i ≤ 2 * μ i)
    (hrep : ∀ i, 0 < retained i → w i ≤ 2 * retained i) (h : ι → Bool) :
    variance w h ≤ 36 * variance μ h + disagreement (auxiliaryWeights w retained) retained h := by
  have hρ := replacement_nonneg hw hr
  have hρ₁ := replacement_total hw₁ hr₁
  have hdom : ∀ i, replacementWeights w retained i ≤ 6 * μ i := by
    intro i
    have hthree := replacement_le_three hw hw₁ hr hrep i
    linarith only [hthree, hret i]
  have hv : variance (replacementWeights w retained) h ≤ 36 * variance μ h := by
    have hv' := variance_domination hρ hμ hρ₁ hμ₁ (by norm_num : (0 : ℝ) ≤ 6) hdom h
    norm_num at hv'
    exact hv'
  have hd := replacement_mass_change hw hr hr₁ h
  have hc : variance w h ≤ variance (replacementWeights w retained) h +
      disagreement (auxiliaryWeights w retained) retained h :=
    variance_change (mass_nonneg hw h) (hw₁ ▸ mass_le_total hw h)
      (mass_nonneg hρ h) (hρ₁ ▸ mass_le_total hρ h) hd.1 hd.2
  exact hc.trans (add_le_add hv le_rfl)

end UniformSparsestCut.FiniteWeights

end OAI
