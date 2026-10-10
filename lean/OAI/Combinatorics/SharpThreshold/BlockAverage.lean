import Mathlib

namespace OAI

universe u v w

noncomputable section

namespace Problem313.BlockAverage

open scoped BigOperators

/-- Exchange the average over blocks with a sum over objects detected by a block. -/
theorem weighted_incidence_sum
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) =
      ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : P b s <;> simp [h]

/-- Nonnegative block weights give nonnegative incidence probabilities. -/
theorem incidence_sum_nonneg
    {β : Type v} [Fintype β] (μ : β → ℝ) (P : β → Prop)
    [DecidablePred P] (hμ : ∀ b, 0 ≤ μ b) :
    0 ≤ ∑ b, if P b then μ b else 0 := by
  apply Finset.sum_nonneg
  intro b hb
  split_ifs
  · exact hμ b
  · exact le_rfl

/-- A collection of nonnegative masses detected with probability at least `c`
contributes at least `c` times its total mass to the average detected mass. -/
theorem capture_lower_bound
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] (low : Finset α) (c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0) :
    c * ∑ s ∈ low, w s ≤ ∑ b, μ b * ∑ s, if P b s then w s else 0 := by
  rw [weighted_incidence_sum, Finset.mul_sum]
  calc
    ∑ s ∈ low, c * w s ≤
        ∑ s ∈ low, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_right (hcapture s hs) (hw s)
    _ ≤ ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      intro s hs hnot
      exact mul_nonneg (incidence_sum_nonneg μ (fun b => P b s) hμ) (hw s)

/-- Pointwise block bounds average to a global bound using the incidence
probability of each coordinate. No normalization assumption is required. -/
theorem block_upper_bound
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (a d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤ a * d * ∑ i, I i := by
  calc
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤
        ∑ b, μ b * (a * ∑ i, if E b i then I i else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hblock b) (hμ b)
    _ = a * ∑ b, μ b * ∑ i, if E b i then I i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = a * ∑ i, (∑ b, if E b i then μ b else 0) * I i := by
      rw [weighted_incidence_sum]
    _ ≤ a * ∑ i, d * I i := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hincidence i) (hI i)
    _ = a * d * ∑ i, I i := by rw [← Finset.mul_sum]; ring

/-- The algebraic block-capture argument, with arbitrary capture and incidence
constants. It separates all finite averaging from the Fourier and graph input. -/
theorem captured_mass_le
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ s ∈ low, w s) ≤ (a * d / c) * ∑ i, I i := by
  have hlow := capture_lower_bound μ w P low c hμ hw hcapture
  have hupp := block_upper_bound μ w I P E a d hμ hI ha hblock hincidence
  have hcombined := hlow.trans hupp
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * ∑ s ∈ low, w s ≤ a * d * ∑ i, I i := hcombined
    _ = c * ((a * d / c) * ∑ i, I i) := by field_simp [ne_of_gt hc]

/-- The factor-four consequence used for uniform vertex blocks:
capture at least `m/(2*n)` and edge incidence at most `2*m/n`. -/
theorem captured_mass_le_four
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  have h := captured_mass_le μ w I P E low a c (4 * c)
    hμ hw hI ha hc hcapture hblock hincidence
  have hc0 : c ≠ 0 := ne_of_gt hc
  have heq : a * (4 * c) / c = 4 * a := by field_simp [ne_of_gt hc]
  simpa only [heq] using h

/-- Uniform finite sampling agrees with the normalized cardinality used by the
vertex-block counting lemmas. This also holds for an empty sampling family. -/
theorem uniform_incidence_sum
    {β : Type v} [DecidableEq β] (Ω : Finset β) (P : β → Prop)
    [DecidablePred P] :
    (∑ b : Ω, if P b.val then (1 : ℝ) / Ω.card else 0) =
      ((Ω.filter P).card : ℝ) / Ω.card := by
  rw [← Finset.sum_subtype Ω (fun _ => Iff.rfl)
    (fun b => if P b then (1 : ℝ) / Ω.card else 0)]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Uniform-block version of the factor-four capture argument, stated entirely
with cardinal-ratio probabilities to match the combinatorial counting API. -/
theorem captured_mass_le_four_uniform
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [DecidableEq β] [Fintype ι]
    (Ω : Finset β) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hI : ∀ i, 0 ≤ I i)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤
      ((Ω.filter (fun b => P b s)).card : ℝ) / Ω.card)
    (hblock : ∀ b ∈ Ω, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i,
      ((Ω.filter (fun b => E b i)).card : ℝ) / Ω.card ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  apply captured_mass_le_four
    (fun _ : Ω => (1 : ℝ) / Ω.card) w I
    (fun b s => P b.val s) (fun b i => E b.val i) low a c
  · intro b
    positivity
  · exact hw
  · exact hI
  · exact ha
  · exact hc
  · intro s hs
    rw [uniform_incidence_sum Ω (fun b => P b s)]
    exact hcapture s hs
  · intro b
    exact hblock b.val b.property
  · intro i
    rw [uniform_incidence_sum Ω (fun b => E b i)]
    exact hincidence i

end Problem313.BlockAverage

end

end OAI
