import OAI.Analysis.LipschitzHilbert.Estimates.CountableCarleson
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineRoots

namespace OAI

/-!
# Gluing rootwise counting tails on a bounded interval

Finite root covers and their total lengths transfer a rootwise tail to
any bounded interval. The two shifted grids used by the covering lemma
then combine by an exact ENNReal pigeonhole inequality.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [MeasurableSpace X]

theorem measureReal_le_sum_of_finite_cover (μ : Measure X) (s : Finset ι)
    (Q : ι → Set X) {E : Set X} (hcover : E ⊆ ⋃ i ∈ s, Q i)
    (hfinite : ∀ i ∈ s, μ (Q i) ≠ ⊤) :
    μ.real E ≤ ∑ i ∈ s, μ.real (Q i) := by
  have hsum : (∑ i ∈ s, μ (Q i)) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun i hi => (hfinite i hi).lt_top)
  have hfin : μ (⋃ i ∈ s, Q i) ≠ ⊤ :=
    ((measure_biUnion_finset_le s Q).trans_lt hsum).ne
  exact (measureReal_mono hcover hfin).trans (measureReal_biUnion_finset_le s Q)

theorem finite_root_tail_gluing (μ : Measure X) (s : Finset ι) (Q : ι → Set X)
    {U E : Set X} (hcover : U ⊆ ⋃ i ∈ s, Q i)
    (hfinite : ∀ i ∈ s, μ (Q i) ≠ ⊤) {c : ℝ}
    (hroot : ∀ i ∈ s, μ.real (E ∩ Q i) ≤ c * μ.real (Q i)) :
    μ.real (E ∩ U) ≤ c * ∑ i ∈ s, μ.real (Q i) := by
  have hc : E ∩ U ⊆ ⋃ i ∈ s, E ∩ Q i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx.2)
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx.1, hxi⟩⟩
  calc
    μ.real (E ∩ U) ≤ ∑ i ∈ s, μ.real (E ∩ Q i) :=
      measureReal_le_sum_of_finite_cover μ s (fun i => E ∩ Q i) hc
        (fun i hi => measure_ne_top_of_subset Set.inter_subset_right (hfinite i hi))
    _ ≤ ∑ i ∈ s, c * μ.real (Q i) := Finset.sum_le_sum fun i hi => hroot i hi
    _ = _ := (Finset.mul_sum ..).symm

/-- Rootwise estimates combine with the actual floor-index root band. -/
theorem dyadic_root_tail_gluing (q k : ℤ) {a b : ℝ} (hab : a ≤ b)
    {E : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hroot : ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      volume.real (E ∩ DyadicLineGrid.cell q k j) ≤
        c * volume.real (DyadicLineGrid.cell q k j)) :
    volume.real (E ∩ Set.Icc a b) ≤ c * (b - a + 2 * DyadicLineGrid.scale k) := by
  have h := finite_root_tail_gluing volume (DyadicLineGrid.rootBand q k a b)
    (DyadicLineGrid.cell q k) (DyadicLineGrid.interval_subset_rootBand q k a b)
    (fun j _ => by rw [DyadicLineGrid.cell, Real.volume_Ico]; exact ENNReal.ofReal_ne_top) hroot
  exact h.trans (mul_le_mul_of_nonneg_left (DyadicLineGrid.rootBand_total_length q k hab) hc)

omit [MeasurableSpace X] in
theorem ennreal_two_count_superlevel (f g : X → ℝ≥0∞) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    {x | ENNReal.ofReal lambda < f x + g x} ⊆
      {x | ENNReal.ofReal (lambda / 2) < f x} ∪
        {x | ENNReal.ofReal (lambda / 2) < g x} := by
  intro x hx
  by_contra h
  have h0 : f x ≤ ENNReal.ofReal (lambda / 2) := by
    exact le_of_not_gt (fun hf => h (Or.inl hf))
  have h1 : g x ≤ ENNReal.ofReal (lambda / 2) := by
    exact le_of_not_gt (fun hg => h (Or.inr hg))
  have hsum := add_le_add h0 h1
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  have heq : lambda / 2 + lambda / 2 = lambda := by ring
  rw [heq] at hsum
  exact not_lt_of_ge hsum hx

/-- Adding the counts from two grids costs a factor two in both the
front constant and the threshold. -/
theorem two_count_tail_gluing (μ : Measure X) {U : Set X} (hUfinite : μ U ≠ ⊤)
    (f g : X → ℝ≥0∞) {lambda B : ℝ} (hlambda : 0 ≤ lambda)
    (hf : μ.real ({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ≤ B)
    (hg : μ.real ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U) ≤ B) :
    μ.real ({x | ENNReal.ofReal lambda < f x + g x} ∩ U) ≤ 2 * B := by
  have hcover : {x | ENNReal.ofReal lambda < f x + g x} ∩ U ⊆
      ({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ∪
        ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U) := by
    intro x hx
    rcases ennreal_two_count_superlevel f g hlambda hx.1 with h | h
    · exact Or.inl ⟨h, hx.2⟩
    · exact Or.inr ⟨h, hx.2⟩
  have hfinite : μ (({x | ENNReal.ofReal (lambda / 2) < f x} ∩ U) ∪
      ({x | ENNReal.ofReal (lambda / 2) < g x} ∩ U)) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.union_subset Set.inter_subset_right Set.inter_subset_right) hUfinite
  have h := (measureReal_mono hcover hfinite).trans (measureReal_union_le _ _)
  linarith

/-- The rootwise Carleson tail on the two actual translated grids gives
the full bounded-interval tail, with the threshold loss made explicit. -/
theorem two_dyadic_root_exponential_tail (k : ℤ) {a b A lambda : ℝ}
    (hab : a ≤ b) (hA : 0 < A) (hlambda : 0 ≤ lambda)
    (count : ℤ → ℝ → ℝ≥0∞)
    (hroot : ∀ q ∈ ({0, 1} : Finset ℤ), ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      ∀ t : ℝ, 0 ≤ t →
      volume.real ({x | ENNReal.ofReal t < count q x} ∩ DyadicLineGrid.cell q k j) ≤
        2 * volume.real (DyadicLineGrid.cell q k j) * Real.exp (-t / (2 * A))) :
    volume.real ({x | ENNReal.ofReal lambda < count 0 x + count 1 x} ∩ Set.Icc a b) ≤
      4 * (b - a + 2 * DyadicLineGrid.scale k) * Real.exp (-lambda / (4 * A)) := by
  have hexp : -(lambda / 2) / (2 * A) = -lambda / (4 * A) := by
    field_simp [ne_of_gt hA]
    ring
  have hq (q : ℤ) (hq : q ∈ ({0, 1} : Finset ℤ)) :
      volume.real ({x | ENNReal.ofReal (lambda / 2) < count q x} ∩ Set.Icc a b) ≤
        (2 * Real.exp (-lambda / (4 * A))) *
          (b - a + 2 * DyadicLineGrid.scale k) := by
    apply dyadic_root_tail_gluing q k hab (by positivity)
    intro j hj
    have hr := hroot q hq j hj (lambda / 2) (by positivity)
    rw [hexp] at hr
    convert hr using 1
    ring
  have h := two_count_tail_gluing volume (by simp) (count 0) (count 1) hlambda
    (hq 0 (by simp)) (hq 1 (by simp))
  convert h using 1
  ring

/-- A root scale bounded by twelve times the allowed interval length
gives an absolute global constant. This applies to `exists_root_scale`. -/
theorem two_dyadic_root_exponential_tail_scale (k : ℤ) {a b A H lambda : ℝ}
    (hab : a ≤ b) (hA : 0 < A) (hlambda : 0 ≤ lambda)
    (hscale : DyadicLineGrid.scale k ≤ 12 * H)
    (count : ℤ → ℝ → ℝ≥0∞)
    (hroot : ∀ q ∈ ({0, 1} : Finset ℤ), ∀ j ∈ DyadicLineGrid.rootBand q k a b,
      ∀ t : ℝ, 0 ≤ t →
      volume.real ({x | ENNReal.ofReal t < count q x} ∩ DyadicLineGrid.cell q k j) ≤
        2 * volume.real (DyadicLineGrid.cell q k j) * Real.exp (-t / (2 * A))) :
    volume.real ({x | ENNReal.ofReal lambda < count 0 x + count 1 x} ∩ Set.Icc a b) ≤
      96 * (b - a + H) * Real.exp (-lambda / (4 * A)) := by
  refine (two_dyadic_root_exponential_tail k hab hA hlambda count hroot).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith

end LipschitzHilbert

end

end OAI
