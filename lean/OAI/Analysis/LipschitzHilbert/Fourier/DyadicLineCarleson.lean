import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineBad
import OAI.Analysis.LipschitzHilbert.Estimates.BinCarleson

namespace OAI

/-! The actual maximal bad intervals satisfy the finite Carleson bound. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

theorem maximal_bad_carleson {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    {P : Set ℝ} (hP : MeasurableSet P) (hPfinite : volume P ≠ ∞)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ P) :
    (∑ i, volume.real (cell q (level i) (pos i))) ≤ (C / β) * volume.real P := by
  apply finite_bin_carleson_of_finite_sums (fun i => cell q (level i) (pos i)) bin f volume
    hP hPfinite (fun i => cell_measurable q (level i) (pos i)) hsub
    (fun b => integrableOn_of_unit_bound (hf b) (hbound b) hPfinite)
    (fun b x => (hbound b x).1)
  · intro i j hij hb
    apply maximalBad_disjoint (hmax i)
    · simpa only [← hb] using hmax j
    · intro hcoords
      exact hij (hunique i j hb (congrArg Prod.fst hcoords) (congrArg Prod.snd hcoords))
  · exact hβ
  · intro s x _
    exact hsum s x
  · intro i
    rw [cell_length]
    exact (hmax i).2.1

/-- Restricting a finite family of occurrences to any finite-measure test
set preserves the same Carleson constant. -/
theorem maximal_bad_carleson_restricted {ι B : Type*} [Fintype ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    {P : Set ℝ} (hP : MeasurableSet P) (hPfinite : volume P ≠ ∞) :
    (∑ i, if cell q (level i) (pos i) ⊆ P then volume.real (cell q (level i) (pos i)) else 0) ≤
      (C / β) * volume.real P := by
  classical
  let s := Finset.univ.filter (fun i => cell q (level i) (pos i) ⊆ P)
  have h := maximal_bad_carleson (ι := s) q top f (fun i => bin i.1)
    (fun i => level i.1) (fun i => pos i.1)
    (fun i j hb hl hp => Subtype.ext (hunique i.1 j.1 hb hl hp))
    hβ (fun i => hmax i.1) hf hbound hsum hP hPfinite
    (fun i => (Finset.mem_filter.mp i.property).2)
  have heq : (∑ i : s, volume.real (cell q (level i.1) (pos i.1))) =
      ∑ i ∈ s, volume.real (cell q (level i) (pos i)) :=
    (Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => volume.real (cell q (level i) (pos i)))).symm
  rw [heq] at h
  simpa only [s, Finset.sum_filter] using h

end LipschitzHilbert.DyadicLineGrid

end

end OAI
