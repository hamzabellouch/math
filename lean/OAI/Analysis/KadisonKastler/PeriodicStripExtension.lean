import OAI.Analysis.KadisonKastler.HorizontalStripGluing
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! # A bounded holomorphic strip with matching boundary values is constant

The matching edges give a periodic extension. The preceding rectangular
Morera argument removes the seams, and Liouville applies to the extension.
-/

namespace KadisonKastler

open Complex Set
open scoped Topology

noncomputable section

def periodicStripExtension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (z - (⌊z.im⌋ : ℂ) * I)

theorem periodicStripExtension_eq {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (k : ℤ) {z : ℂ} (hz : (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1) :
    periodicStripExtension f z = f (z - (k : ℂ) * I) := by
  by_cases hlt : z.im < (k : ℝ) + 1
  · rw [periodicStripExtension, Int.floor_eq_iff.mpr ⟨hz.1, hlt⟩]
  · have hi : z.im = ((k + 1 : ℤ) : ℝ) := by push_cast; linarith [hz.2]
    have hfloor : ⌊z.im⌋ = k + 1 := by rw [hi, Int.floor_intCast]
    have h₁ : z - ((k + 1 : ℤ) : ℂ) * I = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have h₂ : z - (k : ℂ) * I = (z.re : ℂ) + I := by
      apply Complex.ext <;> simp [hi]
    rw [periodicStripExtension, hfloor, h₁, h₂, he]

private theorem periodicStripExtension_continuousOn_cell {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1}) (k : ℤ) :
    ContinuousOn (periodicStripExtension f)
      {z | (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1} := by
  have hmap : MapsTo (fun z : ℂ => z - (k : ℂ) * I)
      {z | (k : ℝ) ≤ z.im ∧ z.im ≤ (k : ℝ) + 1}
      {z | 0 ≤ z.im ∧ z.im ≤ 1} := by
    intro z hz
    change 0 ≤ (z - (k : ℂ) * I).im ∧ (z - (k : ℂ) * I).im ≤ 1
    simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
      mul_one, mul_zero, add_zero]
    constructor <;> linarith [hz.1, hz.2]
  exact (hc.comp (by fun_prop) hmap).congr
    (fun z hz => periodicStripExtension_eq he k hz)

theorem periodicStripExtension_continuous {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1}) :
    Continuous (periodicStripExtension f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let k : ℤ := ⌊z.im⌋
  have hlo : (k : ℝ) ≤ z.im := Int.floor_le _
  have hhi : z.im < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hclosed (j : ℤ) : IsClosed {w : ℂ | (j : ℝ) ≤ w.im ∧ w.im ≤ (j : ℝ) + 1} :=
    isClosed_Icc.preimage continuous_im
  have hu := (periodicStripExtension_continuousOn_cell he hc (k - 1)).union_of_isClosed
    (periodicStripExtension_continuousOn_cell he hc k) (hclosed _) (hclosed _)
  apply hu.continuousAt
  apply Filter.mem_of_superset
    ((isOpen_Ioo.preimage continuous_im).mem_nhds
      (show (k : ℝ) - 1 < z.im ∧ z.im < (k : ℝ) + 1 by constructor <;> linarith))
  intro w hw
  by_cases hwk : w.im ≤ (k : ℝ)
  · left
    change ((k - 1 : ℤ) : ℝ) ≤ w.im ∧ w.im ≤ ((k - 1 : ℤ) : ℝ) + 1
    push_cast
    constructor <;> linarith [hw.1]
  · right
    exact ⟨by linarith, hw.2.le⟩

private theorem periodicStripExtension_differentiableAt_cell {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (k : ℤ) {z : ℂ} (hz : (k : ℝ) < z.im ∧ z.im < (k : ℝ) + 1) :
    DifferentiableAt ℂ (periodicStripExtension f) z := by
  have hm : 0 < (z - (k : ℂ) * I).im ∧ (z - (k : ℂ) * I).im < 1 := by
    simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
      mul_one, mul_zero, add_zero]
    constructor <;> linarith [hz.1, hz.2]
  have hf := (hd.differentiableAt ((isOpen_Ioo.preimage continuous_im).mem_nhds hm)).comp z
    (show DifferentiableAt ℂ (fun w : ℂ => w - (k : ℂ) * I) z by fun_prop)
  apply hf.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage continuous_im).mem_nhds hz] with w hw
  exact periodicStripExtension_eq he k ⟨hw.1.le, hw.2.le⟩

theorem periodicStripExtension_differentiable {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1}) :
    Differentiable ℂ (periodicStripExtension f) := by
  intro z
  let k : ℤ := ⌊z.im⌋
  have hlo : (k : ℝ) ≤ z.im := Int.floor_le _
  have hhi : z.im < (k : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hlt : (k : ℝ) < z.im
  · exact periodicStripExtension_differentiableAt_cell he hd k ⟨hlt, hhi⟩
  · have heq : z.im = (k : ℝ) := le_antisymm (le_of_not_gt hlt) hlo
    have hg := differentiableOn_horizontal_strip_glue
      (f := periodicStripExtension f) (a := (k : ℝ) - 1) (b := (k : ℝ) + 1)
      (s := (k : ℝ)) (by linarith) (by linarith)
      (periodicStripExtension_continuous he hc).continuousOn ?_
    · exact hg.differentiableAt
        ((isOpen_Ioo.preimage continuous_im).mem_nhds (by simp [heq]))
    · intro w hw₁ hw₂ hne
      by_cases hlow : w.im < (k : ℝ)
      · apply periodicStripExtension_differentiableAt_cell he hd (k - 1)
        push_cast
        exact ⟨hw₁, by linarith⟩
      · exact periodicStripExtension_differentiableAt_cell he hd k
          ⟨lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hne), hw₂⟩

/-- The exact scalar uniqueness statement needed after normalizing a KMS strip. -/
theorem bounded_matching_strip_constant {f : ℂ → ℂ}
    (he : ∀ t : ℝ, f ((t : ℂ) + I) = f t)
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hb : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = f 0 := by
  obtain ⟨C, hC⟩ := hb
  have hbound : Bornology.IsBounded (Set.range (periodicStripExtension f)) := by
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    apply hC
    · simpa only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
        mul_one, mul_zero, add_zero] using sub_nonneg.mpr (Int.floor_le z.im)
    · simp only [sub_im, mul_im, intCast_re, I_im, intCast_im, I_re,
        mul_one, mul_zero, add_zero]
      linarith [Int.lt_floor_add_one z.im]
  intro z hz₁ hz₂
  have h := (periodicStripExtension_differentiable he hc hd).apply_eq_apply_of_bounded hbound z 0
  have hz' : periodicStripExtension f z = f z := by
    simpa using periodicStripExtension_eq (f := f) he (0 : ℤ) (z := z)
      (by simpa using And.intro hz₁ hz₂)
  rw [hz'] at h
  simpa [periodicStripExtension] using h

end

end KadisonKastler

end OAI
