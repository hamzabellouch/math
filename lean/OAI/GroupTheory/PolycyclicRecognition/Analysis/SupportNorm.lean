import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace OAI

/-!
# The norm obtained from weighted nilpotent boxes

For a bracket-word basis, each generator occurs with a positive integral
multiplicity. Unimodularity says that the corresponding weighted sum of
characters is zero. The support exponent of a segment is the maximum, over
these bases, of the weighted positive parts of the characters. This finite
data yields the support norm identities.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

/-- The finite algebraic data of the segment-support formula. -/
structure SupportDatum (W I B : Type*) [AddCommGroup W] [Module ℝ W]
    [Fintype I] [Fintype B] where
  weight : I → W →ₗ[ℝ] ℝ
  multiplicity : B → I → ℕ
  positive : ∀ b i, 0 < multiplicity b i
  balanced : ∀ b w, ∑ i, (multiplicity b i : ℝ) * weight i w = 0
  separates : ∀ w, (∀ i, weight i w = 0) → w = 0

namespace SupportDatum

variable (D : SupportDatum W I B)

/-- The support exponent contributed by one bracket-word basis. -/
noncomputable def basisSupport (b : B) (w : W) : ℝ :=
  ∑ i, (D.multiplicity b i : ℝ) * max 0 (D.weight i w)

/-- The support exponent of the segment from zero to `w`. -/
noncomputable def segmentSupport (w : W) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => D.basisSupport b w)

omit [Nonempty B] in
theorem basisSupport_nonneg (b : B) (w : W) : 0 ≤ D.basisSupport b w := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)

theorem basisSupport_le (b : B) (w : W) :
    D.basisSupport b w ≤ D.segmentSupport w := by
  exact Finset.le_sup' (f := fun b => D.basisSupport b w) (Finset.mem_univ b)

theorem segmentSupport_le {w : W} {r : ℝ}
    (h : ∀ b, D.basisSupport b w ≤ r) : D.segmentSupport w ≤ r := by
  exact Finset.sup'_le _ _ fun b _ => h b

theorem segmentSupport_nonneg (w : W) : 0 ≤ D.segmentSupport w := by
  obtain ⟨b⟩ := ‹Nonempty B›
  exact (D.basisSupport_nonneg b w).trans (D.basisSupport_le b w)

omit [Nonempty B] in
@[simp] theorem basisSupport_zero (b : B) : D.basisSupport b 0 = 0 := by
  simp [basisSupport]

@[simp] theorem segmentSupport_zero : D.segmentSupport 0 = 0 := by
  apply le_antisymm (D.segmentSupport_le fun b => (D.basisSupport_zero b).le)
  exact D.segmentSupport_nonneg 0

omit [Nonempty B] in
theorem basisSupport_neg (b : B) (w : W) :
    D.basisSupport b (-w) = D.basisSupport b w := by
  have hpart (a : ℝ) : max 0 (-a) = max 0 a - a := by
    rcases le_total 0 a with ha | ha
    · rw [max_eq_right ha, max_eq_left (neg_nonpos.mpr ha)]
      ring
    · rw [max_eq_left ha, max_eq_right (neg_nonneg.mpr ha)]
      ring
  simp only [basisSupport, map_neg, hpart, mul_sub, Finset.sum_sub_distrib]
  rw [D.balanced, sub_zero]

@[simp] theorem segmentSupport_neg (w : W) :
    D.segmentSupport (-w) = D.segmentSupport w := by
  simp only [segmentSupport, D.basisSupport_neg]

omit [Nonempty B] in
theorem basisSupport_add_le (b : B) (v w : W) :
    D.basisSupport b (v + w) ≤ D.basisSupport b v + D.basisSupport b w := by
  simp only [basisSupport, map_add, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply max_le
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)

theorem segmentSupport_add_le (v w : W) :
    D.segmentSupport (v + w) ≤ D.segmentSupport v + D.segmentSupport w := by
  apply D.segmentSupport_le
  intro b
  exact (D.basisSupport_add_le b v w).trans
    (add_le_add (D.basisSupport_le b v) (D.basisSupport_le b w))

omit [Nonempty B] in
theorem basisSupport_smul_of_nonneg (b : B) (w : W) {r : ℝ} (hr : 0 ≤ r) :
    D.basisSupport b (r • w) = r * D.basisSupport b w := by
  simp only [basisSupport, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmax := mul_max_of_nonneg 0 (D.weight i w) hr
  rw [mul_zero] at hmax
  rw [← hmax]
  ring

theorem segmentSupport_smul_of_nonneg (w : W) {r : ℝ} (hr : 0 ≤ r) :
    D.segmentSupport (r • w) = r * D.segmentSupport w := by
  apply le_antisymm
  · apply D.segmentSupport_le
    intro b
    rw [D.basisSupport_smul_of_nonneg b w hr]
    exact mul_le_mul_of_nonneg_left (D.basisSupport_le b w) hr
  · obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun b => D.basisSupport b w)
    change r * Finset.univ.sup' _ _ ≤ _
    rw [heq, ← D.basisSupport_smul_of_nonneg b w hr]
    exact D.basisSupport_le b (r • w)

theorem segmentSupport_smul (w : W) (r : ℝ) :
    D.segmentSupport (r • w) = |r| * D.segmentSupport w := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, D.segmentSupport_smul_of_nonneg w hr]
  · rw [abs_of_nonpos hr, ← D.segmentSupport_neg (r • w), ← neg_smul]
    exact D.segmentSupport_smul_of_nonneg w (neg_nonneg.mpr hr)

omit [Nonempty B] in
theorem weight_eq_zero_of_basisSupport_eq_zero (b : B) (w : W)
    (h : D.basisSupport b w = 0) (i : I) : D.weight i w = 0 := by
  have hpos (v : W) (hv : D.basisSupport b v = 0) : D.weight i v ≤ 0 := by
    have hterm : (D.multiplicity b i : ℝ) * max 0 (D.weight i v) ≤ 0 := by
      calc
        _ ≤ D.basisSupport b v := Finset.single_le_sum
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)) (Finset.mem_univ i)
        _ = 0 := hv
    have hm : (0 : ℝ) < D.multiplicity b i := Nat.cast_pos.mpr (D.positive b i)
    have hmax : max 0 (D.weight i v) ≤ 0 := by nlinarith
    exact (le_max_right _ _).trans hmax
  apply le_antisymm (hpos w h)
  have hn := hpos (-w) ((D.basisSupport_neg b w).trans h)
  simpa only [map_neg, neg_nonpos] using hn

@[simp] theorem segmentSupport_eq_zero_iff (w : W) :
    D.segmentSupport w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    obtain ⟨b⟩ := ‹Nonempty B›
    apply D.separates w
    intro i
    apply D.weight_eq_zero_of_basisSupport_eq_zero b w _ i
    exact le_antisymm ((D.basisSupport_le b w).trans_eq hw) (D.basisSupport_nonneg b w)
  · rintro rfl
    exact D.segmentSupport_zero

theorem segmentSupport_pos {w : W} (hw : w ≠ 0) : 0 < D.segmentSupport w := by
  exact lt_of_le_of_ne (D.segmentSupport_nonneg w)
    (Ne.symm fun h => hw ((D.segmentSupport_eq_zero_iff w).mp h))

/-- The segment support is an actual real vector-space norm. This construction
does not install a new topology on a space carrying an existing norm. -/
theorem normCore : letI : Norm W := ⟨D.segmentSupport⟩; NormedSpace.Core ℝ W := by
  let : Norm W := ⟨D.segmentSupport⟩
  exact
    { norm_nonneg := D.segmentSupport_nonneg
      norm_smul := fun r w => by simpa only [Real.norm_eq_abs] using D.segmentSupport_smul w r
      norm_triangle := D.segmentSupport_add_le
      norm_eq_zero_iff := D.segmentSupport_eq_zero_iff }

end SupportDatum
end PolycyclicRecognition

end OAI
