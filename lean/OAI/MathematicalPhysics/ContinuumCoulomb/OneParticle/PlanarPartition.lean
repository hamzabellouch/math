import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarIMS
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

/-! A smooth square partition for finitely many disjoint planar cutoffs.
The exterior function is smooth even on the regions where all site cutoffs
vanish; no square root at a zero is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarTrigPartition {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) : Option ι → PlanarPosition → ℝ
  | none => fun x => 1 + ∑ i, (Real.cos (χ i x) - 1)
  | some i => fun x => Real.sin (χ i x)

theorem planarTrigPartition_C1 {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (i : Option ι) : ContDiff ℝ 1 (planarTrigPartition χ i) := by
  cases i with
  | none => exact contDiff_const.add (ContDiff.sum (fun i _ => (hχ i).cos.sub contDiff_const))
  | some i => exact (hχ i).sin

theorem disjoint_cutoff_vanish {ι : Type*}
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {i j : ι} {x : PlanarPosition} (hxi : x ∈ tsupport (χ i)) (hji : j ≠ i)
    (e : PlanarPosition) : χ j x = 0 ∧ planarPartial (χ j) e x = 0 := by
  have hxj : x ∉ tsupport (χ j) :=
    fun hxj => Set.disjoint_left.mp (hdisj i j hji.symm) hxi hxj
  refine ⟨image_eq_zero_of_notMem_tsupport hxj, ?_⟩
  simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hxj, zero_apply]

theorem planarTrigPartition_exterior_at {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {i : ι} {x : PlanarPosition} (hxi : x ∈ tsupport (χ i)) :
    planarTrigPartition χ none x = Real.cos (χ i x) := by
  classical
  dsimp only [planarTrigPartition]
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [(disjoint_cutoff_vanish χ hdisj hxi hji 0).1, Real.cos_zero, sub_self]
  · simp

/-- The exterior and all site members have square sum exactly one. -/
theorem planarTrigPartition_square_sum {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (x : PlanarPosition) : ∑ i, planarTrigPartition χ i x ^ 2 = 1 := by
  classical
  rw [Fintype.sum_option]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    rw [planarTrigPartition_exterior_at χ hdisj hi]
    have hs : (∑ j, planarTrigPartition χ (some j) x ^ 2) = Real.sin (χ i x) ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp only [planarTrigPartition, (disjoint_cutoff_vanish χ hdisj hi hji 0).1,
          Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      · simp
    rw [hs]
    nlinarith [Real.sin_sq_add_cos_sq (χ i x)]
  · have hz (i : ι) : χ i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hx ⟨i, hi⟩)
    simp only [planarTrigPartition, hz, Real.cos_zero, Real.sin_zero, sub_self,
      Finset.sum_const_zero, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]

theorem planarTrigPartition_partial_site {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (i : ι) (e x : PlanarPosition) :
    planarPartial (planarTrigPartition χ (some i)) e x =
      Real.cos (χ i x) * planarPartial (χ i) e x := by
  dsimp only [planarTrigPartition, planarPartial]
  rw [fderiv_sin ((hχ i).differentiable (by norm_num) x)]
  rfl

theorem planarTrigPartition_partial_exterior {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (e x : PlanarPosition) :
    planarPartial (planarTrigPartition χ none) e x =
      -(∑ i, Real.sin (χ i x) * planarPartial (χ i) e x) := by
  have hd (i : ι) : HasFDerivAt (fun y => Real.cos (χ i y) - 1)
      (-Real.sin (χ i x) • fderiv ℝ (χ i) x) x := by
    simpa only [sub_zero, Pi.sub_def] using
      (((hχ i).differentiable (by norm_num) x).hasFDerivAt.cos.sub (hasFDerivAt_const 1 x))
  have hs := (hasFDerivAt_const (1 : ℝ) x).add
    (HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hd i))
  have he := congrArg (fun L : PlanarPosition →L[ℝ] ℝ => L e) hs.fderiv
  simpa only [planarTrigPartition, planarPartial, zero_add, sum_apply, smul_apply,
    smul_eq_mul, neg_mul, Finset.sum_neg_distrib, Pi.add_def, Pi.sub_def] using he

/-- Disjoint supports prevent a factor equal to the number of wells in the
localization error: the square gradient equals that of the active angle. -/
theorem planarTrigPartition_gradient_square {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (e x : PlanarPosition) :
    (∑ i, planarPartial (planarTrigPartition χ i) e x ^ 2) =
      ∑ i, planarPartial (χ i) e x ^ 2 := by
  classical
  rw [Fintype.sum_option, planarTrigPartition_partial_exterior χ hχ]
  simp_rw [planarTrigPartition_partial_site χ hχ]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    have hz (j : ι) (hji : j ≠ i) : planarPartial (χ j) e x = 0 :=
      (disjoint_cutoff_vanish χ hdisj hi hji e).2
    have hs : (∑ j, Real.sin (χ j x) * planarPartial (χ j) e x) =
        Real.sin (χ i x) * planarPartial (χ i) e x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, mul_zero]
      · simp
    have hc : (∑ j, (Real.cos (χ j x) * planarPartial (χ j) e x) ^ 2) =
        (Real.cos (χ i x) * planarPartial (χ i) e x) ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      · simp
    have hg : (∑ j, planarPartial (χ j) e x ^ 2) = planarPartial (χ i) e x ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hz j hji, zero_pow (by decide : 2 ≠ 0)]
      · simp
    rw [hs, hc, hg]
    calc
      _ = (Real.sin (χ i x) ^ 2 + Real.cos (χ i x) ^ 2) * planarPartial (χ i) e x ^ 2 := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · have hz (i : ι) : planarPartial (χ i) e x = 0 := by
      have hi : x ∉ tsupport (χ i) := fun hi => hx ⟨i, hi⟩
      simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hi, zero_apply]
    simp only [hz, mul_zero, Finset.sum_const_zero, neg_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]

theorem planarTrigPartition_gradient_bound {ι : Type*} [Fintype ι]
    (χ : ι → PlanarPosition → ℝ) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {G : ℝ} (hG : 0 ≤ G) (e : PlanarPosition)
    (hbound : ∀ i x, |planarPartial (χ i) e x| ≤ G) (x : PlanarPosition) :
    (∑ i, planarPartial (planarTrigPartition χ i) e x ^ 2) ≤ G ^ 2 := by
  classical
  rw [planarTrigPartition_gradient_square χ hχ hdisj]
  by_cases hx : ∃ i, x ∈ tsupport (χ i)
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hG).mpr (hbound i x)
    · intro j _ hji
      rw [(disjoint_cutoff_vanish χ hdisj hi hji e).2, zero_pow (by decide : 2 ≠ 0)]
    · simp
  · have hz (i : ι) : planarPartial (χ i) e x = 0 := by
      have hi : x ∉ tsupport (χ i) := fun hi => hx ⟨i, hi⟩
      simp only [planarPartial, fderiv_of_notMem_tsupport ℝ hi, zero_apply]
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact sq_nonneg G

end ContinuumCoulomb

end

end OAI
