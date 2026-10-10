import OAI.NumberTheory.TwoPoint.Bounds.Nonbacktracking
import OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Star.BigOperators

namespace OAI

/-!
# The resolvent path for noncommuting edge operators

The definitions and lemmas here implement the path used in manuscript
Lemma `q:noncommuting`. The only products that are commuted are an edge
operator and its own resolvent.
-/

open scoped BigOperators NNReal ENNReal

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def edgeResolvent (B : E →L[ℂ] E) (u : ℝ) : E →L[ℂ] E :=
  Ring.inverse (1 + u • B)

noncomputable def transferResolvent (B : ι → E →L[ℂ] E) (u : ℝ) : E →L[ℂ] E :=
  1 - ∑ i, u • (B i * edgeResolvent (B i) u)

noncomputable def nonbacktrackingContinuous (B : ι → E →L[ℂ] E) :
    (ι → E) →L[ℂ] (ι → E) :=
  (nonbacktracking (fun i => (B i).toLinearMap)).toContinuousLinearMap

lemma isUnit_edge_shift (B : E →L[ℂ] E) (u : ℝ) (h : ‖u • B‖ < 1) :
    IsUnit (1 + u • B) := by
  simpa only [norm_neg, sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one (x := -(u • B)) (by simpa using h))

omit [FiniteDimensional ℂ E] in
lemma edgeResolvent_mul (B : E →L[ℂ] E) (u : ℝ) (h : IsUnit (1 + u • B)) :
    (1 + u • B) * edgeResolvent B u = 1 :=
  Ring.mul_inverse_cancel _ h

omit [FiniteDimensional ℂ E] in
lemma edgeResolvent_commute (B : E →L[ℂ] E) (u : ℝ) (h : IsUnit (1 + u • B)) :
    B * edgeResolvent B u = edgeResolvent B u * B := by
  let A := 1 + u • B
  let R := edgeResolvent B u
  have hAR : A * R = 1 := Ring.mul_inverse_cancel _ h
  have hRA : R * A = 1 := Ring.inverse_mul_cancel _ h
  have hAB : A * B = B * A := by
    simp [A, add_mul, mul_add]
  calc
    B * R = (R * A) * (B * R) := by rw [hRA, one_mul]
    _ = R * (A * B) * R := by simp only [mul_assoc]
    _ = R * (B * A) * R := by rw [hAB]
    _ = (R * B) * (A * R) := by simp only [mul_assoc]
    _ = R * B := by rw [hAR, mul_one]

omit [DecidableEq ι] in
lemma transferResolvent_selfAdjoint (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) : IsSelfAdjoint (transferResolvent B u) := by
  unfold transferResolvent
  apply IsSelfAdjoint.sub (by simp)
  apply isSelfAdjoint_sum
  intro i _
  apply (isSelfAdjoint_iff.mpr (by rfl) : IsSelfAdjoint u).smul
  have hR : IsSelfAdjoint (edgeResolvent (B i) u) :=
    ((IsSelfAdjoint.one (E →L[ℂ] E)).add ((isSelfAdjoint_iff.mpr (by rfl) : IsSelfAdjoint u).smul
      (hB i))).ringInverse
  change star (B i * edgeResolvent (B i) u) = B i * edgeResolvent (B i) u
  rw [star_mul, hR.star_eq, (hB i).star_eq]
  exact (edgeResolvent_commute (B i) u (hunit i)).symm

lemma clm_injective_of_isUnit {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (T : V →L[ℂ] V) (h : IsUnit T) : Function.Injective T := by
  obtain ⟨v, rfl⟩ := h
  exact (ContinuousLinearEquiv.ofUnit v).injective

theorem transferResolvent_injective (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i))
    (hH : IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B)) :
    Function.Injective (transferResolvent B u) := by
  have hR (i : ι) (v : E) : edgeResolvent (B i) u v +
      (u : ℂ) • B i (edgeResolvent (B i) u v) = v := by
    have h := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_mul (B i) u (hunit i))
    simpa using h
  have h := resolvent_transfer_injective (fun i => (B i).toLinearMap) (u : ℂ)
    (fun i => (edgeResolvent (B i) u).toLinearMap) hR
    (clm_injective_of_isUnit (1 - (u : ℂ) • nonbacktrackingContinuous B) hH)
  intro v w hvw
  apply h
  change v - ∑ i, u • B i (edgeResolvent (B i) u v) =
    w - ∑ i, u • B i (edgeResolvent (B i) u w)
  simpa only [transferResolvent, sub_apply, one_apply_eq_self, sum_apply,
    smul_apply, mul_apply_eq_comp] using hvw

omit [DecidableEq ι] in
theorem transferResolvent_continuousOn (B : ι → E →L[ℂ] E) (a b : ℝ)
    (hunit : ∀ u ∈ Set.Icc a b, ∀ i, IsUnit (1 + u • B i)) :
    ContinuousOn (transferResolvent B) (Set.Icc a b) := by
  apply continuousOn_const.sub
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_id.smul
  apply continuousOn_const.mul
  intro u hu
  obtain ⟨v, hv⟩ := hunit u hu i
  have hi := NormedRing.inverse_continuousAt v
  rw [hv] at hi
  have hc : ContinuousWithinAt (fun s : ℝ => (1 : E →L[ℂ] E) + s • B i)
      (Set.Icc a b) u := by fun_prop
  change ContinuousWithinAt (fun s : ℝ => Ring.inverse ((1 : E →L[ℂ] E) + s • B i))
    (Set.Icc a b) u
  exact ContinuousAt.comp_continuousWithinAt (g := Ring.inverse) hi hc

/-- The positivity step of the nonbacktracking spectral transfer. -/
theorem transferResolvent_positive [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (t : ℝ) (ht : 0 ≤ t)
    (hsmall : ∀ u ∈ Set.Icc 0 t, ∀ i, ‖u • B i‖ < 1)
    (hH : ∀ u ∈ Set.Icc 0 t,
      IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B)) :
    ∀ v : E, v ≠ 0 → 0 < (inner ℂ (transferResolvent B t v) v).re := by
  have hu : ∀ u ∈ Set.Icc 0 t, ∀ i, IsUnit (1 + u • B i) :=
    fun u hu i => isUnit_edge_shift _ _ (hsmall u hu i)
  apply selfAdjoint_path_positive (transferResolvent B) 0 t ht
    (transferResolvent_continuousOn B 0 t hu)
  · ext v
    simp [transferResolvent]
  · intro u hu'
    exact (transferResolvent_selfAdjoint B hB u (hu u hu')).isSymmetric
  · intro u hu'
    exact transferResolvent_injective B u (hu u hu') (hH u hu')

lemma edgeResolvent_norm_le_two [Nontrivial E] (B : E →L[ℂ] E) (u : ℝ)
    (hnorm : ‖u • B‖ ≤ 1 / 2) : ‖edgeResolvent B u‖ ≤ 2 := by
  let x : E →L[ℂ] E := -(u • B)
  have hx : ‖x‖ < 1 := by simpa [x] using hnorm.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound := tsum_geometric_le_of_norm_lt_one x hx
  have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖x‖)).mpr
    have : ‖x‖ ≤ 1 / 2 := by simpa [x] using hnorm
    linarith
  have heq : edgeResolvent B u = ↑(Units.oneSub x hx)⁻¹ := by
    simpa [edgeResolvent, x] using NormedRing.inverse_one_sub x hx
  rw [heq]
  change ‖∑' n : ℕ, x ^ n‖ ≤ 2
  simpa only [norm_one, sub_self, zero_add] using hbound.trans
    (show ‖(1 : E →L[ℂ] E)‖ - 1 + (1 - ‖x‖)⁻¹ ≤ 2 by simpa using hinv)

lemma nonbacktracking_resolvent_isUnit (B : ι → E →L[ℂ] E) (m : ℝ≥0)
    (hm : 0 < m) (hrad : spectralRadius ℂ (nonbacktrackingContinuous B) ≤ (m : ℝ≥0∞))
    (u : ℝ) (hu : |u| < (m : ℝ)⁻¹) :
    IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B) := by
  apply spectrum.isUnit_one_sub_smul_of_lt_inv_radius (𝕜 := ℂ)
    (a := nonbacktrackingContinuous B) (z := (u : ℂ))
  apply lt_of_lt_of_le _ (ENNReal.inv_le_inv.mpr hrad)
  have hnn : ‖(u : ℂ)‖₊ < m⁻¹ := by
    exact_mod_cast (by simpa using hu : ‖(u : ℂ)‖ < ((m⁻¹ : ℝ≥0) : ℝ))
  rw [← ENNReal.coe_inv hm.ne']
  exact_mod_cast hnn

end TwoPointCorrelations

end OAI
