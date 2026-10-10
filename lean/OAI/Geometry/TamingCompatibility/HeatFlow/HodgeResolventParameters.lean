import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScaleSmoothing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalSmooth

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeWeakSolution_parameter (r s : ℝ) (hr : 0 < r) (hs' : 0 < s)
    (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr
      (r^2 • f + (s^2-r^2) • hodgeResolvent A J α hs ht s f) =
      s^2 • hodgeWeakSolution A J α hs ht s hs' f := by
  apply hodgeWeakSolution_unique A J α hs ht r hr
  intro v
  rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_left,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h := hodgeWeakSolution_identity A J α hs ht s hs' f v
  rw [hodgeResolvent_eq A J α hs ht s hs', ContinuousLinearMap.comp_apply] at h ⊢
  nlinarith only [h]

lemma hodgeResolvent_parameter (r s : ℝ) (hr : 0 < r) (hs' : 0 < s) :
    r^2 • hodgeResolvent A J α hs ht r - s^2 • hodgeResolvent A J α hs ht s =
      (r^2-s^2) • (hodgeResolvent A J α hs ht r * hodgeResolvent A J α hs ht s) := by
  ext f
  have h := congrArg (hodgeInclusion A J α hs ht)
    (hodgeWeakSolution_parameter A J α hs ht r s hr hs' f)
  rw [map_smul] at h
  simp only [← ContinuousLinearMap.comp_apply, ← hodgeResolvent_eq A J α hs ht _] at h
  simp only [map_add, map_smul] at h
  simp only [sub_apply, smul_apply,
    mul_apply_eq_comp]
  calc
    r^2 • hodgeResolvent A J α hs ht r f - s^2 • hodgeResolvent A J α hs ht s f =
      -((s^2-r^2) • hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht s f)) := by
        rw [← h]; abel
    _ = (r^2-s^2) • hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht s f) := by
      rw [← neg_smul]; congr 1; ring

lemma hodgeResolvent_commute (r s : ℝ) :
    Commute (hodgeResolvent A J α hs ht r) (hodgeResolvent A J α hs ht s) := by
  by_cases hr : 0 < r
  · by_cases hs' : 0 < s
    · by_cases hrs : r = s
      · subst s; exact Commute.refl _
      · have h := hodgeResolvent_parameter A J α hs ht r s hr hs'
        have h' := hodgeResolvent_parameter A J α hs ht s r hs' hr
        have hc : r^2 - s^2 ≠ 0 := by
          intro hz
          have hsqr : r^2 = s^2 := sub_eq_zero.mp hz
          have : r = s := (sq_eq_sq₀ hr.le hs'.le).mp hsqr
          exact hrs this
        have he : (r^2-s^2) • (hodgeResolvent A J α hs ht r * hodgeResolvent A J α hs ht s) =
            (r^2-s^2) • (hodgeResolvent A J α hs ht s * hodgeResolvent A J α hs ht r) := by
          rw [← h]
          have hn := congrArg Neg.neg h'
          simpa only [neg_sub, ← neg_smul, neg_sub] using hn
        exact (smul_right_injective _ hc he : _ = _)
    · have hz : hodgeResolvent A J α hs ht s = 1 := by simp only [hodgeResolvent, dite_eq_right hs']
      rw [hz]; exact Commute.one_right _
  · have hz : hodgeResolvent A J α hs ht r = 1 := by simp only [hodgeResolvent, dite_eq_right hr]
    rw [hz]; exact Commute.one_left _

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_eigenvalue_positive_le_one (f : L2 A J α hs ht true)
    (hf : f ≠ 0) (x : ℝ) (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    0 < x ∧ x ≤ 1 := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hp := hodgeResolvent_nonnegative A J α hs ht 1 f
  rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have hx0 : 0 ≤ x := (mul_nonneg_iff_of_pos_right (sq_pos_of_pos hn)).mp hp
  have hb := hodgeResolvent_norm_le A J α hs ht 1 f
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0] at hb
  have hx1 : x ≤ 1 := by nlinarith
  have hne : x ≠ 0 := by
    intro hz
    have hz' : hodgeResolvent A J α hs ht 1 f = hodgeResolvent A J α hs ht 1 0 := by
      rw [hx, hz, zero_smul, map_zero]
    exact hf (hodgeResolvent_injective A J α hs ht 1 zero_lt_one hz')
  exact ⟨lt_of_le_of_ne hx0 (Ne.symm hne), hx1⟩

lemma hodgeResolvent_eigenvector_parameter (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeResolvent A J α hs ht r f = (x / (r^2+(1-r^2)*x)) • f := by
  have hdpos : 0 < r^2 + (1-r^2)*x := by
    have hr2 := sq_pos_of_pos hr
    have hp := mul_nonneg hr2.le (sub_nonneg.mpr hx1)
    by_cases hz : x = 0
    · simpa only [hz, mul_zero, add_zero] using hr2
    · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
      nlinarith
  have hd := ne_of_gt hdpos
  have h := congrArg (hodgeInclusion A J α hs ht)
    (hodgeWeakSolution_parameter A J α hs ht r 1 hr zero_lt_one f)
  rw [map_smul] at h
  simp only [← ContinuousLinearMap.comp_apply, ← hodgeResolvent_eq A J α hs ht _] at h
  simp only [one_pow, one_smul, hx] at h
  rw [smul_smul, ← add_smul, map_smul] at h
  calc
    hodgeResolvent A J α hs ht r f =
        (r^2+(1-r^2)*x)⁻¹ • ((r^2+(1-r^2)*x) • hodgeResolvent A J α hs ht r f) := by
      rw [inv_smul_smul₀ hd]
    _ = (r^2+(1-r^2)*x)⁻¹ • (x • f) := by rw [h]
    _ = (x / (r^2+(1-r^2)*x)) • f := by
      rw [smul_smul]; congr 1; ring

lemma hodgeRegularization_sq_eigenvector (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    (hodgeRegularization A J α hs ht r ^ 2) f =
      (x / (r^2+(1-r^2)*x))^6 • f := by
  have he := hodgeResolvent_eigenvector_parameter A J α hs ht r hr f x hx0 hx1 hx
  have hp (n : ℕ) : (hodgeResolvent A J α hs ht r ^ n) f =
      (x / (r^2+(1-r^2)*x))^n • f := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, he, smul_smul]
      congr 1
  change ((hodgeResolvent A J α hs ht r ^ 3)^2) f = _
  rw [← pow_mul]
  exact hp 6

variable (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

lemma hodgeResolvent_eigenspaces_total :
    (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x)ᗮ = ⊥ := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (hodgeResolvent_compact A J α hs ht D hD 1 zero_lt_one)
    (hodgeResolvent_symmetric A J α hs ht 1)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
