import OAI.Geometry.NodalSets.Elliptic.RealCompactH1Approximation
import OAI.Geometry.NodalSets.Elliptic.RealSquareCutoffWeakGradient
import OAI.Geometry.NodalSets.Elliptic.RealWeakDifferenceBound

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_cutoff_pointwise_bound (a t r : ℝ) (ha : |a| ≤ 1) :
    (a*(t+2*r))^2 ≤ 2*t^2+8*r^2 := by
  have hsq : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).mpr ha
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (t+2*r))
  nlinarith [sq_nonneg (t-2*r)]

theorem real_square_cutoff_gradient_energy {n : ℕ} (eta q : Coord n → ℝ)
    (V : Fin n → Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hb : ∀ x, |eta x| ≤ 1) (hq : MemLp q 2 volume) (hV : ∀ j, MemLp (V j) 2 volume) :
    let T := fun j x ↦ eta x*V j x
    let R := fun j x ↦ coordPartial eta x j*q x
    let P := realSquareCutoffGradient eta q V
    (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    (∑ j, ∫ x, (P j x)^2) ≤
      2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  have hT (j : Fin n) : MemLp (fun x ↦ eta x*V j x) 2 volume :=
    real_compact_localL2_product hc eta (V j) he.continuous Subset.rfl ((hV j).restrict _)
  have hR (j : Fin n) : MemLp (fun x ↦ coordPartial eta x j*q x) 2 volume :=
    real_compact_localL2_product hc _ q (real_coordPartial_smooth eta he j).continuous
      (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)) (hq.restrict _)
  have hid (j : Fin n) : realSquareCutoffGradient eta q V j =
      fun x ↦ eta x*((eta x*V j x)+2*(coordPartial eta x j*q x)) := by
    funext x; unfold realSquareCutoffGradient; ring
  have hP (j : Fin n) : MemLp (realSquareCutoffGradient eta q V j) 2 volume := by
    rw [hid]
    exact real_compact_localL2_product hc eta _ he.continuous Subset.rfl
      (((hT j).add ((hR j).const_mul 2)).restrict _)
  refine ⟨fun j ↦ ⟨hT j,hR j,hP j⟩,?_⟩
  have hle (j : Fin n) : (∫ x, (realSquareCutoffGradient eta q V j x)^2) ≤
      2*(∫ x, (eta x*V j x)^2)+8*(∫ x, (coordPartial eta x j*q x)^2) := by
    rw [← integral_const_mul,← integral_const_mul,
      ← integral_add ((hT j).integrable_sq.const_mul 2) ((hR j).integrable_sq.const_mul 8)]
    apply integral_mono (hP j).integrable_sq
      (((hT j).integrable_sq.const_mul 2).add ((hR j).integrable_sq.const_mul 8))
    intro x
    rw [hid]
    exact real_square_cutoff_pointwise_bound _ _ _ (hb x)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hle j)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using hsum

theorem real_compact_weak_test_difference_energy {n : ℕ} (v : Coord n → ℝ)
    (P T R : Fin n → Coord n → ℝ) (hv : MemLp v 2 volume) (hc : HasCompactSupport v)
    (hP : ∀ j, MemLp (P j) 2 volume)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, v x*coordPartial psi x j)=-(∫ x, P j x*psi x))
    (hbound : (∑ j, ∫ x, (P j x)^2) ≤
      2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2)) (i : Fin n) (h : ℝ) :
    MemLp (realDifferenceQuotient i h v) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h v x)^2) ≤
        2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  have hd := real_weak_derivative_difference_bound v (P i)
    (real_compact_memLp_integrable v hv hc) hv (hP i) i (hw i) h
  refine ⟨hd.1,hd.2.trans (le_trans ?_ hbound)⟩
  exact Finset.single_le_sum (f := fun j ↦ ∫ x, (P j x)^2)
    (fun j _ ↦ integral_nonneg (fun x ↦ sq_nonneg (P j x))) (Finset.mem_univ i)

end
end Yau

end OAI
