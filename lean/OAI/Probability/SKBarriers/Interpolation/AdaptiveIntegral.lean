import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SK.Analytic

theorem integral_square_ge_square {r : ℝ → ℝ}
    (hr : ContinuousOn r (Set.Icc (0:ℝ) 1)) :
    (∫ u in (0:ℝ)..1, r u)^2 ≤ ∫ u in (0:ℝ)..1, (r u)^2 := by
  let d := ∫ u in (0:ℝ)..1, r u
  have hi := hr.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hi2 := (hr.pow 2).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have H := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (fun u => sq_nonneg (r u-d))
  have he : (fun u => (r u-d)^2) = (fun u => (r u)^2-2*d*r u+d^2) := by
    funext u; ring
  rw [he,intervalIntegral.integral_add (f := fun u => (r u)^2-2*d*r u) (g := fun _ => d^2)
    (hi2.sub (hi.const_mul (2*d))) intervalIntegrable_const,
    intervalIntegral.integral_sub (f := fun u => (r u)^2) (g := fun u => 2*d*r u) hi2 (hi.const_mul (2*d)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at H
  change 0 ≤ (∫ u in (0:ℝ)..1, (r u)^2)-2*d*d+(1-0)*d^2 at H
  dsimp only [d] at H
  nlinarith

theorem adaptive_integrated_bound {k : ℕ} (f : ℝ → ℝ) (q : ℝ → Fin (k+1) → ℝ)
    (r : ℝ → Fin (k+1) → ℝ) (e : ℝ → ℝ) (w : Fin (k+1) → ℝ)
    (hw : ∀ j, 0 ≤ w j) {c ε : ℝ} (hc : 0 ≤ c)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hr : ∀ j, ContinuousOn (fun u => r u j) (Set.Icc (0:ℝ) 1))
    (hq : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (r u) (Set.Icc (0:ℝ) 1) u)
    (hD : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f
      (c*(-1+2*r u (Fin.last k)-∑ j, w j*(r u j)^2+e u)) u)
    (he : ∀ u ∈ Set.Ioo (0:ℝ) 1, e u ≤ ε) :
    f 1-f 0 ≤ c*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
      ∑ j, w j*(q 1 j-q 0 j)^2+ε) := by
  have hqc := HasDerivWithinAt.continuousOn hq
  have hqi (j : Fin (k+1)) := (continuous_apply j).comp_continuousOn hqc
  have hri (j : Fin (k+1)) := (hr j).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hr2 (j : Fin (k+1)) := ((hr j).pow 2).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hint (j : Fin (k+1)) : (∫ u in (0:ℝ)..1, r u j) = q 1 j-q 0 j := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) (hqi j) _ (hri j)
    intro u hu
    exact hasDerivAt_pi.mp ((hq u ⟨hu.1.le,hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2)) j
  let g := fun u => c*(-1+2*r u (Fin.last k)-∑ j, w j*(r u j)^2+ε)
  have hg : ContinuousOn g (Set.Icc (0:ℝ) 1) := by
    exact continuousOn_const.mul (((continuousOn_const.add (continuousOn_const.mul (hr _))).sub
      (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul ((hr j).pow 2)))).add continuousOn_const)
  have H : f 1-f 0 ≤ ∫ u in (0:ℝ)..1, g u := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num) hf
      (fun u hu => (hD u hu).hasDerivWithinAt) hg.integrableOn_Icc
    intro u hu
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (he u hu)) hc
  have hs : (∫ u in (0:ℝ)..1, ∑ j, w j*(r u j)^2) =
      ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2) := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro j _; exact (hr2 j).const_mul (w j)
  have hsum : IntervalIntegrable (fun u => ∑ j, w j*(r u j)^2) volume 0 1 :=
    (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul ((hr j).pow 2))).intervalIntegrable_of_Icc (by norm_num)
  have hgint : (∫ u in (0:ℝ)..1, g u) =
      c*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
        ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2)+ε) := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((intervalIntegrable_const.add ((hri _).const_mul 2)).sub hsum) intervalIntegrable_const,
      intervalIntegral.integral_sub (intervalIntegrable_const.add ((hri _).const_mul 2)) hsum,
      intervalIntegral.integral_add intervalIntegrable_const ((hri _).const_mul 2),
      intervalIntegral.integral_const_mul,hs,hint]
    simp
  rw [hgint] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ hc
  have hx : (∑ j, w j*(q 1 j-q 0 j)^2) ≤
      ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2) := by
    apply Finset.sum_le_sum
    intro j _
    have HH := integral_square_ge_square (hr j)
    rw [hint] at HH
    exact mul_le_mul_of_nonneg_left HH (hw j)
  linarith
end SK.Analytic

end
end

end

end OAI
