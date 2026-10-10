import OAI.Analysis.CircleDomains.Topology.CircleCovectors

namespace OAI

/-!
# Actual cutoff differential of a periodic coordinate

The same covector formula used by the random-grid estimate is the
intrinsic differential of the descended circle cutoff. Its scalar input
can be the bounded canonical representative; integer changes of branch
do not change either the multiplier or the error term.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem deriv_map_add_int_of_add_one {P : ℝ → ℝ}
    (hP : ∀ x, P (x + 1) = P x + 1) (x : ℝ) (m : ℤ) :
    deriv P (x + (m : ℝ)) = deriv P x := by
  have heq : (fun y => P (y + (m : ℝ))) = (fun y => P y + (m : ℝ)) :=
    funext (fun y => map_add_int_of_add_one hP y m)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  simpa only [deriv_comp_add_const, deriv_add_const] using hd

theorem staircaseCovector_reciprocal_add_int
    (N : ℕ) (δ χ θ x : ℝ) (m : ℤ) (u c : ℝ × ℝ) :
    staircaseCovector (reciprocalGridStep N) δ χ θ (x + (m : ℝ)) u c =
      staircaseCovector (reciprocalGridStep N) δ χ θ x u c := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  unfold staircaseCovector
  rw [deriv_map_add_int_of_add_one hP, map_add_int_of_add_one hP]
  congr 2
  ring

theorem circleGradient_reciprocal_cutoff
    {f : (ℝ × ℝ) → UnitAddCircle} {u χ : (ℝ × ℝ) → ℝ} {x : ℝ × ℝ}
    (hf : ContinuousAt f x) (hu : ContDiffAt ℝ ∞ u x) (hχ : ContDiffAt ℝ ∞ χ x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : ℝ) :
    circleGradient (circleCutoff f χ (shiftedStaircase (reciprocalGridStep N) δ θ)) x =
      staircaseCovector (reciprocalGridStep N) δ (χ x) θ
        (circleRepresentative (f x)) (circleGradient f x) (planarGradient χ x) := by
  let P := shiftedStaircase (reciprocalGridStep N) δ θ
  have hP (r : ℝ) : P (r + 1) = P r + 1 := by
    simpa only [P, reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  let v := cutoffStaircase u χ P
  have hv : ContDiffAt ℝ ∞ v x := hu.add (hχ.mul
    (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh θ).contDiffAt.comp x hu).sub hu))
  have hnew : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] circleCutoff f χ P := by
    filter_upwards [hproj] with y hy
    exact (circleCutoff_eq_lift f χ hP hy).symm
  have hfnew : ContinuousAt (circleCutoff f χ P) x :=
    ((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hv.continuousAt).congr hnew
  have hbase := circleGradient_eq_lift hf hu.continuousAt hproj
  have hmod := circleGradient_eq_lift hfnew hv.continuousAt hnew
  have hxproj : (u x : UnitAddCircle) = f x := hproj.self_of_nhds
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (circleRepresentative (f x)) (u x)).mp
    ((coe_circleRepresentative (f x)).trans hxproj.symm)
  have hr : circleRepresentative (f x) = u x + (m : ℝ) := by simpa only [mul_one] using hm
  rw [hmod, planarGradient_cutoffStaircase (hu.differentiableAt (by simp))
    (hχ.differentiableAt (by simp)) (reciprocalGridStep_pos N) hδ hδh θ, hbase, hr]
  exact (staircaseCovector_reciprocal_add_int N δ (χ x) θ (u x) m
    (planarGradient u x) (planarGradient χ x)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
