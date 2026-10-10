import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeInverse
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelFamily
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalPath

namespace OAI

/-! # Continuous free pullback on a finite expanding slab -/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeInverse expandingInverseTransfer
  expandingScaleTransfer

private theorem continuous_schrodinger_apply :
    Continuous (fun p : ℝ × FourierL2 => schrodingerFlow p.1 p.2) := by
  apply continuous_operator_apply_of_uniform_bound
    (fun t => (schrodingerFlow t).toContinuousLinearMap.restrictScalars ℝ) 1
  · intro t
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖schrodingerFlow t f‖ ≤ 1 * ‖f‖
    simp only [(schrodingerFlow t).norm_map, one_mul, le_refl]
  · exact continuous_schrodingerFlow

noncomputable def expandingInversePath (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := expandingFreeInverse a b k L t ha hk hL t.2.1 (u t)
  continuous_toFun := by
    simp_rw [expandingFreeInverse_apply]
    have hr := (expandingPhysicalPath a k L T ha hk hL u).continuous
    have hx : Continuous (fun t : Icc (0 : ℝ) T =>
        expandingScaleTransfer a k 1 L ha hk le_rfl hL
          (expandingPhysicalPath a k L T ha hk hL u t)) :=
      (expandingScaleTransfer a k 1 L ha hk le_rfl hL).continuous.comp hr
    have ht : Continuous (fun t : Icc (0 : ℝ) T => -expandingFreeTime L t) := by
      unfold expandingFreeTime
      fun_prop
    have hA : Continuous (fun t : Icc (0 : ℝ) T => (expandingFreeAmplitude a b t)⁻¹) := by
      apply Continuous.inv₀
      · unfold expandingFreeAmplitude
        fun_prop
      · intro t
        exact Complex.exp_ne_zero _
    exact hA.smul (continuous_schrodinger_apply.comp (ht.prodMk hx))

@[simp] theorem expandingInversePath_apply (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    expandingInversePath a b k L T ha hk hL u t =
      expandingFreeInverse a b k L t ha hk hL t.2.1 (u t) := rfl

theorem expandingInversePath_return (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    expandingFreeStep a b k L t ha hk hL t.2.1
      (expandingInversePath a b k L T ha hk hL u t) = u t := by
  rw [expandingInversePath_apply, expandingFreeInverse_right]

theorem expandingFreeInverse_after_kernel (a b k L t τ : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hτ : τ ∈ Icc 0 t) (f : FourierL2) :
    expandingFreeInverse a b k L t ha hk hL (hτ.1.trans hτ.2)
      (expandingFreeStep a b k (expandingRadius L τ) (t - τ) ha hk
        (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) f) =
      expandingFreeInverse a b k L τ ha hk hL hτ.1 f := by
  let v := expandingFreeInverse a b k L τ ha hk hL hτ.1 f
  have hv : expandingFreeStep a b k L τ ha hk hL hτ.1 v = f :=
    expandingFreeInverse_right a b k L τ ha hk hL hτ.1 f
  have hadd := congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A v)
    (expandingFreeStep_add a b k L τ (t - τ) ha hk hL hτ.1 (sub_nonneg.mpr hτ.2))
  simp only [ContinuousLinearMap.comp_apply, add_sub_cancel, hv] at hadd
  rw [hadd, expandingFreeInverse_left]

end DefocusingNLS

end OAI
