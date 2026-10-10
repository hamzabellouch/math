import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldRadial
import OAI.Probability.InvariantIsing.Magnetic.MagneticLevelDerivative
import OAI.Probability.InvariantIsing.Fields.FieldHeightRadialHessian

namespace OAI

/-! The radial row sign of the constrained height Hessian, obtained from
the actual fixed-magnetization radial comparison. -/

noncomputable section
open Set Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma magneticFieldLevel_congr {h k : FieldStep} (he : h = k) (s : ℝ)
    (i : Fin (h.depth + 1)) (j : Fin (k.depth + 1)) (hij : i.val = j.val) :
    magneticFieldLevel h s i = magneticFieldLevel k s j := by
  cases he
  have hi : i = j := Fin.ext hij
  subst j
  rfl

theorem magneticHeight_radial_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    ∑ j, magneticHeightSchur h F s r i j * r j ≤ 0 := by
  let k := fieldStepOfStrictHeights h r hrs
  let c : ℝ → ℝ≥0 := fun t => ⟨Real.sqrt (Real.exp t), Real.sqrt_nonneg _⟩
  let g := fun t : ℝ => magneticFieldLevel (fieldScaleCovariance k (c t)) s i
  have hcpos (t : ℝ) : 0 < c t := Real.sqrt_pos.2 (Real.exp_pos t)
  have hg : Monotone g := by
    intro a b hab
    have hc : c a ≤ c b := Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hab)
    exact magneticFieldLevel_radial k (hcpos a) hc i hs
  have he : g = fun t : ℝ => magneticHeightLevel h s (r + (Real.exp t - 1) • r) i := by
    funext t
    have hvec : r + (Real.exp t - 1) • r = Real.exp t • r := by module
    have htR : r + (Real.exp t - 1) • r ∈ fieldStrictHeightCone h.depth := by
      rw [hvec]
      exact fieldStrictHeightCone_smul hrs (Real.exp_pos t)
    have hsq : (c t : ℝ) ^ 2 = Real.exp t := Real.sq_sqrt (Real.exp_pos t).le
    have heq : r + (Real.exp t - 1) • r = fun j => (c t : ℝ) ^ 2 * r j := by
      rw [hvec]
      funext j
      change Real.exp t * r j = (c t : ℝ) ^ 2 * r j
      rw [hsq]
    have hk : fieldStepOfStrictHeights h (r + (Real.exp t - 1) • r) htR =
        fieldScaleCovariance k (c t) := by
      unfold fieldStepOfStrictHeights fieldWithHeights fieldScaleCovariance k
      congr 1
    rw [magneticHeightLevel, dite_eq_left htR]
    exact (magneticFieldLevel_congr hk s i i rfl).symm
  have hd := hasDerivAt_magneticHeightLevel_line h F hI hU hs r r hr hrs i
  have hq : HasDerivAt (fun t : ℝ => Real.exp t - 1) 1 0 := by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp 0).sub_const 1
  have hd' : HasDerivAt (fun t : ℝ => magneticHeightLevel h s (r + t • r) i)
      ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
        (∑ j, magneticHeightSchur h F s r i j * r j)) (Real.exp 0 - 1) := by
    simpa only [Real.exp_zero, sub_self] using hd
  have ht := hd'.comp 0 hq
  have hp : 0 ≤ (-2 / (h.cut i.succ - h.cut i.castSucc)) *
      (∑ j, magneticHeightSchur h F s r i j * r j) := by
    have hder : HasDerivAt g
        ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
          (∑ j, magneticHeightSchur h F s r i j * r j)) 0 := by
      simpa only [he, Function.comp_def, mul_one] using ht
    exact hder.nonneg_of_monotone hg
  have hw : 0 < h.cut i.succ - h.cut i.castSucc :=
    sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)
  have hn : -2 / (h.cut i.succ - h.cut i.castSucc) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hw
  nlinarith

end InvariantIsing

end

end OAI
