import OAI.InformationTheory.BooleanNoise.ConcavityAcrossJoin
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def logCorrectedPerspective (f : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  v * f (x / v) - C * v * Real.log v

def logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  f (x / v) - (x / v) * f' (x / v) - C * (Real.log v + 1)

def logCorrectedPerspectiveSecondDeriv (f'' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  ((x / v) ^ 2 * f'' (x / v) - C) / v

private theorem hasDerivAt_const_quotient (x v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => x / w) (-x / v ^ 2) v := by
  convert! (hasDerivAt_const v x).div (hasDerivAt_id v) (ne_of_gt hv) using 1
  simp

theorem hasDerivAt_logCorrectedPerspective (f f' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspective f x C)
      (logCorrectedPerspectiveDeriv f f' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hp := (hasDerivAt_id v).mul (hf.comp v hi)
  have hl := ((hasDerivAt_id v).mul (Real.hasDerivAt_log (ne_of_gt hv))).const_mul C
  convert hp.sub hl using 1
  · ext w
    change w * f (x / w) - C * w * Real.log w =
      w * f (x / w) - C * (w * Real.log w)
    ring
  · dsimp only [logCorrectedPerspectiveDeriv, id_eq, Function.comp_def]
    field_simp [ne_of_gt hv]
    ring

theorem hasDerivAt_logCorrectedPerspectiveDeriv (f f' f'' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v))
    (hf' : HasDerivAt f' (f'' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspectiveDeriv f f' x C)
      (logCorrectedPerspectiveSecondDeriv f'' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hfirst := hf.comp v hi
  have hsecond := hi.mul (hf'.comp v hi)
  have hlog := ((Real.hasDerivAt_log (ne_of_gt hv)).add_const 1).const_mul C
  convert! (hfirst.sub hsecond).sub hlog using 1
  dsimp only [logCorrectedPerspectiveSecondDeriv, Function.comp_apply]
  field_simp [ne_of_gt hv]
  ring

theorem continuousOn_logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Ioi 0)) :
    ContinuousOn (logCorrectedPerspectiveDeriv f f' x C) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => x / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hv => ne_of_gt hv)
  have hmap : MapsTo (fun v : ℝ => x / v) (Ioi 0) (Ioi 0) :=
    fun _ hv => div_pos hx hv
  have hcf : ContinuousOn f (Ioi 0) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Ioi 0) :=
    continuousOn_id.log (fun _ hv => ne_of_gt hv)
  exact ((hcf.comp hi hmap).sub (hi.mul (hf'.comp hi hmap))).sub
    (continuousOn_const.mul (hl.add continuousOn_const))

theorem concaveOn_logCorrectedPerspective (f f' f'' : ℝ → ℝ)
    (x C join : ℝ) (hx : 0 < x) (hjoin : 0 < join)
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hcf' : ContinuousOn f' (Ioi 0))
    (hf' : ∀ y, 0 < y → y ≠ join → HasDerivAt f' (f'' y) y)
    (hcurv : ∀ y, 0 < y → y ≠ join → y ^ 2 * f'' y ≤ C) :
    ConcaveOn ℝ (Ioi 0) (logCorrectedPerspective f x C) := by
  have hneq {v : ℝ} (hv : 0 < v) (hvc : v ≠ x / join) : x / v ≠ join := by
    intro heq
    apply hvc
    apply (eq_div_iff (ne_of_gt hjoin)).mpr
    have h := (div_eq_iff (ne_of_gt hv)).mp heq
    linarith
  apply concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (logCorrectedPerspective f x C) (logCorrectedPerspectiveDeriv f f' x C)
    (logCorrectedPerspectiveSecondDeriv f'' x C) 0 (x / join)
  · intro v hv
    exact hasDerivAt_logCorrectedPerspective f f' x C hv (hf _ (div_pos hx hv))
  · exact continuousOn_logCorrectedPerspectiveDeriv f f' x C hx hf hcf'
  · intro v hv hvc
    exact hasDerivAt_logCorrectedPerspectiveDeriv f f' f'' x C hv
      (hf _ (div_pos hx hv)) (hf' _ (div_pos hx hv) (hneq hv hvc))
  · intro v hv hvc
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hcurv _ (div_pos hx hv) (hneq hv hvc))) hv.le

end LeanBlast.CourtadeKumar

end

end OAI
