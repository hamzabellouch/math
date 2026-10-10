import OAI.Geometry.SurfaceImmersion.Geometry.NormalAxisFactor

namespace OAI

/-! Normal coordinates adapted to the two simple zeros on the axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def axisNormalizedDefect (d : ℝ → Base) (N : Base → Base) (x : Base) : Base :=
  (planeComplexFrame (d (x 1))).inverse (N x)

lemma axisNormalizedDefect_smoothAt {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x) (hx : d (x 1) ≠ 0) :
    ContDiffAt ℝ ∞ (axisNormalizedDefect d N) x := by
  have hF : ContDiff ℝ ∞ (fun y : Base => planeComplexFrame (d (y 1))) :=
    planeComplexFrame_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))
  exact ((planeComplexFrame_invertible hx).contDiffAt_map_inverse.comp x hF.contDiffAt).clm_apply hN

lemma axisNormalizedDefect_fderiv_zero {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x)
    (hx : d (x 1) ≠ 0) (hz : N x = 0) :
    fderiv ℝ (axisNormalizedDefect d N) x =
      ((planeComplexFrame (d (x 1))).inverse).comp (fderiv ℝ N x) := by
  have hF : ContDiff ℝ ∞ (fun y : Base => planeComplexFrame (d (y 1))) :=
    planeComplexFrame_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))
  have hJ := (planeComplexFrame_invertible hx).contDiffAt_map_inverse.comp x hF.contDiffAt
  have hD := (hJ.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hN.differentiableAt (by simp)).hasFDerivAt
  apply ContinuousLinearMap.ext
  intro v
  have he := congrArg (fun L => L v) hD.fderiv
  change (fderiv ℝ (fun y : Base => (planeComplexFrame (d (y 1))).inverse (N y)) x) v = _
  simpa [Function.comp_def,hz] using he

lemma axisNormalizedDefect_axis {d : ℝ → Base} {N : Base → Base} {p q t : ℝ}
    (hd : d t ≠ 0) (he : N (crosscapAxis t) = ((t-p)*(t-q)) • d t) :
    axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  change (planeComplexFrame (d t)).inverse (N (crosscapAxis t)) = _
  rw [he,planeComplexFrame_inverse_axis hd]

lemma injective_second_column_nonzero (L : Base →L[ℝ] Base)
    (hL : Function.Surjective L) (haxis : (L (![0,1] : Base)) 1 = 0) :
    (L (![1,0] : Base)) 1 ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hL (![0,1] : Base)
  have hsplit : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  have he := congrFun hv 1
  rw [hsplit,map_add,map_smul,map_smul] at he
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,haxis,mul_zero,add_zero,
    Matrix.cons_val_one,Matrix.cons_val_zero] at he
  norm_num at he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
