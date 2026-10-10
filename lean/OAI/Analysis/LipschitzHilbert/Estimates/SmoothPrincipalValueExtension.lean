import OAI.Analysis.LipschitzHilbert.Estimates.SmoothPrincipalValueBound
import OAI.Analysis.LipschitzHilbert.Fourier.SmoothPrincipalValueLinear
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! The density consequence of a uniform short-transform estimate. The
extension agrees almost everywhere with the actual symmetric principal
value on every Schwartz input and has the same operator bound. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem exists_smoothPrincipalValue_extension
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0}
    (hbound : ∀ (f : SchwartzMap DirectionPlane ℂ) (ε : ℝ), 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C*eLpNorm f 2 volume) :
    ∃ T : Lp ℂ 2 (volume : Measure DirectionPlane) →L[ℂ]
        Lp ℂ 2 (volume : Measure DirectionPlane),
      ‖T‖ ≤ C ∧ ∀ f : SchwartzMap DirectionPlane ℂ,
        (T (f.toLp 2 volume) : DirectionPlane → ℂ) =ᵐ[volume]
          smoothPrincipalValue v a f := by
  have hmem (f : SchwartzMap DirectionPlane ℂ) :
      MemLp (smoothPrincipalValue v a f) 2 volume :=
    smoothPrincipalValue_memLp hv f.differentiable ha
      (ENNReal.mul_lt_top (by simp) (f.memLp 2 volume).eLpNorm_lt_top)
      (hbound f)
  let S : SchwartzMap DirectionPlane ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure DirectionPlane) :=
    { toFun := fun f => (hmem f).toLp (smoothPrincipalValue v a f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hmem (f+g)).coeFn_toLp,
          (hmem f).coeFn_toLp, (hmem g).coeFn_toLp,
          Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hx hf hg hadd
        rw [hx,hadd]
        simp only [Pi.add_apply,hf,hg]
        exact congrFun (smoothPrincipalValue_add v f.differentiable g.differentiable ha) x
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
          Lp.coeFn_smul c ((hmem f).toLp _)] with x hx hf hsmul
        simp only [RingHom.id_apply]
        rw [hx,hsmul]
        simp only [Pi.smul_apply,hf]
        exact congrFun (smoothPrincipalValue_smul v c f.differentiable ha) x }
  let inclusion := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure DirectionPlane)).toLinearMap
  have hdense : DenseRange inclusion :=
    SchwartzMap.denseRange_toLpCLM (F := ℂ) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  have hnorm (f : SchwartzMap DirectionPlane ℂ) : ‖S f‖ ≤ (C:ℝ)*‖inclusion f‖ := by
    change ‖(hmem f).toLp (smoothPrincipalValue v a f)‖ ≤ (C:ℝ)*‖f.toLp 2 volume‖
    rw [Lp.norm_toLp,SchwartzMap.norm_toLp]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (f.memLp 2 volume).eLpNorm_ne_top)
      (smoothPrincipalValue_eLpNorm_le hv f.differentiable ha (hbound f))
    simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h
  refine ⟨S.extendOfNorm inclusion,
    LinearMap.opNorm_extendOfNorm_le hdense C.property hnorm, ?_⟩
  intro f
  have heq := LinearMap.extendOfNorm_eq (f := S) (e := inclusion)
    hdense ⟨C,hnorm⟩ f
  change ((S.extendOfNorm inclusion) (inclusion f) : DirectionPlane → ℂ) =ᵐ[volume] _
  rw [heq]
  exact (hmem f).coeFn_toLp

end LipschitzHilbert

end

end OAI
