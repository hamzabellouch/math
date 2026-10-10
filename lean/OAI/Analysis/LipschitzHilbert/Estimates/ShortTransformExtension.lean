import OAI.Analysis.LipschitzHilbert.Estimates.SmoothPrincipalValueExtension

namespace OAI

/-! The dense Schwartz-space realization of a uniformly bounded hard
truncation extends to a bounded linear operator on L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem exists_shortTransform_extension (v : DirectionPlane → DirectionPlane)
    (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (C : ℝ≥0)
    (hbound : ∀ f : SchwartzMap DirectionPlane ℂ,
      eLpNorm (shortTransform v epsilon R f) 2 volume≤C*eLpNorm f 2 volume) :
    ∃ T : Lp ℂ 2 (volume : Measure DirectionPlane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap DirectionPlane ℂ,
        (T (f.toLp 2 volume) : DirectionPlane → ℂ)=ᵐ[volume] shortTransform v epsilon R f := by
  have hmem (f : SchwartzMap DirectionPlane ℂ) : MemLp (shortTransform v epsilon R f) 2 volume :=
    (hbound f).trans_lt (ENNReal.mul_lt_top (by simp) (f.memLp 2 volume).eLpNorm_lt_top)
  let S : SchwartzMap DirectionPlane ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure DirectionPlane) :=
    { toFun := fun f => (hmem f).toLp (shortTransform v epsilon R f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hmem (f+g)).coeFn_toLp,(hmem f).coeFn_toLp,(hmem g).coeFn_toLp,
          Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hx hf hg hadd
        rw [hx,hadd]
        simp only [Pi.add_apply,hf,hg]
        exact shortTransform_add v f.continuous g.continuous he heR x
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hmem (c • f)).coeFn_toLp,(hmem f).coeFn_toLp,
          Lp.coeFn_smul c ((hmem f).toLp _)] with x hx hf hsmul
        simp only [RingHom.id_apply]
        rw [hx,hsmul]
        simp only [Pi.smul_apply,hf]
        exact shortTransform_smul v c f epsilon R x }
  let inclusion := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure DirectionPlane)).toLinearMap
  have hdense : DenseRange inclusion :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠∞)
  have hnorm (f : SchwartzMap DirectionPlane ℂ) : ‖S f‖≤(C:ℝ)*‖inclusion f‖ := by
    change ‖(hmem f).toLp (shortTransform v epsilon R f)‖≤(C:ℝ)*‖f.toLp 2 volume‖
    rw [Lp.norm_toLp,SchwartzMap.norm_toLp]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (f.memLp 2 volume).eLpNorm_ne_top) (hbound f)
    simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h
  refine ⟨S.extendOfNorm inclusion,LinearMap.opNorm_extendOfNorm_le hdense C.property hnorm,?_⟩
  intro f
  have heq := LinearMap.extendOfNorm_eq (f:=S) (e:=inclusion) hdense ⟨C,hnorm⟩ f
  change ((S.extendOfNorm inclusion) (inclusion f) : DirectionPlane → ℂ)=ᵐ[volume] _
  rw [heq]
  exact (hmem f).coeFn_toLp

end LipschitzHilbert

end

end OAI
