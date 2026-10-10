import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticLocalWeak

namespace OAI

/-! The coordinate Green identity applied to a genuine smooth section
with its actual differential equation. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_continuousOn (F : CubicThetaSection) :
    ContinuousOn (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2} := by
  apply F.val.continuous.comp_continuousOn
  apply cubicThetaPointInclusion.symm.continuousOn.mono
  intro p hp
  rwa [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target]

lemma cubicThetaSmooth_axis_regular (G : cubicThetaSmoothTests) (k : CubicThetaAxis)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 2 (fun t => cubicThetaSectionFunction G
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) := by
  have hc := G.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hl : ContDiff ℝ ∞ (cubicThetaCoordinateLine k p.1.re p.1.im p.2) := by
    cases k with
    | x => exact (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
    | y => exact (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
    | height => exact contDiff_const.prodMk contDiff_id
  have he : cubicThetaCoordinateLine k p.1.re p.1.im p.2
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)=p :=
    (cubicThetaCoordinateLine_center _ _ _ _).trans (cubicThetaCartesianPoint_self p)
  have hcp : ContDiffAt ℝ ∞ (cubicThetaSectionFunction G)
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) := by
    rw [he]
    exact hc
  exact (hcp.comp _ hl.contDiffAt).of_le (by norm_num)

theorem cubicThetaSmooth_local_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (lam : ℂ) (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (φ : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ
      (cubicThetaSectionFunction G) p)+
      lam*(∫ p, star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)=
    ∫ p, star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
  have hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {p : ℂ × ℝ | 0<p.2} :=
    G.property.1.of_le (show (1:ℕ∞ω)≤∞ by norm_num)
  have hg := cubicThetaLocalGreen_identity φ (cubicThetaSectionFunction G) hφ hc hp hG
    (fun k => cubicThetaAxisSecond_continuousOn k _
      (isOpen_lt continuous_const continuous_snd) (G.property.1.of_le (by norm_num)))
    (fun k p hp => cubicThetaSmooth_axis_regular G k hp)
  have hd : ContinuousOn (fun p : ℂ × ℝ => (p.2:ℂ)^3) {p : ℂ × ℝ | 0<p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3
  have hn : ∀ p∈{p : ℂ × ℝ | 0<p.2}, (p.2:ℂ)^3≠0 :=
    fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')
  have hM : Integrable (fun p => star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable
      hφ.continuous hc hp (hG.continuousOn.div hd hn)
  have hJ : Integrable (fun p => star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable
      hφ.continuous hc hp ((cubicThetaSectionFunction_continuousOn J).div hd hn)
  have he (p : ℂ × ℝ) :
      star (φ p)*cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p/(p.2:ℂ)^3=
        lam*(star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)-
          star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
    by_cases hpos : 0<p.2
    · rw [hEq p hpos]
      ring
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hpos (hp h))
      simp only [hz,star_zero,zero_mul,zero_div,mul_zero,sub_self]
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian
      (cubicThetaSectionFunction G) p/(p.2:ℂ)^3)=
      lam*(∫ p, star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)-
        ∫ p, star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
    simp_rw [he]
    rw [integral_sub (hM.const_mul _) hJ,integral_const_mul]
  rw [hi] at hg
  linear_combination hg

end CubicFirstMoment

end

end OAI
