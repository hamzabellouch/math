import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatSmallHeight

namespace OAI

/-! The small-height Gamma limit applies to the actual Fourier heat
kernel, and proves that it cannot vanish identically in height. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaNormalizedHeat_scale (s : ℂ) (A : ℝ) {v : ℝ} (hv : 0<v) :
    (∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v t)=
      ((v^2:ℝ):ℂ)^(s-1)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
  let a : ℝ := v^2
  have ha : 0<a := sq_pos_of_pos hv
  have hac : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hi := integral_comp_mul_left_Ioi (cubicThetaNormalizedHeat s A v) 0 ha
  rw [mul_zero,Complex.real_smul,Complex.ofReal_inv] at hi
  have he : (∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v (a*t))=
      (a:ℂ)^(s-2)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    dsimp only [cubicThetaNormalizedHeat,cubicThetaDualHeat]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le ht.le]
    have hfrac : -A*v^2/(a*t)=-A/t := by dsimp [a]; field_simp
    rw [hfrac]
    change (Real.exp (-(a*t)):ℂ)*((a:ℂ)^(s-2)*(t:ℂ)^(s-2))*(Real.exp (-A/t):ℂ)=_
    rw [show -v^2*t-A/t=-(a*t)+(-A/t) by dsimp [a]; ring,Real.exp_add,
      Complex.ofReal_mul]
    ring
  have hp : (a:ℂ)*(a:ℂ)^(s-2)=(a:ℂ)^(s-1) := by
    calc
      _ = (a:ℂ)^(1:ℂ)*(a:ℂ)^(s-2) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hac]; congr 1; ring
  calc
    _ = (a:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v (a*t)) := by
      rw [hi]
      field_simp
    _ = (a:ℂ)^ (s-1)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
      rw [he,← mul_assoc,hp]

theorem cubicThetaDualHeat_eventually_nonzero {s : ℂ} (hs : 1<s.re)
    {A : ℝ} (hA : 0≤A) :
    ∀ᶠ v in 𝓝[>] (0:ℝ), (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)≠0 := by
  have hG : Complex.Gamma (s-1)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hn := (cubicThetaNormalizedHeat_gamma_limit hs hA).eventually
    (eventually_ne_nhds hG)
  filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with v hv hpos
  intro hz
  rw [cubicThetaNormalizedHeat_scale s A hpos,hz,mul_zero] at hv
  exact hv rfl

end CubicFirstMoment

end

end OAI
