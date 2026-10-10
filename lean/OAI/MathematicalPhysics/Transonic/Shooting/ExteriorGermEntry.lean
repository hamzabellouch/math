import OAI.MathematicalPhysics.Transonic.Exterior.BarrierSound
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyEuler
import OAI.MathematicalPhysics.Transonic.Exterior.TaylorEntry

namespace OAI

section
noncomputable section
namespace SepticProfile.SourceFamily
open Set Filter PowerSeries ExteriorPolynomial
open scoped Topology ContDiff

lemma UniformGerm.jet_data (G : UniformGerm) (p : Parameter) :
    coeff 0 (SonicJet.jet (G.realFunction p))=1 ∧
    coeff 1 (SonicJet.jet (G.realFunction p))=slp p ∧
    Formal.residual (sig p) (kap p) (3/5) (SonicJet.jet (G.realFunction p))=0 := by
  have han := G.real_analytic p (x:=0) (by simpa using G.radius_pos)
  refine ⟨?_,?_,?_⟩
  · simp [SonicJet.coeff_jet,UniformGerm.realFunction,G.value]
  · simp only [SonicJet.coeff_jet,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,div_one]
    rw [G.real_derivative p (by simpa using G.radius_pos)]
    simpa using congrArg Complex.re (G.slope p)
  · apply SonicJet.residual_of_smooth_solution (sig p) (kap p) han.contDiffAt
    have hr : ∀ᶠ x:ℝ in 𝓝 0, |x|<G.radius :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using G.radius_pos)
    filter_upwards [hr] with x hx
    exact sub_eq_zero.mpr (G.real_equation p hx)

/-- A finite Taylor sign certificate supplies a genuine positive entry point
for continuation. No unverified Taylor-tail estimate is assumed. -/
lemma UniformGerm.exists_exterior_entry (G : UniformGerm) (p : Parameter)
    {d w : ℝ} (hd : 0<d) (hw : 0<w)
    (hp : 0<coeff 74 (SonicJet.jet (G.realFunction p))) :
    ∃ a : ℝ, 0<a ∧ a<1 ∧ d/256*a<w ∧ d/256*a<G.radius ∧
      (lowerPoly (SonicJet.jet (G.realFunction p)) d).eval a<G.realFunction p (d/256*a) ∧
      G.realFunction p (d/256*a)<Real.sqrt (5/3) := by
  let f := G.realFunction p
  have han : AnalyticAt ℝ f 0 := G.real_analytic p (by simpa using G.radius_pos)
  have hf0 : f 0=1 := by simp [f,UniformGerm.realFunction,G.value]
  have hq : (1:ℝ)<Real.sqrt (5/3) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    have hn := Real.sqrt_nonneg (5/3:ℝ)
    nlinarith
  have ht := enters_above_trunc73 f han.contDiffAt hp
  have hh : 0<d/256 := div_pos hd (by norm_num)
  have hc : Tendsto (fun a:ℝ => d/256*a) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using (show Continuous (fun a:ℝ => d/256*a) by fun_prop).tendsto (0:ℝ)
  have htop : ∀ᶠ x:ℝ in 𝓝 0, f x<Real.sqrt (5/3) :=
    han.continuousAt.eventually (Iio_mem_nhds (by simpa only [hf0] using hq))
  have hall : ∀ᶠ a:ℝ in 𝓝 0, a<1 ∧ d/256*a<w ∧ d/256*a<G.radius ∧
      (0<d/256*a → (PowerSeries.trunc 74 (SonicJet.jet f)).eval (d/256*a)<f (d/256*a)) ∧
      f (d/256*a)<Real.sqrt (5/3) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ)<1),
      hc.eventually (Iio_mem_nhds hw),hc.eventually (Iio_mem_nhds G.radius_pos),
      hc.eventually ht,hc.eventually htop] with a ha hw hr ht htop
    exact ⟨ha,hw,hr,ht,htop⟩
  have hwithin := hall.filter_mono (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hpos : ∀ᶠ a in 𝓝[>] (0:ℝ), 0<a := self_mem_nhdsWithin
  obtain ⟨a,ha,hprop⟩ := (hpos.and hwithin).exists
  refine ⟨a,?_,hprop.1,hprop.2.1,hprop.2.2.1,?_,hprop.2.2.2.2⟩
  · exact ha
  · rw [lowerPoly_eval_scale]
    exact hprop.2.2.2.1 (mul_pos hh ha)

end SepticProfile.SourceFamily

end
end

end OAI
