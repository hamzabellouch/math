import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyGerm

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Filter Metric
open scoped Topology ContDiff

def UniformGerm.realFunction (G : UniformGerm) (a : Parameter) (x : ℝ) : ℝ := (G.U a (x:ℂ)).re

def UniformGerm.eulerFunction (G : UniformGerm) (a : Parameter) : ℝ → ℝ :=
  G.realFunction a ∘ SourceEuler.changeOfVariable (1/500)

lemma UniformGerm.real_analytic (G : UniformGerm) (a : Parameter) {x : ℝ}
    (hx : |x|<G.radius) : AnalyticAt ℝ (G.realFunction a) x := by
  apply (G.analytic a (x:ℂ) _).re_ofReal
  simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx

lemma UniformGerm.real_derivative (G : UniformGerm) (a : Parameter) {x : ℝ}
    (hx : |x|<G.radius) : deriv (G.realFunction a) x=(deriv (G.U a) (x:ℂ)).re := by
  apply ((G.analytic a (x:ℂ) _).differentiableAt.hasDerivAt.real_of_complex).deriv
  simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx

lemma UniformGerm.real_equation (G : UniformGerm) (a : Parameter) {x : ℝ}
    (hx : |x|<G.radius) :
    (1+x)*(1-sig a*(1+x)^2)*(1-(G.realFunction a x)^2)*deriv (G.realFunction a) x =
      (1-(3/5:ℝ)*(G.realFunction a x)^2)*
        (kap a*(1+x)*(1-(G.realFunction a x)^2)+3*((1+x)-G.realFunction a x)) := by
  have he := G.equation a (x:ℂ) (by simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx)
  have huv : G.U a (x:ℂ)=(G.realFunction a x:ℂ) := by
    apply Complex.ext <;> simp [UniformGerm.realFunction,G.real]
  have he' := congrArg Complex.re he
  rw [huv] at he'
  unfold Remainder.res at he'
  change ((1+(x:ℂ))*(1-(sig a:ℂ)*(1+(x:ℂ))^2)*(1-(G.realFunction a x:ℂ)^2)*
    deriv (G.U a) (x:ℂ)-(1-(cst a:ℂ)*(G.realFunction a x:ℂ)^2)*
      ((kap a:ℂ)*(1+(x:ℂ))*(1-(G.realFunction a x:ℂ)^2)+3*((1+(x:ℂ))-(G.realFunction a x:ℂ)))).re=0 at he'
  have hc : cst a=(3/5:ℝ) := rfl
  rw [hc] at he'
  rw [G.real_derivative a hx]
  simp only [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_mul,
    ← Complex.ofReal_sub,← Complex.ofReal_pow,← Complex.ofReal_ofNat] at he'
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at he'
  exact sub_eq_zero.mp he'

lemma UniformGerm.euler_data (G : UniformGerm) (a : Parameter) :
    AnalyticAt ℝ (G.eulerFunction a) 0 ∧ G.eulerFunction a 0=1 ∧
      deriv (G.eulerFunction a) 0= -slp a/500 ∧
      ∀ᶠ t in 𝓝 (0:ℝ), SourceEuler.residual (sig a) (kap a) (3/5) (1/500) t
        (G.eulerFunction a t) (deriv (G.eulerFunction a) t)=0 := by
  have hva : AnalyticAt ℝ (G.realFunction a) 0 := G.real_analytic a (by simpa using G.radius_pos)
  have hv0 : G.realFunction a 0=1 := by simp [UniformGerm.realFunction,G.value]
  have hvd : deriv (G.realFunction a) 0=slp a := by
    rw [G.real_derivative a (by simpa using G.radius_pos)]
    simpa using congrArg Complex.re (G.slope a)
  have hp0 : SourceEuler.changeOfVariable (1/500) 0=0 := by simp [SourceEuler.changeOfVariable]
  have hpa : AnalyticAt ℝ (SourceEuler.changeOfVariable (1/500)) 0 := by
    unfold SourceEuler.changeOfVariable
    fun_prop (disch := norm_num)
  have huder {t:ℝ} (ht:1-t≠0)
      (hvt : DifferentiableAt ℝ (G.realFunction a) (SourceEuler.changeOfVariable (1/500) t)) :
      deriv (G.eulerFunction a) t=deriv (G.realFunction a) (SourceEuler.changeOfVariable (1/500) t)*
        (-(1/500)/(1-t)^2) :=
    ((hvt.hasDerivAt).comp t (SourceEuler.derivative_changeOfVariable (1/500) t ht)).deriv
  refine ⟨(hp0 ▸ hva).comp hpa,by simpa only [UniformGerm.eulerFunction,Function.comp_apply,hp0] using hv0,?_,?_⟩
  · rw [huder (by norm_num) (by simpa only [hp0] using hva.differentiableAt),hp0,hvd]
    ring
  · have hpt : Tendsto (SourceEuler.changeOfVariable (1/500)) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hp0] using hpa.continuousAt
    have hrad : ∀ᶠ x:ℝ in 𝓝 0, |x|<G.radius := by
      exact (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using G.radius_pos)
    have htn : ∀ᶠ t:ℝ in 𝓝 0, 1-t≠0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
    filter_upwards [hpt.eventually hrad,htn] with t ht htn
    rw [huder htn (G.real_analytic a ht).differentiableAt]
    exact SourceEuler.transform_equation _ _ _ _ _ _ _ htn (G.real_equation a ht)

end SepticProfile.SourceFamily

end
end

end OAI
