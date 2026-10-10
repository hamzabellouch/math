import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
import OAI.NumberTheory.DirichletL.Descent.CommonMeasure

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapEnergy
open InverseInitialOverlapFourier InverseMoment

theorem polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density g xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density g xj t*φ k t‖^2)≤C*E := by
  obtain ⟨C,hC,hint⟩ := density_moment g J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro κ inst xj φ E hE hφ hbound
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density g xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density g xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density g xj t‖ := by
    rw [show b t=density g xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h]
      using (hint xj).1
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C := by
    simpa only [hbnorm,h]
      using (hint xj).2
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapEnergy

end

end OAI
