import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusFluxDecay

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma tendsto_linear_mul_exp_neg_gap {gap : ℝ} (hg : 0<gap) :
    Tendsto (fun t : ℝ => t*exp (-gap*(t-1))) atTop (𝓝 0) := by
  have hy : Tendsto (fun t : ℝ => gap*(t-1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-1) tendsto_id).const_mul_atTop hg
  have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hy
  have hh := (he.div_const gap).add (tendsto_exp_neg_gap hg)
  have hfun : (fun t : ℝ => (gap*(t-1))^1*exp (-(gap*(t-1)))/gap+exp (-gap*(t-1)))=
      fun t => t*exp (-gap*(t-1)) := by
    ext t
    rw [pow_one,←neg_mul]
    field_simp
    ring
  dsimp only [Function.comp_def] at hh
  rw [hfun] at hh
  simpa using hh

lemma flatCrossFlux_zero_of_bounds {s : Fin 3→ℝ} {f g : Coord3→ℝ}
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f {x | 0<x 0})
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g {x | 0<x 0})
    (hfp : AngularPeriodic (2*Real.pi) f) (hgp : AngularPeriodic (2*Real.pi) g)
    (hfh : ∀ x,0<x 0 → flatTensorLaplacian s f x=0)
    (hgh : ∀ x,0<x 0 → flatTensorLaplacian s g x=0)
    {A B C D E gap t : ℝ} (hA : 0≤A) (hB : 0≤B) (_ : 0≤C) (hD : 0≤D) (_ : 0≤E)
    (hgap : 0<gap) (ht : 0<t)
    (hb : ∀ x : Coord3,1≤x 0 →
      ‖f x‖≤A*x 0+B ∧ ‖fderiv ℝ f x (flatAxis 0)‖≤C ∧
      ‖g x‖≤D*exp (-gap*(x 0-1)) ∧
      ‖fderiv ℝ g x (flatAxis 0)‖≤E*exp (-gap*(x 0-1))) :
    torusCellIntegral (2*Real.pi) (fun x => flatCrossFlux s f g x 0) t=0 := by
  apply torus_flux_zero_of_tendsto ht (by positivity)
    (flatCrossFlux_smoothOn (axial_halfspace_open 0) hf hg)
    (flatCrossFlux_periodic hfp hgp)
  · intro x hx
    rw [flatCrossFlux_divergence (hf.contDiffAt ((axial_halfspace_open 0).mem_nhds hx))
      (hg.contDiffAt ((axial_halfspace_open 0).mem_nhds hx)),hfh x hx,hgh x hx]
    ring
  · have hlim : Tendsto (fun t : ℝ => (D*C+B*E)*exp (-gap*(t-1))+
        (A*E)*(t*exp (-gap*(t-1)))) atTop (𝓝 0) := by
      simpa using ((tendsto_exp_neg_gap hgap).const_mul (D*C+B*E)).add
        ((tendsto_linear_mul_exp_neg_gap hgap).const_mul (A*E))
    apply torusCellIntegral_tendsto_zero (by positivity) hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht'
    intro y z
    obtain ⟨hfb,hfd,hgb,hgd⟩ := hb ![t,y,z] ht'
    have hAB : 0≤A*t+B := add_nonneg (mul_nonneg hA (le_trans zero_le_one ht')) hB
    calc
      _ ≤ ‖g ![t,y,z]‖*‖fderiv ℝ f ![t,y,z] (flatAxis 0)‖+
          ‖f ![t,y,z]‖*‖fderiv ℝ g ![t,y,z] (flatAxis 0)‖ := by
        simpa only [flatCrossFlux,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,flatModeFlux,
          Matrix.cons_val_zero,norm_mul] using norm_sub_le
          (g ![t,y,z]*fderiv ℝ f ![t,y,z] (flatAxis 0))
          (f ![t,y,z]*fderiv ℝ g ![t,y,z] (flatAxis 0))
      _ ≤ (D*exp (-gap*(t-1)))*C+(A*t+B)*(E*exp (-gap*(t-1))) :=
        add_le_add (mul_le_mul hgb hfd (norm_nonneg _) (mul_nonneg hD (exp_nonneg _)))
          (mul_le_mul hfb hgd (norm_nonneg _) hAB)
      _ = _ := by ring

end ScalarConductivity

end
end

end OAI
