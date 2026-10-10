import Mathlib.Analysis.MellinInversion
import OAI.NumberTheory.Jacobsthal.Estimates.RieszTermCalculus
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.QuadraticSieveMellin
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinStrip

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open MeasureTheory Filter
open scoped Topology SchwartzMap

variable (ρ : 𝓢(ℝ, ℂ))
local notation "smoothKernel" => mellin (ρ : ℝ → ℂ)

noncomputable def smoothDirichletTerm (f : ℕ → ℂ) (sigma X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n *
    smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)

lemma norm_smoothDirichletTerm (f : ℕ → ℂ) (sigma : ℝ) {X : ℝ} (hX : 0 < X)
    (n : ℕ) (t : ℝ) :
    ‖smoothDirichletTerm ρ f sigma X n t‖ =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma * ‖smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have ht : ‖LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n‖ = ‖LSeries.term f (sigma:ℂ) n‖ := by
    simp only [LSeries.norm_term_eq,hre,Complex.ofReal_re]
  unfold smoothDirichletTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hX,hre]
  ring

lemma smoothDirichletTerm_eq_scaled (f : ℕ → ℂ) (hf0 : f 0 = 0) (sigma : ℝ)
    {X : ℝ} (hX : 0 < X) (n : ℕ) (t : ℝ) :
    smoothDirichletTerm ρ f sigma X n t = f n *
      (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  by_cases hn : n=0
  · simp [smoothDirichletTerm,hn,hf0]
  · unfold smoothDirichletTerm
    rw [LSeries.term_of_ne_zero hn,riesz_scale_cpow (by exact_mod_cast Nat.pos_of_ne_zero hn) hX]
    simp only [div_eq_mul_inv]
    push_cast
    ring

lemma continuous_smoothDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 0 < sigma) (hX : 0 < X) (n : ℕ) :
    Continuous (smoothDirichletTerm ρ f sigma X n) := by
  by_cases hn : n=0
  · subst n
    unfold smoothDirichletTerm
    simp only [LSeries.term_zero,zero_mul]
    exact continuous_const
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    have hnp : Continuous (fun t:ℝ => (n:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      simp_rw [Complex.cpow_def_of_ne_zero hnC]
      fun_prop
    have hXp : Continuous (fun t:ℝ => (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      simp_rw [Complex.cpow_def_of_ne_zero hXC]
      fun_prop
    have hterm : Continuous (fun t:ℝ => LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnp (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    exact (hterm.mul (schwartz_mellin_vertical_continuous ρ sigma hs)).mul hXp

lemma integrable_smoothDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 0 < sigma) (hX : 0 < X) (n : ℕ) :
    Integrable (smoothDirichletTerm ρ f sigma X n) := by
  have hg := (schwartz_mellin_vertical_integrable ρ sigma hs).norm.const_mul
    (‖LSeries.term f (sigma:ℂ) n‖ * X^sigma)
  apply hg.mono' (continuous_smoothDirichletTerm ρ f hs hX n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (norm_smoothDirichletTerm ρ f sigma hX n t).le)

lemma integral_norm_smoothDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hX : 0 < X) (n : ℕ) :
    (∫ t:ℝ, ‖smoothDirichletTerm ρ f sigma X n t‖) =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma *
        ∫ t:ℝ, ‖smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp_rw [norm_smoothDirichletTerm ρ f sigma hX n]
  exact integral_const_mul _ _

end Ostmann.Dirichlet

end OAI
