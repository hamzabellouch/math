import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! On a fixed positive-height compact set, the hyperbolic L2 density
is bounded by a constant times the Euclidean L2 density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCompact_inverseCube_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ y∈K, (y.2^3)⁻¹≤C := by
  have hv : ContinuousOn (fun y : ℂ × ℝ => (y.2^3)⁻¹) K :=
    ((continuous_snd.pow 3).continuousOn).inv₀ (fun y hy => pow_ne_zero 3 (hpos hy).ne')
  obtain ⟨C₀,hC₀⟩ := hK.exists_bound_of_continuousOn hv
  refine ⟨max C₀ 0,le_max_right _ _,fun y hy => ?_⟩
  exact (le_abs_self _).trans ((hC₀ y hy).trans (le_max_left _ _))

private lemma normSquare_integrable {f : ℂ × ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun y => ‖f y‖^2) (volume : Measure (ℂ × ℝ)) := by
  have hcont : Continuous (fun y => ‖f y‖^2) := hf.norm.pow 2
  have hs : HasCompactSupport (fun y => ‖f y‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hs

private lemma normSquare_divCube_integrableOn {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) {f : ℂ × ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn (fun y => ‖f y‖^2/y.2^3) K := by
  have hn : ContinuousOn (fun y => ‖f y‖^2) K := (hf.norm.pow 2).continuousOn
  have hd : ContinuousOn (fun y : ℂ × ℝ => y.2^3) K := (continuous_snd.pow 3).continuousOn
  have hdiv : ContinuousOn (fun y => ‖f y‖^2/y.2^3) K :=
    hn.div hd (fun y hy => pow_ne_zero 3 (hpos hy).ne')
  exact hdiv.integrableOn_compact hK

theorem cubicThetaCompactDensity_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ), Continuous f → HasCompactSupport f → tsupport f⊆K →
      (∫ y, ‖f y‖^2/y.2^3)≤C*(∫ y, ‖f y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_inverseCube_bound hK hpos
  refine ⟨C,hC,fun f hf hc hs => ?_⟩
  have hnum := normSquare_integrable hf hc
  have hdiv := normSquare_divCube_integrableOn hK hpos hf
  have hmono : (∫ y in K, ‖f y‖^2/y.2^3)≤C*(∫ y in K, ‖f y‖^2) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hdiv (hnum.integrableOn.const_mul C) hK.measurableSet
    intro y hy
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_right (hbound y hy) (sq_nonneg ‖f y‖)
  have hz : ∀ y, y∉K → f y=0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht))
  have h₁ : (∫ y in K, ‖f y‖^2/y.2^3)=∫ y, ‖f y‖^2/y.2^3 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hz y hy,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]
  have h₂ : (∫ y in K, ‖f y‖^2)=∫ y, ‖f y‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hz y hy,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  rwa [h₁,h₂] at hmono

end CubicFirstMoment

end

end OAI
