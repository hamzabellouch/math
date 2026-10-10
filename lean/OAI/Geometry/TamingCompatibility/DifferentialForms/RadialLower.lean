import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialPerturbation

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma log_variable_ddc_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    (hinner : ∀ u v, ⟪K u,K v⟫ = ⟪u,v⟫)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    2*s^2*‖v‖^2/(s^2+‖z‖^2)^2 - (16*L*M/(s+‖z‖))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (logPotential s)) z ![v,J z v] := by
  have hp := log_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  have hb := log_ddc_lower K hKK hinner hs z v
  rw [Real.norm_eq_abs,abs_le] at hp
  linarith [hp.1]

lemma sqrt_variable_ddc_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    (hinner : ∀ u v, ⟪K u,K v⟫ = ⟪u,v⟫)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖v‖^2/(s+‖z‖) - (10*L*M)*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (sqrtPotential s)) z ![v,J z v] := by
  have hp := sqrt_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  have hb := sqrt_ddc_lower K hKK hinner hs z v
  have hA := radial_sq_pos hs z
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have hqa : Real.sqrt (s^2+‖z‖^2) ≤ s+‖z‖ := by
    nlinarith [mul_nonneg (le_of_lt hs) (norm_nonneg z),norm_nonneg z]
  have hden : ‖v‖^2/(s+‖z‖) ≤ ‖v‖^2/Real.sqrt (s^2+‖z‖^2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hq hqa
  rw [Real.norm_eq_abs,abs_le] at hp
  linarith [hp.1]

omit [InnerProductSpace ℝ E] in

lemma log_trace_inner_ball {s : ℝ} (hs : 0 < s) (z v : E) (hz : ‖z‖ ≤ s) :
    ‖v‖^2/(2*s^2) ≤ 2*s^2*‖v‖^2/(s^2+‖z‖^2)^2 := by
  have hA := radial_sq_pos hs z
  apply (div_le_div_iff₀ (by positivity : 0 < 2*s^2) (pow_pos hA 2)).mpr
  have hz2 : ‖z‖^2 ≤ s^2 := by nlinarith [norm_nonneg z]
  have hA2 : (s^2+‖z‖^2)^2 ≤ 4*s^4 := by
    nlinarith [sq_nonneg (s^2-‖z‖^2)]
  nlinarith [mul_le_mul_of_nonneg_right hA2 (sq_nonneg ‖v‖)]
end TamingCompatibility.RadialPotential

end
end

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def annularParameters : Set (ℝ × E) :=
  Icc (0:ℝ) 1 ×ˢ (Metric.closedBall (0:E) 2 \ Metric.ball 0 (1/2))

omit [InnerProductSpace ℝ E] in
lemma annularParameters_positive {p : ℝ × E} (hp : p ∈ annularParameters (E := E)) :
    0 < p.1^2 + ‖p.2‖^2 := by
  have hz := hp.2.2
  simp only [Metric.mem_ball,dist_zero_right,not_lt] at hz
  nlinarith [sq_nonneg p.1]

lemma log_joint_smooth_at {p : ℝ × E} (hp : 0 < p.1^2+‖p.2‖^2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => logPotential q.1 q.2) p := by
  have h : ContDiffAt ℝ ∞ (fun q : ℝ × E => q.1^2+‖q.2‖^2) p :=
    (contDiff_fst.pow 2).contDiffAt.add ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt
  exact contDiffAt_const.mul (h.log (ne_of_gt hp))

lemma sqrt_joint_smooth_at {p : ℝ × E} (hp : 0 < p.1^2+‖p.2‖^2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => sqrtPotential q.1 q.2) p := by
  have h : ContDiffAt ℝ ∞ (fun q : ℝ × E => q.1^2+‖q.2‖^2) p :=
    (contDiff_fst.pow 2).contDiffAt.add ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt
  exact h.sqrt (ne_of_gt hp)

omit [InnerProductSpace ℝ E] in
lemma annularParameters_compact [ProperSpace E] : IsCompact (annularParameters (E := E)) :=
  isCompact_Icc.prod ((isCompact_closedBall (0:E) 2).diff Metric.isOpen_ball)

lemma log_annular_derivatives_bounded [ProperSpace E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ annularParameters (E := E),
      ‖iteratedFDeriv ℝ n (fun q : ℝ × E => logPotential q.1 q.2) p‖ ≤ C := by
  have hc : ContinuousOn
      (iteratedFDeriv ℝ n (fun q : ℝ × E => logPotential q.1 q.2)) annularParameters := by
    intro p hp
    exact ((log_joint_smooth_at (annularParameters_positive hp)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨C,hC⟩ := (annularParameters_compact (E := E)).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p hp
  exact (hC p hp).trans (le_max_left _ _)

lemma sqrt_annular_derivatives_bounded [ProperSpace E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ annularParameters (E := E),
      ‖iteratedFDeriv ℝ n (fun q : ℝ × E => sqrtPotential q.1 q.2) p‖ ≤ C := by
  have hc : ContinuousOn
      (iteratedFDeriv ℝ n (fun q : ℝ × E => sqrtPotential q.1 q.2)) annularParameters := by
    intro p hp
    exact ((sqrt_joint_smooth_at (annularParameters_positive hp)).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨C,hC⟩ := (annularParameters_compact (E := E)).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p hp
  exact (hC p hp).trans (le_max_left _ _)
lemma logPotential_radial_scale {r s : ℝ} (hr : 0 < r) (z : E)
    (hA : 0 < s^2+‖z‖^2) :
    logPotential (r*s) (r • z) = Real.log r + logPotential s z := by
  simp only [logPotential,norm_smul,Real.norm_of_nonneg (le_of_lt hr)]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring]
  rw [Real.log_mul (ne_of_gt (pow_pos hr 2)) (ne_of_gt hA),Real.log_pow]
  ring

lemma sqrtPotential_radial_scale {r s : ℝ} (hr : 0 < r) (z : E) :
    sqrtPotential (r*s) (r • z) = r * sqrtPotential s z := by
  simp only [sqrtPotential,norm_smul,Real.norm_of_nonneg (le_of_lt hr)]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring]
  rw [Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs,abs_of_pos hr]
end TamingCompatibility.RadialPotential

end
end

end
end
end

end OAI
