import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingSmooth

namespace OAI

/-! Smoothness makes both cutoff derivatives vanish at the two endpoints,
so the forcing can be reconstructed from the open annulus. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_derivatives_zero_closed {v : ℝ} (hv : v≤1 ∨ 2≤v) :
    deriv cubicThetaCuspCutoff v=0 ∧ deriv (deriv cubicThetaCuspCutoff) v=0 := by
  have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  rcases hv with hv | hv
  · have h₁ : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Iio (1:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inl ht)).1
    have h₂ : EqOn (deriv (deriv cubicThetaCuspCutoff)) (fun _ => 0) (Iio (1:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inl ht)).2
    have hm : v∈closure (Iio (1:ℝ)) := by simpa only [closure_Iio,mem_Iic] using hv
    exact ⟨h₁.closure hd.continuous continuous_const hm,
      h₂.closure hdd.continuous continuous_const hm⟩
  · have h₁ : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Ioi (2:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inr ht)).1
    have h₂ : EqOn (deriv (deriv cubicThetaCuspCutoff)) (fun _ => 0) (Ioi (2:ℝ)) :=
      fun t ht => (cubicThetaCuspCutoff_derivatives_zero (Or.inr ht)).2
    have hm : v∈closure (Ioi (2:ℝ)) := by simpa only [closure_Ioi,mem_Ici] using hv
    exact ⟨h₁.closure hd.continuous continuous_const hm,
      h₂.closure hdd.continuous continuous_const hm⟩

lemma cubicThetaIncomingForcing_zero_closed (s : ℂ) {v : ℝ} (hv : v≤1 ∨ 2≤v) :
    cubicThetaIncomingForcing s v=0 := by
  obtain ⟨h₁,h₂⟩ := cubicThetaCuspCutoff_derivatives_zero_closed hv
  simp [cubicThetaIncomingForcing,h₁,h₂]

end CubicFirstMoment

end

end OAI
