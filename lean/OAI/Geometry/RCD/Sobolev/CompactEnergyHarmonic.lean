import OAI.Geometry.RCD.Sobolev.LocalLipschitzGreenTrace
import OAI.Geometry.RCD.Sobolev.GradientQuadraticEnergy
import OAI.Geometry.RCD.Sobolev.EnergyAffineRigidity

namespace OAI

/-! # Sharp compact-test energy variation forces the weak harmonic equation -/

open Set Filter MeasureTheory Metric InnerProductSpace Laplacian
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem compact_energy_variation_harmonic {n : ℕ} {g ψ : Euclidean n → ℝ}
    {S ρ M : ℝ} (hS : 0<S) (hρS : ρ<S)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hψ : InteriorSmoothTest n S ψ) (hs : tsupport ψ⊆ball 0 ρ)
    (hvary : ∀ t : ℝ,
      (∫ z in ball 0 ρ, ‖fderiv ℝ (fun y => g y+t*ψ y) z‖^2)≤
        M+t^2*(∫ z in ball 0 S, ‖fderiv ℝ ψ z‖^2)) :
    (∫ z, g z*(Δ ψ) z)=0 := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψ.2.1 hψ.1 (by simp)
  have hψlocal : ∀ W<S, ∃ B : ℝ≥0, LipschitzOnWith B ψ (closedBall 0 W) :=
    fun _ _ => ⟨L,hL.lipschitzOnWith⟩
  have hgd := local_lipschitz_derivative hρS hg
  have hψd := local_lipschitz_derivative hρS hψlocal
  have hzero (A : Set (Euclidean n)) (hA : tsupport ψ⊆A) :
      (∫ z in A, ‖fderiv ℝ ψ z‖^2)=∫ z, ‖fderiv ℝ ψ z‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [fderiv_of_notMem_tsupport ℝ (fun hx => hz (hA hx)),norm_zero,zero_pow (by decide : 2≠0)]
  have henergy : (∫ z in ball 0 S, ‖fderiv ℝ ψ z‖^2)=
      ∫ z in ball 0 ρ, ‖fderiv ℝ ψ z‖^2 := by
    rw [hzero _ hψ.2.2,hzero _ hs]
  have hcross : (∫ z in ball 0 ρ, inner ℝ (gradient g z) (gradient ψ z))=0 := by
    apply energy_affine_rigidity (E := ∫ z in ball 0 ρ, ‖fderiv ℝ g z‖^2)
      (M := M) (P := ∫ z in ball 0 ρ, ‖fderiv ℝ ψ z‖^2)
    intro t
    have hh := hvary t
    rw [(gradient_quadratic_energy g ψ (ball 0 ρ) hgd.1 hψd.1 hgd.2 hψd.2 t).2.2,
      henergy] at hh
    exact hh
  have hcrossall : (∫ z, inner ℝ (gradient g z) (gradient ψ z))=0 := by
    rw [← hcross]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hz' : z∉tsupport ψ := fun hx => hz (hs hx)
    simp only [gradient,fderiv_of_notMem_tsupport ℝ hz',map_zero,inner_zero_right]
  have hgreen := local_lipschitz_green_trace hS hg hψ
  rw [hcrossall] at hgreen
  linarith only [hgreen]

end RegularPointCoordinates

end

end OAI
