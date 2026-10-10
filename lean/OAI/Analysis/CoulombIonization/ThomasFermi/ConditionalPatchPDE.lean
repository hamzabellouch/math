import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchRandomVariables
import OAI.Analysis.CoulombIonization.FieldAnalysis.PatchWeakPoisson

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_weak_pde {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (hs : tsupport g ⊆ ball 0 R) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    let W := fun x => normalizedCoreField Z lam (coreSlice ψ t u) (y+x)-tfBallPotential R f x
    (∫ x, W x*Δ g x ∂ballMeasure R) = 4*Real.pi*
      (∫ x, (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x ∂ballMeasure R) := by
  let Φ := conditionalPatchField ψ t Z lam y R u
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  let V := fun x => normalizedCoreField Z lam (coreSlice ψ t u) (y+x)
  let W := fun x => V x-tfBallPotential R f x
  change (∫ x, W x*Δ g x ∂ballMeasure R) = _
  have hp : MemLp V (5/2) (ballMeasure R) :=
    normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
  have he : Φ =ᵐ[ballMeasure R] V := conditionalPatchField_ae ψ t Z lam y R u hp
  have h0 : (0 : Space) ∉ ball y R := by
    intro hn
    have hh := hnuc 0 (ball_subset_closedBall hn)
    simp only [norm_zero] at hh
    linarith
  have hA : ∀ a ∈ A, a ∉ ball y R := by
    intro a ha hn
    have hh := hsep a ha a (ball_subset_closedBall hn)
    simp only [sub_self,norm_zero] at hh
    linarith
  have hharm : (∫ x, V x*Δ g x ∂ballMeasure R) = 0 :=
    normalizedCoreField_weak_harmonic_ball hu A hcore y R h0 hA hg hcg hs Z lam
  have hlp : MemLp (Δ g) (5/3) (ballMeasure R) :=
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg)
      (μ := volume)).mono_measure Measure.restrict_le_self
  have hi : Integrable (fun x => V x*Δ g x) (ballMeasure R) := hp.integrable_mul hlp
  have hi' := tfBallPotential_laplacian_integrable R f hg hcg hs
  have heuler : ∀ᵐ x ∂ballMeasure R, f x =
      (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
    filter_upwards [tfPatchFunctional_euler R Φ tfKinetic_pos
      (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ)
      (fun g hg => tfPatchMinimizer_min R tfKinetic tfKinetic_pos Φ hg),he] with x hx hΦ
    simpa only [hΦ] using hx
  calc
    _ = (∫ x, V x*Δ g x ∂ballMeasure R)-
        (∫ x, tfBallPotential R f x*Δ g x ∂ballMeasure R) := by
      simp only [W,sub_mul]
      exact integral_sub hi hi'
    _ = 4*Real.pi*(∫ x, f x*g x ∂ballMeasure R) := by
      rw [hharm,tfBallPotential_weak_laplacian R f hg hcg hs]
      ring
    _ = _ := by
      congr 1
      exact integral_congr_ae (heuler.mono fun x hx => by simp only [hx]; rfl)

end CoulombAtom

end

end OAI
