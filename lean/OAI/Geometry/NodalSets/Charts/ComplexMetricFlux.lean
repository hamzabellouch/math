import OAI.Geometry.NodalSets.Charts.AbsolutePiola
import OAI.Geometry.NodalSets.Charts.MetricFluxPullback

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourceFlux (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (u : Coord → ℂ) (i : Fin 4) (x : Coord) : ℂ :=
  ∑ j, ((w x : ℂ) * (sourcePrincipal g i j x : ℂ)) * coordPartial j u x

def pulledFlux (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (p : QuadParam Coord) (u : Coord → ℂ) (i : Fin 4) (x : Coord) : ℂ :=
  ∑ j, ((chartDensity w p x : ℂ) * complexPrincipal g i j p x) * coordPartial j u x

lemma sourcePrincipal_smooth_at
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (sourcePrincipal g i j) x := by
  have hi : ContDiffAt ℝ ∞ (fun z ↦ ContinuousLinearMap.inverse (g z)) x := by
    have h := contDiffAt_map_inverse (n := ∞) (positiveMetricEquiv (g x) hp)
    exact h.comp x hg.contDiffAt
  exact (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (hi.clm_apply contDiffAt_const)

lemma sourceFlux_smooth_at
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (x : Coord) (hp : ∀ v, v ≠ 0 → 0 < g x v v) (i : Fin 4) :
    ContDiffAt ℝ ∞ (sourceFlux g w u i) x := by
  apply ContDiffAt.sum
  intro j _
  exact ((Complex.ofRealCLM.contDiff.comp hw).contDiffAt.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x (sourcePrincipal_smooth_at g hg x hp i j))).mul
      (coordPartial_contDiff hu j).contDiffAt

lemma complex_principal_jacobian
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    ((jacobian (rawQuadratic p) x).det : ℂ) *
      (∑ j, complexPrincipal g i j p x * (jacobian (rawQuadratic p) x a j : ℂ)) =
      ∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
        (sourcePrincipal g b a (rawQuadratic p x) : ℂ) := by
  unfold complexPrincipal
  exact_mod_cast determinant_principal_jacobian g p x hp J hJ i a

lemma complex_gradient_flux_transform
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : Coord → ℂ) (hu : DifferentiableAt ℝ u (rawQuadratic p x)) (i : Fin 4) :
    ((jacobian (rawQuadratic p) x).det : ℂ) *
      (∑ j, complexPrincipal g i j p x * coordPartial j (u ∘ rawQuadratic p) x) =
      ∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
        (∑ a, (sourcePrincipal g b a (rawQuadratic p x) : ℂ) * coordPartial a u (rawQuadratic p x)) := by
  have hF : DifferentiableAt ℝ (rawQuadratic p) x :=
    (rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
  simp_rw [coordPartial_comp (rawQuadratic p) x hF u hu]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (((jacobian (rawQuadratic p) x).det : ℂ) *
        ∑ j, complexPrincipal g i j p x * (jacobian (rawQuadratic p) x a j : ℂ)) *
          coordPartial a u (rawQuadratic p x) := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = _ := by
      simp_rw [complex_principal_jacobian g p x hp J hJ]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem actual_pulled_flux
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : Coord → ℂ) (hu : DifferentiableAt ℝ u (rawQuadratic p x)) (i : Fin 4) :
    pulledFlux g w p (u ∘ rawQuadratic p) i x =
      absolutePiola (rawQuadratic p) (sourceFlux g w u) i x := by
  have he := complex_gradient_flux_transform g p x hp J hJ u hu i
  have hd : (jacobian (rawQuadratic p) x).det ≠ 0 := by
    change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
    rw [hJ]
    exact coordDet_equiv_ne_zero J
  have hdC := Complex.ofReal_ne_zero.mpr hd
  have hsource : signedPiola (rawQuadratic p) (sourceFlux g w u) i x =
      (w (rawQuadratic p x) : ℂ) *
        (∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
          ∑ a, (sourcePrincipal g b a (rawQuadratic p x) : ℂ) * coordPartial a u (rawQuadratic p x)) := by
    simp only [signedPiola,sourceFlux,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold absolutePiola
  rw [hsource, ← he]
  have hpull : pulledFlux g w p (u ∘ rawQuadratic p) i x =
      (w (rawQuadratic p x) : ℂ) * ((|(jacobian (rawQuadratic p) x).det| : ℝ) : ℂ) *
        ∑ j, complexPrincipal g i j p x * coordPartial j (u ∘ rawQuadratic p) x := by
    simp only [pulledFlux,chartDensity,coordDet,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
    rfl
  rw [hpull]
  push_cast
  field_simp

end
end Yau.Geometry

end OAI
