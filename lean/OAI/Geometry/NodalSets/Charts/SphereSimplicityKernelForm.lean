import OAI.Geometry.NodalSets.Charts.SphereSimplicityAnnihilation
import OAI.Geometry.NodalSets.Charts.SphereSimplicityBump
import OAI.Geometry.NodalSets.Charts.SphereSimplicityExtension
import OAI.Geometry.NodalSets.Charts.SphereSimplicityKernel

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem exists_sphere_simplicity_kernel_form (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (r : ℝ) (hradius : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (zeta : Yau.Jets.Coord → ℝ) (a b : Base → ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧ ContDiff ℝ ∞ zeta ∧ tsupport zeta ⊆ Q ∧
      (∀ x, 0 ≤ zeta x) ∧ (∃ x, 0 < zeta x) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2) ∧
      (∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
        (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) ∧
      (∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (u ∘ seedSphereFromCoord) y i) x+
        lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) ∧
      (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        0 ≤ sphereEnergyForm a b lam v v ∧ sphereEnergyForm a b lam u v = 0) ∧
      ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        (∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
        (sphereEnergyForm a b lam v v = 0 ↔ ∃ c : ℝ, ∀ p, v p = c*u p) := by
  obtain ⟨Q,zeta,Z,s,hQ,hQr,hz,hzQ,hzn,hs0,hz1,hZ,hZQ,hZval,hZn,hU⟩ :=
    exists_sphere_simplicity_bump hradius
  obtain ⟨a,b,ha,hb,haQ,hbQ,haval,hbval,hcancel⟩ :=
    sphere_simplicity_extension u hu lam hlam.ne' zeta hz hQ hzQ
  have hzc : HasCompactSupport zeta := hQ.of_isClosed_subset isClosed_closure hzQ
  have hzpos : ∃ x, 0 < zeta x := ⟨0,by rw [hz1 0 (Metric.mem_closedBall_self hs0.le)]; norm_num⟩
  refine ⟨Q,zeta,a,b,hQ,hQr,hz,hzQ,(fun x ↦ (hzn x).1),hzpos,ha,hb,haQ,hbQ,haval,hbval,hcancel,?_,?_⟩
  · intro v hv
    exact ⟨sphere_simplicity_energy_nonneg u v a b hu hv zeta hz hzc (fun x ↦ (hzn x).1)
        lam hlam.ne' haval hbval,
      sphere_simplicity_form_annihilates u a b Z hu ha hb hQ haQ hbQ zeta hz hzc lam hlam.ne'
        haval hbval hZval v hv⟩
  · intro v hv hev
    exact sphere_simplicity_energy_kernel_iff A hA hs hp rho hr hrp u v a b hu hv hune lam hlam.ne'
      heu hev zeta hz hzc (fun x ↦ (hzn x).1) hzpos haval hbval

end
end Yau.Target

end OAI
