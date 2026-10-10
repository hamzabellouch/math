import OAI.Analysis.CircleDomains.Modulus.NormalizedLimits

namespace OAI

/-!
# Applying normalized compactness to sphere models

All complex-plane hypotheses of the compactness theorem are obtained
from actual normalized smooth sphere equivalences and their retained
holomorphic cores. The exterior estimate follows from the univalent
area theorem.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finite_part_injOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q) :
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz w hw he
  apply OnePoint.coe_injective
  apply heq.bijOn.injOn (hDQ z hz) (hDQ w hw)
  calc
    f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (coe_finiteCoord (heq.finite_forward hinf hfix (hDQ z hz))).symm
    _ = ((finiteCoord (f (w : Sphere)) : ℂ) : Sphere) := congrArg ((↑) : ℂ → Sphere) he
    _ = f (w : Sphere) := coe_finiteCoord (heq.finite_forward hinf hfix (hDQ w hw))

theorem finite_part_differentiableOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hD : IsOpen D) (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q)
    (hconf : IsConformalOn f (((↑) : ℂ → Sphere) '' D)) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz
  exact (analyticAt_finite_map_of_conformal (OnePoint.isOpenMap_coe D hD)
    hconf (mem_image_of_mem _ hz)
    (heq.finite_forward hinf hfix (hDQ z hz))).differentiableAt.differentiableWithinAt

theorem normalized_sphere_model_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem)
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V) {R : ℝ} (hR : 0 < R)
    (hsource : ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q)
    (hconf : IsConformalOn f ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : IsPrincipalNormalized f) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ →
      ‖finiteCoord (f (z : Sphere)) - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf : OnePoint.infty ∈ Q := hsource (by simp)
  have hDQ : ∀ z : ℂ, z ∈ {z | R < ‖z‖} → (z : Sphere) ∈ Q := by
    intro z hz
    apply hsource
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
      dist_zero_right, mem_compl_iff, not_lt] using hz.le
  apply harea.scaled_exterior_decay hR
  · apply finite_part_differentiableOn heq hinf hnorm.1
      (isOpen_lt continuous_const continuous_norm) hDQ
    apply hconf.mono
    rintro _ ⟨z, hz, rfl⟩
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
      dist_zero_right, mem_compl_iff, not_le] using (show R < ‖z‖ from hz)
  · exact finite_part_injOn heq hinf hnorm.1 hDQ
  · exact hnorm.2

theorem exists_normalized_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ F (⋃ n, D n) ∧ InjOn F (⋃ n, D n) ∧
      (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  apply exists_normalized_univalent_limit hmontel hhurwitz hR hD hconn hmono
    (fun n => finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1
      (hD n) (hDQ n) (hcore n))
    (fun n => finite_part_injOn (heq n) (hinf n) (hnorm n).1 (hDQ n)) hext
  · intro n z hz hzn
    obtain ⟨_, hbound⟩ := normalized_model_uniform_bound harea (heq n) (hV n)
      hR (hsource n) (hconf n) (hnorm n)
    obtain ⟨w, hw, hweq⟩ := hbound z (hDQ n z hz) hzn
    have he : w = finiteCoord (f n (z : Sphere)) := by
      have := congrArg finiteCoord hweq
      simpa only [finiteCoord_coe] using this
    simpa only [Metric.mem_closedBall, dist_zero_right, he] using hw
  · intro n
    exact normalized_sphere_model_exterior_decay harea (heq n) hR
      (hsource n) (hconf n) (hnorm n)

end CircleDomainRigidity

end

end OAI
