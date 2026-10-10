import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialL2

namespace OAI

/-! # Bounded radial test functionals on the actual homogeneous completion

Tensor-product tests turn the completed Cartesian derivatives into bounded
functionals. Their exact radial integral formula is the bridge used when
passing radial integration by parts through the Schwartz completion.
-/

open MeasureTheory

namespace DefocusingNLS

/-- On the dense Schwartz domain the polar completion agrees with the
ordinary Cartesian derivative pulled back along the polar map. -/
theorem homogeneousPolarDerivative_Schwartz_ae (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (j : Fin N → Fin 12) (f : SchwartzMap (EuclideanSpace ℝ (Fin 12)) ℂ) :
    homogeneousPolarDerivative a N ha ha1 hk j
        (homogeneousSchwartzEmbedding a N ha ha1 hk f) =ᵐ[physicalPolarMeasure]
      fun p => homogeneousOrderedDerivative N j f (p.2.1 • p.1.1) := by
  change physicalPolarL2 (homogeneousPhysicalDerivative a N ha ha1 hk j
    (homogeneousSchwartzEmbedding a N ha ha1 hk f)) =ᵐ[physicalPolarMeasure] _
  rw [homogeneousPhysicalDerivative_Schwartz]
  have h := physicalPolarL2_ae (homogeneousOrderedDerivativeL2 N j f)
  have hc := measurePreserving_physicalPolarPoint.quasiMeasurePreserving.ae_eq_comp
    (SchwartzMap.coeFn_toLp (homogeneousOrderedDerivative N j f) 2 volume)
  exact h.trans hc

/-- Square-integrable radial and angular factors give a polar L² test. -/
theorem memLp_polarProductTest (h : PhysicalUnitSphere → ℂ)
    (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure) :
    MemLp (fun p : PhysicalUnitSphere × PhysicalPositiveRadius =>
      h p.1 * star (ψ p.2)) 2 physicalPolarMeasure := by
  have hm := hh.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable.star.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh).mul_prod
    ((memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ)
  simpa only [Pi.mul_apply, Pi.star_apply, Function.comp_apply, norm_mul, norm_star, mul_pow] using hi

noncomputable def polarProductTest (h : PhysicalUnitSphere → ℂ)
    (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure) :
    Lp ℂ 2 physicalPolarMeasure :=
  (memLp_polarProductTest h ψ hh hψ).toLp (fun p => h p.1 * star (ψ p.2))

private theorem integrable_polarTestPair (h : PhysicalUnitSphere → ℂ)
    (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure)
    (F : Lp ℂ 2 physicalPolarMeasure) :
    Integrable (fun p : PhysicalUnitSphere × PhysicalPositiveRadius =>
      inner ℂ (h p.1 * star (ψ p.2)) (F p)) physicalPolarMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (polarProductTest h ψ hh hψ) F).congr
  filter_upwards [(memLp_polarProductTest h ψ hh hψ).coeFn_toLp] with p hp
  change polarProductTest h ψ hh hψ p = _ at hp
  rw [hp]

private theorem inner_polarTest (c ψ z : ℂ) :
    inner ℂ (c * star ψ) z = ψ * inner ℂ c z := by
  simp only [RCLike.inner_apply']
  change star (c * star ψ) * z = ψ * (star c * z)
  rw [star_mul, star_star]
  ring

/-- The test functional is exactly the radial integral of its angular projection. -/
theorem polarProductTest_pairing (h : PhysicalUnitSphere → ℂ)
    (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure)
    (F : Lp ℂ 2 physicalPolarMeasure) :
    inner ℂ (polarProductTest h ψ hh hψ) F =
      ∫ r, ψ r * (∫ ω, inner ℂ (h ω) (F (ω, r)) ∂physicalSphereMeasure)
        ∂physicalRadiusMeasure := by
  rw [L2.inner_def]
  have he : (∫ p, inner ℂ (polarProductTest h ψ hh hψ p) (F p)
      ∂physicalPolarMeasure) =
      ∫ p : PhysicalUnitSphere × PhysicalPositiveRadius,
        inner ℂ (h p.1 * star (ψ p.2)) (F p) ∂physicalPolarMeasure := by
    apply integral_congr_ae
    filter_upwards [(memLp_polarProductTest h ψ hh hψ).coeFn_toLp] with p hp
    change polarProductTest h ψ hh hψ p = _ at hp
    rw [hp]
  rw [he]
  change (∫ p : PhysicalUnitSphere × PhysicalPositiveRadius,
    inner ℂ (h p.1 * star (ψ p.2)) (F p)
      ∂physicalSphereMeasure.prod physicalRadiusMeasure) = _
  rw [integral_prod_symm _ (integrable_polarTestPair h ψ hh hψ F)]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [inner_polarTest, integral_const_mul]

/-- Each separated angular/radial test acts boundedly on an ordered derivative. -/
noncomputable def homogeneousRadialTestComponent (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (h : PhysicalUnitSphere → ℂ) (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure) :
    HomogeneousY a N →L[ℂ] ℂ :=
  (innerSL ℂ (polarProductTest (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω)
    ψ (memLp_radialTensor_test N j h hh) hψ)).comp
    (homogeneousPolarDerivative a N ha ha1 hk j)

/-- The finite contracted test remains bounded on the full completion. -/
noncomputable def homogeneousRadialTest (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure) :
    HomogeneousY a N →L[ℂ] ℂ :=
  ∑ j : Fin N → Fin 12, homogeneousRadialTestComponent a N ha ha1 hk j h ψ hh hψ

/-- The bounded completion-level functional has the expected integral formula. -/
theorem homogeneousRadialTest_apply (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (ψ : PhysicalPositiveRadius → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure) (hψ : MemLp ψ 2 physicalRadiusMeasure)
    (u : HomogeneousY a N) :
    homogeneousRadialTest a N ha ha1 hk h ψ hh hψ u =
      ∫ r, ψ r * homogeneousRadialAngularDerivative a N ha ha1 hk h u r
        ∂physicalRadiusMeasure := by
  classical
  have hi (j : Fin N → Fin 12) :
      Integrable (fun r => ψ r * (∫ ω,
        inner ℂ ((radialTensorCoefficient N j ω : ℂ) * h ω)
          (homogeneousPolarDerivative a N ha ha1 hk j u (ω, r))
          ∂physicalSphereMeasure)) physicalRadiusMeasure := by
    have hpair := (integrable_polarTestPair
      (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω) ψ
      (memLp_radialTensor_test N j h hh) hψ
      (homogeneousPolarDerivative a N ha ha1 hk j u)).integral_prod_right
    simpa only [inner_polarTest, integral_const_mul] using hpair
  simp only [homogeneousRadialTest, sum_apply,
    homogeneousRadialTestComponent, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    polarProductTest_pairing, homogeneousRadialAngularDerivative, Finset.mul_sum]
  exact (integral_finsetSum _ (fun j _ => hi j)).symm

end DefocusingNLS

end OAI
