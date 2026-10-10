import OAI.Analysis.CircleDomains.Sobolev.SphericalWeightedCoarea
import OAI.Analysis.CircleDomains.Sobolev.CircleBranchEnergy

namespace OAI

/-! Two fixed cuts reduce the weighted-length estimate for a smooth
circle coordinate to the published scalar coarea specialization. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem ae_finite_spherical_circle_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    {D : Set ℂ} (hD : IsOpen D) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv u z‖ ^ 2) < ∞)
    (A : UnitAddCircle → Set Sphere)
    (hA : ∀ θ, ((↑) : ℂ → Sphere) ⁻¹' A θ ⊆ D ∩ {z | u z = θ})
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in A θ, g p ∂(μH[1] : Measure Sphere)) < ∞ := by
  let O (a : ℝ) := D ∩ u ⁻¹' ({(a : UnitAddCircle)}ᶜ)
  let S (a : ℝ) (θ : UnitAddCircle) : Set Sphere :=
    ((↑) : ℂ → Sphere) '' (O a ∩ {z | (circleBranch u a z : UnitAddCircle) = θ})
  have hO (a : ℝ) : IsOpen (O a) :=
    hu.continuousOn.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl
  have hcut (a : ℝ) : ∀ z ∈ O a, u z ≠ (a : UnitAddCircle) := fun _ hz => hz.2
  have hs (a : ℝ) : ContDiffOn ℝ 1 (circleBranch u a) (O a) :=
    (smooth_circleBranch hu a inter_subset_left (hcut a)).of_le (by simp)
  have he (a : ℝ) : (∫⁻ z in O a, ENNReal.ofReal (‖fderiv ℝ (circleBranch u a) z‖ ^ 2)) < ∞ := by
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    exact (circleBranch_energy_le hu a (hO a).measurableSet inter_subset_left (hcut a) volume).trans_lt henergy
  have hpre (a : ℝ) (θ : UnitAddCircle) : ((↑) : ℂ → Sphere) ⁻¹' S a θ =
      O a ∩ {z | (circleBranch u a z : UnitAddCircle) = θ} :=
    Set.preimage_image_eq _ OnePoint.coe_injective
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  have hfinite (a : ℝ) := ae_finite_spherical_weighted_levels hcoarea hC hderiv
    (hO a) (hs a) (he a) (S a) (hpre a) g hg hg2
  have hneq : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro h
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hh).mp h
    norm_num at heq
  have hsub (θ : UnitAddCircle) : A θ ⊆ S 0 θ ∪ S (1 / 2) θ ∪ {OnePoint.infty} := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      have hz : z ∈ D ∧ u z = θ := hA θ hp
      by_cases h0 : u z ≠ (0 : UnitAddCircle)
      · exact Or.inl (Or.inl ⟨z, ⟨⟨hz.1, h0⟩, by simpa only [Set.mem_ofPred_eq, coe_circleBranch] using hz.2⟩, rfl⟩)
      · have hh : u z ≠ ((1 / 2 : ℝ) : UnitAddCircle) :=
          fun h => hneq ((not_not.mp h0).symm.trans h)
        exact Or.inl (Or.inr ⟨z, ⟨⟨hz.1, hh⟩, by simpa only [Set.mem_ofPred_eq, coe_circleBranch] using hz.2⟩, rfl⟩)
  filter_upwards [hfinite 0, hfinite (1 / 2)] with θ h0 hh
  apply lt_of_le_of_lt (lintegral_mono_set (hsub θ))
  apply lt_of_le_of_lt (lintegral_union_le g _ _)
  let := Measure.nullSingletonClass_hausdorff Sphere (by norm_num : (0 : ℝ) < 1)
  have hz : (∫⁻ p in ({OnePoint.infty} : Set Sphere), g p ∂(μH[1] : Measure Sphere)) = 0 := by
    simp
  rw [hz, add_zero]
  exact (lintegral_union_le g _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨h0, hh⟩)

end CircleDomainRigidity

end

end OAI
