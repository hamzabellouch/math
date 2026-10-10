import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileGeometry

namespace OAI

/-! Uniform regularity of every five-profile perturbation along a compact
set of spatial points and one full oscillation period. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma geometricProfile_real_continuousOn {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) :
    ContinuousOn (fun z : JetPolynomial.Base × ℝ => boundaryProfileMap
      (l.geometricLeadingProfile G hG hGO z.1 (z.2 : CovarianceCorrector.Period))) (S ×ˢ univ) := by
  have hd : ContDiff ℝ ∞ (lowDerivative G 1) := by
    convert ((lowJet_smooth hG).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector 1)) using 1
    funext p
    exact (lowJet_derivative hG 1 p).symm
  let f : JetPolynomial.Base × ℝ → LeadingProfileInput :=
    fun z => ((lowJet G z.1,z.2),lowDerivative G 1 z.1)
  have hf : Continuous f :=
    (((lowJet_smooth hG).continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      (hd.continuous.comp continuous_fst)
  have hmaps : MapsTo f (S ×ˢ univ) ((O ×ˢ univ) ×ˢ univ) :=
    fun z hz => ⟨⟨hGO hz.1,mem_univ _⟩,mem_univ _⟩
  have hh := boundaryProfileMap.continuous.comp_continuousOn
    (l.leadingProfileMap_smooth.continuousOn.comp hf.continuousOn hmaps)
  apply hh.congr
  intro z hz
  exact congrArg boundaryProfileMap (l.leadingProfileMap_geometry hG hGO hz.1 z.2).symm

theorem compact_regular_profile_family {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {J : X → BoundaryProfile}
    (hJ : ContinuousOn J K) (hreg : ∀ x ∈ K, J x ∈ regularBoundaryProfiles) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ H : BoundaryProfile, ‖H-J x‖ < δ →
      H ∈ regularBoundaryProfiles := by
  have hc : IsCompact (J '' K) := hK.image_of_continuousOn hJ
  have hr : J '' K ⊆ regularBoundaryProfiles := by
    rintro _ ⟨x,hx,rfl⟩
    exact hreg x hx
  obtain ⟨δ,hδ,hnear⟩ := compact_boundary_profile_stability hc hr 1 zero_lt_one
  exact ⟨δ,hδ,fun x hx H herr => (hnear _ (mem_image_of_mem J hx) H herr).1⟩

theorem compact_leading_regularity {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {C : Set JetPolynomial.Base}
    (hC : IsCompact C) (hCS : C ⊆ S)
    (hreg : ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1,
      boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period)) ∈
        regularBoundaryProfiles) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ H : BoundaryProfile,
      ‖H-boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period))‖ < δ →
      H ∈ regularBoundaryProfiles := by
  let f : JetPolynomial.Base × ℝ → BoundaryProfile := fun z =>
    boundaryProfileMap (l.geometricLeadingProfile G hG hGO z.1 (z.2 : CovarianceCorrector.Period))
  have hf : ContinuousOn f (C ×ˢ Icc (0 : ℝ) 1) :=
    (l.geometricProfile_real_continuousOn hG hGO).mono (fun z hz => ⟨hCS hz.1,mem_univ _⟩)
  obtain ⟨δ,hδ,hnear⟩ := compact_regular_profile_family (hC.prod isCompact_Icc) hf
    (fun z hz => hreg z.1 hz.1 z.2 hz.2)
  exact ⟨δ,hδ,fun p hp t ht H herr => hnear (p,t) ⟨hp,ht⟩ H herr⟩

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
