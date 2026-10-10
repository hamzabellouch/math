import OAI.Geometry.SurfaceImmersion.Geometry.LeadingInputStability

namespace OAI

/-! Uniform C3 stability of the leading profiles on a compact spatial set,
including every phase on the period circle. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma leadingProfileMap_uniform_near {K : Set LeadingProfileInput} (hK : IsCompact K)
    (hKO : ∀ J ∈ K, J.1.1 ∈ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ H : LeadingProfileInput,
      ‖H-J‖ < δ → ‖l.leadingProfileMap H-l.leadingProfileMap J‖ < ε := by
  have hh := hK.uniformContinuousAt_of_continuousAt l.leadingProfileMap
    (fun J hJ => l.leadingProfileMap_continuousAt (hKO J hJ)) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ,hδ,hclose⟩ := Metric.mem_uniformity_dist.mp hh
  refine ⟨δ,hδ,?_⟩
  intro J hJ H hHJ
  have hd : dist J H < δ := by simpa only [dist_eq_norm,norm_sub_rev] using hHJ
  simpa only [Set.mem_ofPred_eq,Prod.fst,Prod.snd,dist_eq_norm,norm_sub_rev] using hclose hd hJ

def geometricLeadingProfile {S : TopologicalSpace.Opens JetPolynomial.Base}
    (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (p : JetPolynomial.Base) (t : Period) :
    EuclideanBoundaryProfile :=
  ![(l.geometry G hG hGO).longitudinal.val p t,(l.geometry G hG hGO).Y p,
    (l.geometry G hG hGO).C p,
    ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p t,
    (l.geometry G hG hGO).V.angle.val p t]

/-- The slow baseline may be replaced by the original map in all five
leading profiles, using only its unweighted C3 error. -/
theorem geometricLeadingProfile_stability {S : TopologicalSpace.Opens JetPolynomial.Base}
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    (hFO : MapsTo (lowJet F) S O) {K : Set JetPolynomial.Base}
    (hK : IsCompact K) (hKS : K ⊆ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : JetPolynomial.Base → JetPolynomial.Space,
      ∀ hG : ContDiff ℝ ∞ G, ∀ hGO : MapsTo (lowJet G) S O,
      WeightedBound S 1 3 δ (fun p => G p-F p) → ∀ p ∈ K, ∀ t : Period,
        ‖l.geometricLeadingProfile G hG hGO p t-l.geometricLeadingProfile F hF hFO p t‖ < ε := by
  let B : JetPolynomial.Base × ℝ → LeadingProfileInput := fun z =>
    ((lowJet F z.1,z.2),lowDerivative F 1 z.1)
  have hD : Continuous (lowDerivative F 1) := by
    have hh : ContDiff ℝ ∞ (fun p => fderiv ℝ (lowJet F) p (coordinateVector 1)) :=
      ((lowJet_smooth hF).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (lowJet F) p (coordinateVector 1)) = lowDerivative F 1 :=
      funext (lowJet_derivative hF 1)
    rw [he] at hh
    exact hh.continuous
  have hB : Continuous B :=
    (((lowJet_smooth hF).continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      (hD.comp continuous_fst)
  have hBK : IsCompact (B '' (K ×ˢ Icc (0 : ℝ) 1)) :=
    (hK.prod isCompact_Icc).image hB
  obtain ⟨r,hr,hclose⟩ := l.leadingProfileMap_uniform_near hBK
    (by rintro _ ⟨z,hz,rfl⟩; exact hFO (hKS hz.1)) ε hε
  refine ⟨r/2,half_pos hr,?_⟩
  intro G hG hGO hb p hp t
  have ht : t ∈ ((↑) : ℝ → Period) '' Icc (0 : ℝ) (0+1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨s,hs,hst⟩ := ht
  have hinput := leadingInput_sub_bound S.isOpen hF hG (half_pos hr).le hb (hKS hp) s
  have hinput' : ‖(((lowJet G p,s),lowDerivative G 1 p) : LeadingProfileInput)-B (p,s)‖ < r :=
    hinput.trans_lt (half_lt_self hr)
  have he := hclose (B (p,s)) (mem_image_of_mem B ⟨hp,by simpa only [zero_add] using hs⟩)
    ((lowJet G p,s),lowDerivative G 1 p) hinput'
  rw [l.leadingProfileMap_geometry hG hGO (hKS hp) s] at he
  change ‖_ - l.leadingProfileMap ((lowJet F p,s),lowDerivative F 1 p)‖ < ε at he
  rw [l.leadingProfileMap_geometry hF hFO (hKS hp) s] at he
  simpa only [geometricLeadingProfile,hst] using he

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
