import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileMap

namespace OAI

/-! The finite-dimensional leading-profile map evaluates to the exact
geometric velocity and its derivatives in the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

private lemma jet_parameter_pullback_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (c : LowJet × ℝ → RealModes.RVec 4)
    (p : JetPolynomial.Base) (t : ℝ) (hc : DifferentiableAt ℝ c (lowJet G p,t))
    (v : JetPolynomial.Base) (a : ℝ) :
    fderiv ℝ (fun q : JetPolynomial.Base × ℝ =>
      JetVelocityCoordinates.toEuclidean (c (lowJet G q.1,q.2))) (p,t) (v,a) =
      JetVelocityCoordinates.toEuclidean (fderiv ℝ c (lowJet G p,t)
        (fderiv ℝ (lowJet G) p v,a)) := by
  have hlow : HasFDerivAt (lowJet G) (fderiv ℝ (lowJet G) p) p :=
    ((lowJet_smooth hG).differentiable (by simp) p).hasFDerivAt
  have hfirst : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => lowJet G q.1)
      ((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)) (p,t) :=
    by
      simpa only [Function.comp_def] using
        (hlow.comp (p,t) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,t))))
  have hP : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))
      (((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)).prod
        (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ)) (p,t) :=
    hfirst.prodMk (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ).hasFDerivAt
  have hd := ((JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp (lowJet G p,t)
    hc.hasFDerivAt).comp (p,t) hP).fderiv
  change (fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ c) ∘
    (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))) (p,t)) (v,a) = _
  rw [hd]
  rfl

lemma geometry_longitudinal_value {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    (l.geometry G hG hGO).longitudinal.val p (t : Period) =
      JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G p,t)) := by
  rw [Geometry.longitudinal,Family.add_apply,Family.constant_apply _ _ hp,
    l.geometry_velocity hG hGO hp,l.euclideanVelocity_apply (hGO hp)]
  exact (map_add JetVelocityCoordinates.toEuclidean _ _).symm

/-- All five entries depend on the third jet only through the single
transverse derivative of the second jet. -/
theorem leadingProfileMap_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) =
      ![(l.geometry G hG hGO).longitudinal.val p (t : Period),
        (l.geometry G hG hGO).Y p,(l.geometry G hG hGO).C p,
        ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period),
        (l.geometry G hG hGO).V.angle.val p (t : Period)] := by
  have hlong : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).longitudinal.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    exact l.geometry_longitudinal_value hG hGO hq.1 q.2
  have hvel : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).V.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.velocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    rw [l.geometry_velocity hG hGO hq.1,l.euclideanVelocity_apply (hGO hq.1)]
  have hmem : (lowJet G p,t) ∈ (O : Set LowJet) ×ˢ univ := ⟨hGO hp,mem_univ t⟩
  have hW := (l.leadingVelocity_smooth.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
  have hV := (l.smoothVelocity.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
  funext i
  fin_cases i
  · exact (l.geometry_longitudinal_value hG hGO hp t).symm
  · rfl
  · rfl
  · change JetVelocityCoordinates.toEuclidean
        (fderiv ℝ l.leadingVelocity (lowJet G p,t) (lowDerivative G 1 p,0)) =
      ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period)
    rw [Family.slow_apply _ _ hp]
    change _ = fderiv ℝ _ (p,t) (coordinateVector 1,0)
    rw [hlong.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hW,
      lowJet_derivative hG]
  · change JetVelocityCoordinates.toEuclidean (fderiv ℝ l.velocity (lowJet G p,t) (0,1)) =
      (l.geometry G hG hGO).V.angle.val p (t : Period)
    rw [Family.angle_apply _ hp]
    change _ = fderiv ℝ _ (p,t) (0,1)
    rw [hvel.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hV,map_zero]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
