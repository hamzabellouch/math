import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCurveCrossingLoop
import OAI.Geometry.SurfaceImmersion.Primitive.ActualAnalyticProfiledLoop
import OAI.Geometry.SurfaceImmersion.Primitive.ActualCircularPeriod

namespace OAI

/-! Retain the finite-curve and crossing conclusions while restricting to
the low-jet domain required by the exact primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity PhaseGeometry SurfaceJetCoordinates

variable {ι : Type*} [Finite ι]

theorem actual_analytic_curve_crossing_loop {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    {K : ι → Set Base} (hK : ∀ i, IsCompact (K i)) (hKT : ∀ i, K i ⊆ T)
    {P : Set Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ i, K i) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ (⋃ i, K i) ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0)
    {E : Set Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c k : ι → Base → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hk : ∀ i, ContDiff ℝ ∞ (k i))
    (hbc : ∀ i, ∀ x ∈ K i, b i x ≠ 0 ∨ c i x ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ i, ∀ x ∈ K i, -B ≤ k i x)
    (hold : ∀ i, ∀ x ∈ K i, a x = 0 →
      0 < ((coordDeriv dy (coordDeriv dx F) x ⬝ᵥ normalize (realSecondForm F dy dy x))*b i x +
        Real.sqrt (realSecondForm F dy dy x ⬝ᵥ realSecondForm F dy dy x)*c i x)^2 + k i x*(b i x)^2) :
    ∃ Z : TopologicalSpace.Opens GeometricJet,
      jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
    ∃ O : TopologicalSpace.Opens JetPolynomial.LowJet, (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z ∧
    ∃ l : Loop O,
      IsCompact (JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T)) ∧
      JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T) ⊆ O ∧
      l.HasSpatialAmplitude (a ∘ baseEquiv) ∧
      (∀ J ∈ O, a (baseEquiv (JetPolynomial.lowJetPosition J)) = 0 →
        ∀ t, l.velocity (J,t) = normal J) ∧
    ∃ e₁ e₂ : GeometricJet → Vec, ∃ α : GeometricJet × ℝ → ℝ,
      ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧ ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
      (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
      (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
    (∀ x ∈ T, ∀ t : ℝ, surfaceCircularProfile F a e₁ e₂ α (x,t) ∈ regularBoundaryProfiles) ∧
    ∃ η : ℝ, 0 < η ∧
      (∀ z : ℝ, 0 < z → z < η →
      ∀ i, ∀ x ∈ K i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      k i x ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      realSecondForm G (b i x,c i x) (b i x,c i x) p ≠ 0 ∧
      normalize (realSecondForm G (b i x,c i x) (b i x,c i x) p) ≠
        -profilePreferred (realBoundaryProfile G z p)) ∧
      ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ p : Base,
      ‖realBoundaryProfile G z p-surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < η →
      ∀ κ : ℝ,
      coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p =
        κ*gramDet (coordDeriv dx G p) (coordDeriv dy G p) →
      -B ≤ coordinateGauss (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p →
      ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        0 < orderedCrossing G (1,r) (1,s) p κ ∧
        0 < orderedCrossing G (1,s) (1,r) p κ ∧
        ((0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p) ∧
          0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ profilePreferred (realBoundaryProfile G z p)) ∨
         (0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ realSecondForm G (1,s) (1,s) p ∧
           ∃ w : Vec, profilePreferred (realBoundaryProfile G z p) ⬝ᵥ w = 0 ∧
             0 < realSecondForm G (1,r) (1,r) p ⬝ᵥ w ∧
             0 < realSecondForm G (1,s) (1,s) p ⬝ᵥ w)) := by
  obtain ⟨Z,hTZ,hZU,l,hl,⟨W,hW,hCW,hzero⟩,e₁,e₂,α,h₁,h₂,hα,hper,hvel,hreg,η,hη,hcurves,hcross⟩ :=
    actual_supported_curve_crossing_loop hF ha hT hU hTU hn hI hN hHess haT hboundary
      hK hKT hP hlocal hE hET haE slopeBound hSlope hb hc hk hbc B hB hkb hold
  let Q := JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T)
  have hQ : Q ⊆ jetDomain Z := by
    rintro _ ⟨p,hp,rfl⟩
    exact actual_jet_mem hF (hTZ (mem_image_of_mem _ hp))
  have hepos (J : JetPolynomial.LowJet) :
      (decode J).1 = baseEquiv (JetPolynomial.lowJetPosition J) := rfl
  have hamp : l.HasSpatialAmplitude (a ∘ baseEquiv) := by
    intro J _
    exact hl J
  have hQW : ∀ J ∈ Q, (a ∘ baseEquiv) (JetPolynomial.lowJetPosition J) = 0 →
      J ∈ decode ⁻¹' W := by
    rintro _ ⟨p,hp,rfl⟩ hz
    rw [JetPolynomial.lowJetPosition_lowJet] at hz
    change decode (JetPolynomial.lowJet (F ∘ baseEquiv) p) ∈ W
    rw [decode_lowJet hF]
    exact hCW (mem_image_of_mem _ ⟨hp,hz⟩)
  have hz : ∀ J ∈ decode ⁻¹' W,
      (a ∘ baseEquiv) (JetPolynomial.lowJetPosition J) = 0 →
      ∀ t, l.velocity (J,t) = normal J := by
    intro J hJ haJ t
    apply hzero J hJ _ t
    rw [hepos]
    exact haJ
  obtain ⟨O,hQO,hOZ,l',ha',hvel',hz'⟩ := l.restrict_zero_collar (ha.comp baseEquiv.contDiff) hamp
    hQ (hW.preimage decode_smooth.continuous) hQW hz
  refine ⟨Z,hTZ,hZU,O,hOZ,l',?_,hQO,ha',hz',e₁,e₂,α,h₁,h₂,hα,hper,?_,hreg,η,hη,hcurves,hcross⟩
  · exact (baseEquiv.toHomeomorph.isCompact_preimage.mpr hT).image
      (JetPolynomial.lowJet_smooth (hF.comp baseEquiv.contDiff)).continuous
  · intro J t
    rw [hvel']
    exact hvel J t

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
