import OAI.Geometry.SurfaceImmersion.Primitive.ActualSupportedSurfaceLoop
import OAI.Geometry.SurfaceImmersion.Primitive.RestrictedSurfaceLoop

namespace OAI

/-! The constructed geometric loop in the exact coordinates and support
form used by the primitive polynomial expansion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates

theorem actual_analytic_surface_loop {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U K P : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    (hK : IsCompact K) (hKT : K ⊆ T) (haK : ∀ p ∈ K, 0 < a p)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0) :
    ∃ O : TopologicalSpace.Opens JetPolynomial.LowJet, ∃ l : Loop O,
      IsCompact (JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T)) ∧
      JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T) ⊆ O ∧
      l.HasSpatialAmplitude (a ∘ baseEquiv) ∧
      ∀ J ∈ O, a (baseEquiv (JetPolynomial.lowJetPosition J)) = 0 →
        ∀ t, l.velocity (J,t) = normal J := by
  obtain ⟨Z,hTZ,e₁,e₂,_,_,_,l,hl,⟨W,hW,hCW,hzero⟩,_⟩ :=
    actual_supported_surface_loop hF ha hT hU hTU hn hI hN hHess haT hboundary
      hK hKT haK hP hPK hlocal 0
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
  obtain ⟨O,hQO,_,l',ha',_,hz'⟩ := l.restrict_zero_collar (ha.comp baseEquiv.contDiff) hamp
    hQ (hW.preimage decode_smooth.continuous) hQW hz
  refine ⟨O,l',?_,hQO,ha',hz'⟩
  have hc : IsCompact (baseEquiv ⁻¹' T) := baseEquiv.toHomeomorph.isCompact_preimage.mpr hT
  exact hc.image (JetPolynomial.lowJet_smooth (hF.comp baseEquiv.contDiff)).continuous

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
