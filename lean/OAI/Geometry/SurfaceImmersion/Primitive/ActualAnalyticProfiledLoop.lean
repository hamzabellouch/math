import OAI.Geometry.SurfaceImmersion.Primitive.ActualProfiledSurfaceLoop
import OAI.Geometry.SurfaceImmersion.Primitive.RestrictedSurfaceLoop

namespace OAI

/-! The constructed geometric loop in the exact coordinates and support
form used by the primitive polynomial expansion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation

theorem actual_analytic_surface_loop_profiles {F n : Base → Vec} {a : Base → ℝ}
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
    ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
    ∀ H : ℝ, 0 ≤ H →
    ∃ Z : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Z ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Z ∧ ContDiffOn ℝ ∞ e₂ Z ∧
        (∀ j ∈ Z, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      ∃ O : TopologicalSpace.Opens JetPolynomial.LowJet, (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z ∧
      ∃ l : Loop O,
        IsCompact (JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T)) ∧
        JetPolynomial.lowJet (F ∘ baseEquiv) '' (baseEquiv ⁻¹' T) ⊆ O ∧
        l.HasSpatialAmplitude (a ∘ baseEquiv) ∧
        (∀ J ∈ O, a (baseEquiv (JetPolynomial.lowJetPosition J)) = 0 →
          ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
            let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
            J ∈ regularBoundaryProfiles ∧
            sLo ≤ profileCoefficients J 0 ∧ profileCoefficients J 0 ≤ sHi ∧
            |profileCoefficients J 1| ≤ D ∧
            (profileCoefficients J 3 = 0 → H+2 < |profileCoefficients J 2|) := by
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hloop⟩ :=
    actual_supported_surface_loop_profiles hF ha hT hU hTU hn hI hN hHess haT hboundary
      hK hKT haK hP hPK hlocal
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Z,hTZ,e₁,e₂,h₁,h₂,hframe,l,hl,⟨W,hW,hCW,hzero⟩,α,hα,hper,hvel,hprofiles⟩ := hloop H hH
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
  refine ⟨Z,hTZ,e₁,e₂,h₁,h₂,hframe,O,hOZ,l',?_,hQO,ha',hz',α,hα,hper,?_,hprofiles⟩
  · have hc : IsCompact (baseEquiv ⁻¹' T) := baseEquiv.toHomeomorph.isCompact_preimage.mpr hT
    exact hc.image (JetPolynomial.lowJet_smooth (hF.comp baseEquiv.contDiff)).continuous

  · intro J t
    rw [hvel']
    exact hvel J t

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
