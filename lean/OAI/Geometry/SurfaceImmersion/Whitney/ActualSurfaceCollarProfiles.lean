import OAI.Geometry.SurfaceImmersion.Whitney.ActualSurfaceCollarFamily
import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCircularThreshold
import OAI.Geometry.SurfaceImmersion.Primitive.ClosedIntervalTurns

namespace OAI

/-! The preferred frame and its domain are fixed before prescribing the
transverse turn size in the actual supported loop construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation

theorem actual_surface_collar_profile_family {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    :
    ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
      (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      (∃ B : Set GeometricJet, IsOpen B ∧
        CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ B ∧
        ∀ j ∈ B, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) ∧
      ∃ sLo sHi D : ℝ, 0 < sLo ∧ 0 < sHi ∧ 0 ≤ D ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set Base, IsOpen V ∧ {p ∈ T | a p = 0} ⊆ V ∧
      ∀ (K P : Set Base), IsCompact K → K ⊆ T → (∀ p ∈ K, 0 < a p) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ H : ℝ, 0 ≤ H → ∃ Z : TopologicalSpace.Opens GeometricJet,
        CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          (∀ x ∈ V, ∀ t, |α (CollarVelocity.jetSection F x,t)| < ε) ∧
          (∀ x ∈ T, ∀ t : ℝ,
            let J := surfaceCircularProfile F a e₁ e₂ α (x,t)
            J ∈ regularBoundaryProfiles ∧ sLo ≤ profileCoefficients J 0 ∧
              profileCoefficients J 0 ≤ sHi ∧ |profileCoefficients J 1| ≤ D) ∧
          ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
            profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 3 = 0 →
              H+2 < |profileCoefficients (surfaceCircularProfile F a e₁ e₂ α (x,t)) 2| := by
  obtain ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hcollar,hfamily⟩ :=
    actual_surface_collar_family hF ha hT hU hTU hn hI hN hHess haT hboundary
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hthreshold⟩ :=
    compact_surface_circular_threshold hF ha hΩ hT hTΩ h₁ h₂ hframe
  refine ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hcollar,sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hfamily'⟩ := hfamily ε hε
  refine ⟨V,hV,hCV,?_⟩
  intro K P hK hKT haK hP hPK hlocal H hH
  obtain ⟨Λ,_,hprofile⟩ := hthreshold H hH
  obtain ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,τ,hturn,hlarge⟩ :=
    hfamily' K P hK hKT haK hP hPK hlocal Λ
  refine ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,hsmall,?_,?_⟩
  · intro x hx t
    obtain ⟨hreg,hlo,hhi,hd,_⟩ := hprofile Z hTZ hZΩ α hα x hx t
    exact ⟨hreg,hlo,hhi,hd⟩
  · let W : Set Base := CollarVelocity.jetSection F ⁻¹' Z
    have hσ := CollarVelocity.jetSection_smooth hF
    have hW : IsOpen W := Z.isOpen.preimage hσ.continuous
    have hKW : K ⊆ W := fun x hx => hTZ (mem_image_of_mem _ (hKT hx))
    have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
        (W ×ˢ univ) :=
      hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
    have hturn' := closed_interval_turns hW hKW hα'
      (fun x hx => hper (CollarVelocity.jetSection F x) hx) hturn hlarge
    intro x hx t ht hz
    apply (hprofile Z hTZ hZΩ α hα x (hKT hx) t).2.2.2.2
    apply hturn' x hx t ht
    exact (surfaceCircularProfile_turn_iff hΩ hframe α
      (hTΩ (mem_image_of_mem _ (hKT hx))) t).mp hz

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
