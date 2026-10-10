import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCircularThreshold
import OAI.Geometry.SurfaceImmersion.Primitive.ClosedIntervalTurns

namespace OAI

/-! Construct a supported periodic surface loop from an actual immersion,
a preferred normal, a positive phase Hessian and the prescribed amplitude. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates GeometryPreservation

theorem actual_supported_surface_loop_profiles {F n : Base → Vec} {a : Base → ℝ}
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
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
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
  obtain ⟨Ω,hTΩ,hΩ,e₁,e₂,h₁,h₂,hframe,hloop⟩ :=
    actual_supported_surface_loop_fixed_frame hF ha hT hU hTU hn hI hN hHess haT hboundary
      hK hKT haK hP hPK hlocal
  have hKΩ : CollarVelocity.jetSection F '' K ⊆ Ω := (image_mono hKT).trans hTΩ
  obtain ⟨sLo,sHi,D,hsLo,hsHi,hD0,hthreshold⟩ :=
    compact_surface_circular_threshold hF ha hΩ hK hKΩ h₁ h₂ hframe
  refine ⟨sLo,sHi,D,hsLo,hsHi,hD0,?_⟩
  intro H hH
  obtain ⟨Λ,hΛ,hprofile⟩ := hthreshold H hH
  obtain ⟨Z,hTZ,hZΩ,l,hamp,hzero,α,hα,hper,hvel,τ,hturn,hlarge⟩ := hloop Λ
  refine ⟨Z,hTZ,e₁,e₂,h₁.mono hZΩ,h₂.mono hZΩ,
    (fun j hj => hframe j (hZΩ hj)),l,hamp,hzero,α,hα,hper,hvel,?_⟩
  have hKZ : CollarVelocity.jetSection F '' K ⊆ Z := (image_mono hKT).trans hTZ
  let W : Set Base := CollarVelocity.jetSection F ⁻¹' Z
  have hσ := CollarVelocity.jetSection_smooth hF
  have hW : IsOpen W := Z.isOpen.preimage hσ.continuous
  have hKW : K ⊆ W := fun x hx => hKZ (mem_image_of_mem _ hx)
  have hα' : ContDiffOn ℝ ∞ (fun z : Base × ℝ => α (CollarVelocity.jetSection F z.1,z.2))
      (W ×ˢ univ) :=
    hα.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hz => ⟨hz.1,hz.2⟩)
  have hturn' := closed_interval_turns hW hKW hα'
    (fun x hx => hper (CollarVelocity.jetSection F x) hx) hturn hlarge
  intro x hx t ht
  obtain ⟨hreg,hlo,hhi,hd,hN⟩ := hprofile Z hKZ hZΩ α hα x hx t
  refine ⟨hreg,hlo,hhi,hd,?_⟩
  intro hz
  apply hN
  apply hturn' x hx t ht
  exact (surfaceCircularProfile_turn_iff hΩ hframe α
    (hKΩ (mem_image_of_mem _ hx)) t).mp hz

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
