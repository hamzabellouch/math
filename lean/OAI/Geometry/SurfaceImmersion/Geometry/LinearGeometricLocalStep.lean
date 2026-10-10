import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearPerturbedMeanFamily
import OAI.Geometry.SurfaceImmersion.Geometry.UniformLinearQuadraticSolvers
import OAI.Geometry.SurfaceImmersion.Primitive.LinearPhaseDerivativeProfiles
import OAI.Geometry.SurfaceImmersion.Correction.LinearMeanReconstruction
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseTwoJetBounds
import OAI.Geometry.SurfaceImmersion.Geometry.UniformPerturbedLocalStep

namespace OAI

/-! A local increment constructed from fixed geometric phase neighborhoods.
The actual free and quadratic solvers are constructed inside the proof. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry FiniteMean

/-- Compactly controlled geometry for one fixed linear phase. -/
structure LinearPhaseNeighborhood (F : Base → Space) (ξ : SmallModes.Base)
    (S : Compacts Base) where
  nonzero : ξ ≠ 0
  Ω : Set SmallModes.Base
  U : Set SmallModes.Base
  K : Set SmallModes.Base
  openΩ : IsOpen Ω
  openU : IsOpen U
  compactK : IsCompact K
  subsetK : U ⊆ K
  subsetΩ : K ⊆ Ω
  supportU : (modeSupport S : Set SmallModes.Base) ⊆ U
  immersion : ∀ x ∈ Ω, Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x)
  good : ∀ x ∈ Ω, Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) ξ

def LinearPhaseNeighborhood.chart {F : Base → Space} {ξ : SmallModes.Base}
    {S : Compacts Base} (g : LinearPhaseNeighborhood F ξ S) :=
  linearPhaseChart ξ g.nonzero g.U g.openU

theorem linear_geometric_local_step {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {U₀ D : Set Base} (hU₀ : IsOpen U₀) (hD : IsOpen D) (hDU : D ⊆ U₀)
    (K₀ : Compacts Base) (hU₀K : U₀ ⊆ K₀)
    (Q : PhaseBasis) (w : Fin 3 → ℝ) (hw : ∀ j, w j ≠ 0)
    (S : Fin 3 → Compacts Base)
    (g : ∀ j, LinearPhaseNeighborhood F (w j • Q.ξ j) (S j))
    (ξq : QuadraticLabel (Fin 3) → SmallModes.Base)
    (gq : ∀ l, LinearPhaseNeighborhood F (ξq l) (quadraticCompacts S l))
    (hinto : ∀ j x, x ∈ (g j).U → planeCoordinateIsometry.symm x ∈ U₀)
    (hintoq : ∀ l x, x ∈ (gq l).U → planeCoordinateIsometry.symm x ∈ U₀)
    (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
    (hSqU₀ : ∀ l, (quadraticCompacts S l : Set Base) ⊆ U₀)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (w j • Q.ξ j))
    (hphaseq : ∀ l, coordinatePhase (quadraticFamilyPhase φ l) = phaseLinear (ξq l))
    (ψ : ∀ j, SupportedField (F := ℝ) (chartSupport (g j).chart (modeSupport (S j)) (g j).supportU))
    (χ : SmallModes.Base → ℝ)
    (htransport : ∀ j x, x ∈ (g j).U → ψ j ((g j).chart x) = χ x / w j)
    (hsupport : ∀ j, tsupport χ ⊆ (g j).U)
    (hχ : ∀ x ∈ planeCoordinateIsometry.symm ⁻¹' D, χ x = 1)
    {r r₀ ρ R : ℝ} (hρ : 0 < ρ) (hgap : r₀ < r)
    (reference : SmallModes.Base → Tensor)
    (hmargin : ∀ j x, x ∈ (g j).U →
      ρ + ‖Q.Q j‖ * r ≤ Q.Q j (reference x) ∧
      Q.Q j (reference x) ≤ R - ‖Q.Q j‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (Pjet C : ℕ → ℝ),
      (∀ m, 0 ≤ Pjet m) → (∀ m, 1 ≤ C m) → ∀ q : ℕ,
      ∃ ν η₀ : ℝ, 0 < ν ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∃ Sb Eb : ℕ → ℝ, (∀ m, 0 ≤ Sb m) ∧ (∀ m, 0 ≤ Eb m) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j (Pjet m/(s : ℝ)^(j-2)) G) →
      ∀ (H : SmallModes.Base → Tensor), ContDiff ℝ ∞ H →
      (∀ x, ‖H x-reference x‖ ≤ r₀) →
      (∀ m, WeightedBound univ s m (C m) H) →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      0 < δ → δ ≤ τ → δ/τ ≤ ν → τ/s+ε/τ^tensorLoss P ≤ η₀ →
      ∃ W : RField 4, ContDiff ℝ ∞ W ∧
        tsupport W ⊆ ⋃ j, (modeSupport (S j) : Set SmallModes.Base) ∧
        (∀ m, WeightedBound univ τ m (Sb m*δ*τ) W) ∧
        (∀ m, WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
          (Eb m*(δ*(τ/s+ε/τ^tensorLoss P)^(q+1)+δ^3/τ))
          (coordinateMetricMap P ε (fun x => G x+W (planeCoordinateIsometry x))-
            coordinateMetricMap P ε G-δ^2 • H)) := by
  classical
  obtain ⟨ρf,hρf,hf⟩ := uniform_linear_perturbed_mean_family_all_profiles P hP hF
    (fun j => (g j).Ω) (fun j => (g j).U) (fun j => (g j).K)
    (fun j => (g j).openΩ) (fun j => (g j).openU) (fun j => (g j).compactK)
    (fun j => (g j).subsetK) (fun j => (g j).subsetΩ)
    (fun j => w j • Q.ξ j) (fun j => (g j).nonzero)
    (fun j => (g j).immersion) (fun j => (g j).good)
    S (fun j => (g j).supportU) hU₀ K₀ hU₀K hSU₀ φ hφ hphase ψ Q.Q hmargin
  obtain ⟨ρq,hρq,hq⟩ := uniform_linear_quadratic_solvers P hP hF φ hφ S
    (fun l => (gq l).Ω) (fun l => (gq l).U) (fun l => (gq l).K)
    (fun l => (gq l).openΩ) (fun l => (gq l).openU) (fun l => (gq l).compactK)
    (fun l => (gq l).subsetK) (fun l => (gq l).subsetΩ) ξq
    (fun l => (gq l).nonzero) (fun l => (gq l).immersion) (fun l => (gq l).good)
    (fun l => (gq l).supportU) hU₀ K₀ hU₀K hSqU₀ hphaseq
  refine ⟨min ρf ρq,lt_min hρf hρq,?_⟩
  intro Pjet C hPjet hC q
  obtain ⟨Hf,hHf,hjetf⟩ := linear_phase_twoJet_profiles
    (fun j => w j • Q.ξ j) (fun j => (g j).nonzero)
    (fun j => (g j).U) (fun j => (g j).openU)
    (fun j => ⟨(g j).K,(g j).compactK⟩) (fun j => (g j).subsetK)
    hU₀ hinto Pjet hPjet
  obtain ⟨Hq,hHq,hjetq⟩ := linear_phase_twoJet_profiles
    ξq (fun l => (gq l).nonzero)
    (fun l => (gq l).U) (fun l => (gq l).openU)
    (fun l => ⟨(gq l).K,(gq l).compactK⟩) (fun l => (gq l).subsetK)
    hU₀ hintoq Pjet hPjet
  obtain ⟨p,_,_,_,hp⟩ := hf Hf Pjet hHf hPjet
  obtain ⟨Cq,Dq,Jq,Iq,hCq,_,hJq,hIq,hcq⟩ := hq Hq Pjet hHq hPjet
  obtain ⟨Qjet,hQjet,hQrange⟩ := bounded_lowJet_range hU₀ K₀ hU₀K (hPjet 0)
  choose B₀ hB₀ hb using fun m => bounded_lowJet_prefix hU₀ K₀ hU₀K (m+tensorOrder P)
  let B : ℕ → ℝ := fun m => B₀ m+Pjet (m+tensorOrder P)
  have hB (m : ℕ) : 1 ≤ B m := (hB₀ m).trans (le_add_of_nonneg_right (hPjet _))
  obtain ⟨Fp,Mp,hFp,hMp,hφb,hφm⟩ := linear_phase_derivative_profiles φ
    (fun j => w j • Q.ξ j) hphase
  obtain ⟨ν,η₀,hν,hη₀,hη₁,Sb,Eb,hSb,hEb,hstep⟩ :=
    uniform_perturbed_local_step hU₀ hD hDU hQjet P hP p hρ hgap q
      B Fp Mp C hB (fun m => zero_le_one.trans (hFp m))
      (fun m => zero_le_one.trans (hMp m)) hC Cq Dq Jq Iq hCq hJq hIq
  refine ⟨ν,η₀,hν,hη₀,hη₁,Sb,Eb,hSb,hEb,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hpref H hH hHref hHb
    τ ε δ hτ hτs hε hε1 hδ hδτ hδν hsmall
  obtain ⟨d,hfit,heG,heφ,heS,heChart,heCut,heForm⟩ := hp G hG C₀ hC₀
    (hCρ.trans_le (min_le_left _ _)) hclose s hs hs1 (hjetf G hG s hs hs1 hpref) hpref τ ε r le_rfl hτ hτs hε hε1
  obtain ⟨cq,hcqC,hcqD,hcqJ,hcqI⟩ := hcq G hG C₀ hC₀
    (hCρ.trans_le (min_le_right _ _)) hclose s hs hs1 (fun l m => hjetq G hG s hs hs1 hpref l (m+1)) hpref τ ε hτ hτs hε hε1
  have hleading := linear_mean_reconstruction_on d hρ Q w hw χ (fun j => ψ j)
    (by simpa only [heφ] using hphase) heCut
    (by simpa only [heChart,LinearPhaseNeighborhood.chart,linearPhaseChart_source] using htransport) heForm
    (by simpa only [heChart,LinearPhaseNeighborhood.chart,linearPhaseChart_source] using hsupport)
    (planeCoordinateIsometry.symm ⁻¹' D) hχ
  subst G
  subst φ
  subst S
  apply hstep s hs hs1 reference H hH hHref hHb d.smoothG d.phase hφ d.support
    ε τ δ hτ hτs hε hε1 hδ hδτ hδν hsmall
  · apply hQrange d.G d.smoothG
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref 0 2 (by omega)
  · intro m
    exact hb m d.G d.smoothG s (Pjet (m+tensorOrder P)) hs hs1 (hPjet _) (hpref _)
  · intro j m v
    exact hφb U₀ s m (tensorOrder P) j v
  · exact fun j m v hv => hφm s m j v hv
  · exact hSqU₀
  · exact hfit
  · exact hleading
  · exact hcqC
  · exact hcqD
  · exact hcqJ
  · exact hcqI

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
