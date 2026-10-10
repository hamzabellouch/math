import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.IntrinsicSeedPatch

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

def seedCoordImag : Coord → ℝ := seedImagChart ∘ seedCoordEquiv

def seedCoordBranch : Set Coord := {x | seedChartAmbient (seedCoordEquiv x) ∈ seedLogDomain}

lemma seedCoordBranch_open : IsOpen seedCoordBranch :=
  seedLogDomain_open.preimage (seedChartAmbient_smooth.continuous.comp seedCoordEquiv.continuous)

lemma seedCoordReal_smoothOn : ContDiffOn ℝ ∞ seedCoordReal seedCoordBranch := by
  intro x hx
  exact ((seedRealChart_smoothAt hx).comp x seedCoordEquiv.contDiff.contDiffAt).contDiffWithinAt

lemma seedCoordImag_smoothOn : ContDiffOn ℝ ∞ seedCoordImag seedCoordBranch := by
  intro x hx
  exact ((seedImagChart_smoothAt hx).comp x seedCoordEquiv.contDiff.contDiffAt).contDiffWithinAt

theorem seed_log_compact_extensions {K : Set Coord} (hK : IsCompact K) (hKB : K ⊆ seedCoordBranch) :
    ∃ S T : Coord → ℝ, ContDiff ℝ ∞ S ∧ ContDiff ℝ ∞ T ∧
      HasCompactSupport S ∧ HasCompactSupport T ∧
      tsupport S ⊆ seedCoordBranch ∧ tsupport T ⊆ seedCoordBranch ∧
      ∀ x ∈ K, S =ᶠ[𝓝 x] seedCoordReal ∧ T =ᶠ[𝓝 x] seedCoordImag := by
  obtain ⟨S,hS,hSc,hSB,hSe⟩ := compact_smooth_extension hK seedCoordBranch_open hKB
    seedCoordReal seedCoordReal_smoothOn
  obtain ⟨T,hT,hTc,hTB,hTe⟩ := compact_smooth_extension hK seedCoordBranch_open hKB
    seedCoordImag seedCoordImag_smoothOn
  exact ⟨S,T,hS,hT,hSc,hTc,hSB,hTB,fun x hx ↦ ⟨hSe x hx,hTe x hx⟩⟩

lemma seed_log_extension_jets (S T : Coord → ℝ) (x : Coord)
    (hS : S =ᶠ[𝓝 x] seedCoordReal) (hT : T =ᶠ[𝓝 x] seedCoordImag) :
    S x = seedCoordReal x ∧ T x = seedCoordImag x ∧
    fderiv ℝ S x = fderiv ℝ seedCoordReal x ∧
    fderiv ℝ T x = fderiv ℝ seedCoordImag x ∧
    fderiv ℝ (fderiv ℝ S) x = fderiv ℝ (fderiv ℝ seedCoordReal) x := by
  exact ⟨hS.eq_of_nhds,hT.eq_of_nhds,hS.fderiv_eq,hT.fderiv_eq,hS.fderiv.fderiv_eq⟩

lemma seed_log_extension_geometry (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S : Coord → ℝ) (x : Coord) (hS : S =ᶠ[𝓝 x] seedCoordReal) :
    metricGradient g S x = metricGradient g seedCoordReal x ∧
    sourceHessian g S x = sourceHessian g seedCoordReal x := by
  constructor
  · simp only [metricGradient,hS.fderiv_eq]
  · simp only [sourceHessian,hS.fderiv_eq,hS.fderiv.fderiv_eq]

end
end Yau.Target

end OAI
