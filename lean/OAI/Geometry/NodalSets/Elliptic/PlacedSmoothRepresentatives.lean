import OAI.Geometry.NodalSets.Elliptic.FirstJetNonvanishing
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField
import OAI.Geometry.NodalSets.Waves.LocalWaveEnvelopeTransfer
import OAI.Geometry.NodalSets.Waves.PlacedEnvelopeWaves

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma PlacedEnvelopeData.closure_Ω_branch {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.Ω ⊆ seedCoordBranch :=
  d.closure_Ω_patch.trans (subset_closure.trans (d.patch_V.trans d.V_branch))

theorem PlacedEnvelopeData.smooth_representatives {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    ∃ S S0 T0 : Coord → ℝ, ContDiff ℝ ∞ S ∧ ContDiff ℝ ∞ S0 ∧ ContDiff ℝ ∞ T0 ∧
      ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S ∧ S0 =ᶠ[𝓝 x] seedCoordReal ∧
        T0 =ᶠ[𝓝 x] seedCoordImag := by
  obtain ⟨S,hS,_,_,he⟩ := compact_smooth_extension d.compact_closure_Ω
    seedCoordBranch_open d.closure_Ω_branch d.S d.smooth
  obtain ⟨S0,T0,hS0,hT0,_,_,_,_,he0⟩ := seed_log_compact_extensions
    d.compact_closure_Ω d.closure_Ω_branch
  exact ⟨S,S0,T0,hS,hS0,hT0,fun x hx ↦ ⟨he x hx,(he0 x hx).1,(he0 x hx).2⟩⟩

lemma PlacedEnvelopeData.outside_gap {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (x : Coord) (hx : x ∉ d.U) : d.S x-seedCoordReal x ≤ -d.gap := by
  have h := d.outer_gap x (fun h ↦ hx (d.C_U h))
  linarith

lemma seeded_sourceFirstJetSize_germ {f f' v : Coord → ℝ} {x : Coord}
    (h : f =ᶠ[𝓝 x] f') (N : ℝ) :
    sourceFirstJetSize (fun z ↦ f z+v z) N x =
      sourceFirstJetSize (fun z ↦ f' z+v z) N x := by
  have he : (fun z ↦ f z+v z) =ᶠ[𝓝 x] (fun z ↦ f' z+v z) :=
    h.mono (fun z hz ↦ congrArg (· + v z) hz)
  simp only [sourceFirstJetSize,he.eq_of_nhds,he.fderiv_eq]

end
end Yau.Target

end OAI
