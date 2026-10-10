import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.SurfaceImmersion.Geometry.JetVariationSupport
import OAI.Geometry.SurfaceImmersion.Geometry.JetVariationLinearity
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialVariation
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

/-! The actual polynomial linearization as an operator on smooth fields of
fixed compact support, with its finite derivative-loss seminorm estimate. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

variable {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}

def variationLM (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ) :
    SupportedField (F := Space) K →ₗ[ℝ] SupportedField (F := ℝ) K where
  toFun H := ContDiffMapSupportedIn.of_support_subset
    (e.variation_smooth_global hO hU K.isCompact.isClosed hKU he hG H.contDiff hQ H.tsupport_subset t)
    (subset_closure.trans ((e.tsupport_variation G H t).trans H.tsupport_subset))
  map_add' H J := by
    apply DFunLike.ext
    intro p
    exact e.variation_add G H.contDiff J.contDiff (p, t)
  map_smul' c H := by
    apply DFunLike.ext
    intro p
    exact e.variation_smul G H.contDiff c (p, t)

lemma variationLM_apply (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ)
    (H : SupportedField (F := Space) K) (p : Base) :
    variationLM hO hU he hG hQ K hKU t H p = e.variation G H (p, t) := rfl

/-- A fixed finite derivative loss suffices at every output order. The
operator acts on genuine supported smooth functions, not a Banach completion. -/
theorem variationLM_bound {Q : Set LowJet} (hO : IsOpen O) (hU : IsOpen U)
    (hQcompact : IsCompact Q) (hQO : Q ⊆ O) (he : e.SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      WeightedBound U s (m + e.order) B (lowJet G) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Space) K,
        supportedWeightedSeminorm K s m
          (variationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU t H) ≤
        D / (s : ℝ) ^ (e.loss + e.order) * supportedWeightedSeminorm K s (m + e.order) H := by
  obtain ⟨D, hD, hd⟩ := e.compact_variation_bound hU hO hQcompact hQO he m B hB
  refine ⟨D, hD, ?_⟩
  intro G hG hGQ s hs hs1 hGb t ht H
  let C := supportedWeightedSeminorm K s (m + e.order) H
  have hC : 0 ≤ C := apply_nonneg _ _
  have hHb := (weightedBound_of_supportedSeminorm s (m + e.order) H).restrict_open hU
  have hv := hd G H s C hs hs1 hC hG H.contDiff hGQ hGb hHb t ht
  have hglobal := hv.extend_support hU
    ((e.tsupport_variation G H t).trans (H.tsupport_subset.trans hKU)) (by positivity)
  have hresult := supportedSeminorm_le_of_weightedBound hs
    (show 0 ≤ D * C / (s : ℝ) ^ (e.loss + e.order) by positivity)
    (variationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU t H) hglobal
  convert hresult using 1
  dsimp only [C]
  ring

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
