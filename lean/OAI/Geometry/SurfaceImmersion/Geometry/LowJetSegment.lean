import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Compact low-jet margins and uniform bounds along the actual Taylor
segment, obtained from the second derivatives of the displacement. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_segment_bound {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {s B C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hGb : WeightedBound U s m B (lowJet G))
    (hHb : WeightedBound U s (m + 2) C H) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (B + C / s ^ 2) (lowJet (fun p => G p + t • H p)) := by
  have hv := weighted_variationLowJet hU hH hs hs1 hC m hHb
  have hscl := hv.const_smul hU.uniqueDiffOn (variationLowJet_smooth hH).contDiffOn t
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hb := hscl.mono_const (mul_le_of_le_one_left (div_nonneg hC (sq_nonneg s)) ht1)
  have ha := hGb.add hU.uniqueDiffOn hs.le (lowJet_smooth hG).contDiffOn
    ((variationLowJet_smooth hH).const_smul t).contDiffOn hb
  exact ha.congr (fun p _ => lowJet_affine hG hH t p)

lemma lowJet_segment_dist {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {s C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hHb : WeightedBound U s 2 C H) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    {p : Base} (hp : p ∈ U) :
    dist (lowJet (fun q => G q + t • H q) p) (lowJet G p) ≤ C / s ^ 2 := by
  have hv := weighted_variationLowJet hU hH hs hs1 hC 0 hHb
  rw [lowJet_affine hG hH t p, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans (hv.norm_le hp)

theorem exists_lowJet_segment_margin {Q O : Set LowJet}
    (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q ⊆ Q' ∧ Q' ⊆ O ∧
      ∀ {U : Set Base}, IsOpen U → ∀ {G H : Base → Space},
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → Set.MapsTo (lowJet G) U Q →
      ∀ {s C : ℝ}, 0 < s → s ≤ 1 → 0 ≤ C → C / s ^ 2 ≤ ρ →
      WeightedBound U s 2 C H → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q' := by
  obtain ⟨ρ,hρ,hsub⟩ := hQ.exists_cthickening_subset_open hO hQO
  refine ⟨ρ,Metric.cthickening ρ Q,hρ,hQ.cthickening,Metric.self_subset_cthickening Q,hsub,?_⟩
  intro U hU G H hG hH hGQ s C hs hs1 hC hsmall hHb t ht p hp
  exact Metric.mem_cthickening_of_dist_le _ (lowJet G p) ρ Q (hGQ hp)
    ((lowJet_segment_dist hU hG hH hs hs1 hC hHb ht hp).trans hsmall)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
