import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectedJetSequencesNot

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU

theorem exists_firstJet_mul_const_strictFDeriv
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet (g.toHomeomorph p) (c t)) L t₀) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (c t*g)) L' t₀ := by
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    ((c t₀).derivativeAt (g.toHomeomorph p),g.derivativeAt p)).comp t₀
    (hc.snd.prodMk (show HasStrictFDerivAt (fun _ : E => g.derivativeAt p)
      (0 : E →L[ℝ] (Affine n →L[ℂ] Affine n)) t₀ from hasStrictFDerivAt_const _ t₀))
  have hpair := hc.fst.prodMk hB
  have he : (fun t => ambientFirstJet p (c t*g)) =
      (fun t => ((c t).ambientAut (g.toHomeomorph p).val,
        ((c t).derivativeAt (g.toHomeomorph p)).comp (g.derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · exact derivativeAt_mul hU (c t) g p
  rw [he]
  exact ⟨_,hpair⟩

theorem exists_firstJet_const_mul_strictFDeriv
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L t₀) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (g*c t)) L' t₀ := by
  have hy : (c t₀).ambientAut p.val∈U := by
    rw [ambientAut_apply]
    exact ((c t₀).toHomeomorph p).property
  have hA := ((g.ambientAut_analytic hU _ hy).hasStrictFDerivAt).restrictScalars ℝ
  have hD := ((g.ambientAut_analytic hU _ hy).fderiv.hasStrictFDerivAt).restrictScalars ℝ
  have hAv := hA.comp t₀ hc.fst
  have hDv := hD.comp t₀ hc.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ g.ambientAut ((c t₀).ambientAut p.val),(c t₀).derivativeAt p)).comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have he : (fun t => ambientFirstJet p (g*c t)) =
      (fun t => (g.ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (c t) p
  rw [he]
  exact ⟨_,hpair⟩
end Biholomorph
end Release061

end

end OAI
