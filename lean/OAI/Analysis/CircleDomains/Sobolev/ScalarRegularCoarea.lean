import OAI.Analysis.CircleDomains.Sobolev.ScalarRegularCoordinates
import OAI.Analysis.CircleDomains.Sobolev.WeightedCoareaFiniteUnion

namespace OAI

/-! Exact coarea on every bounded Borel set of noncritical differentiability
points of a continuous planar scalar function. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma scalar_regular_weighted_coarea {f : ℂ → ℝ} (hf : Continuous f)
    {S : Set ℂ} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    (hd : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hn : ∀ z ∈ S, fderiv ℝ f z ≠ 0)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : WeightedScalarCoareaIdentity S f q := by
  let A := S ∩ {z | fderiv ℝ f z 1 ≠ 0}
  let B := S ∩ {z | fderiv ℝ f z 1 = 0}
  have hz : MeasurableSet {z | fderiv ℝ f z 1 = 0} :=
    measurableSet_eq_fun (measurable_fderiv_apply_const ℝ f 1) measurable_const
  have hA : MeasurableSet A := hS.inter hz.compl
  have hB : MeasurableSet B := hS.inter hz
  have hneI : ∀ z ∈ B, fderiv ℝ f z Complex.I ≠ 0 := by
    intro z hz hI
    apply hn z hz.1
    ext w
    rw [complexCovector_apply, hz.2, hI]
    simp
  have hAc := scalar_regular_im_weighted_coarea hf hA (hb.subset inter_subset_left)
    (fun z hz => hd z hz.1) (fun _ hz => hz.2) hq
  have hBc := scalar_regular_re_weighted_coarea hf hB (hb.subset inter_subset_left)
    (fun z hz => hd z hz.1) hneI hq
  have hdAB : Disjoint A B := by
    apply disjoint_left.mpr
    exact fun z ha hb => ha.2 hb.2
  have he : A ∪ B = S := by ext z; simp [A, B]; tauto
  have hh := weighted_coarea_union hf hB hdAB q hAc hBc
  rwa [he] at hh

end CircleDomainRigidity

end

end OAI
