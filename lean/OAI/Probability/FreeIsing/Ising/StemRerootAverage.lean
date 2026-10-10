import OAI.Probability.FreeIsing.Ising.OrientedPathWeights
import OAI.Probability.FreeIsing.Trees.StemRerootAverage

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def orderedEdgeFactor (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (u v : TreeVertex d) (x : Paths d) : ℝ :=
  responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (if inward then u else v) (if inward then v else u) x) ^ 2

theorem orderedEdgeFactor_mem_Icc (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (u v : TreeVertex d) (x : Paths d) :
    0 ≤ orderedEdgeFactor hb t inward u v x ∧ orderedEdgeFactor hb t inward u v x ≤ 1 := by
  unfold orderedEdgeFactor
  exact ⟨sq_nonneg _, pow_le_one₀
    (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
    (responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)⟩

theorem rootEdgeProduct_orderedEdgeFactor (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (x : Paths d) :
    rootEdgeProduct (fun u w => orderedEdgeFactor hb t inward u w x) v =
      attenuation hb t inward v x ^ 2 := by
  cases inward <;> simp only [rootEdgeProduct, orderedEdgeFactor, attenuation,
    edge, Bool.false_eq_true, ↓reduceIte, Finset.prod_pow]

omit [IsProbabilityMeasure μ] in
theorem orderedEdgeFactor_relabel_ae [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (g : TreeAut d) (u v : TreeVertex d) :
    (fun x => orderedEdgeFactor hb t inward u v (relabel g x)) =ᵐ[observationLaw μ]
      orderedEdgeFactor hb t inward (g.toEquiv.symm u) (g.toEquiv.symm v) := by
  cases inward
  · exact (cavityObservable_relabel_ae hμ hb g t v u).fun_comp
      (fun y => responseAttenuation (Real.tanh beta) y ^ 2)
  · exact (cavityObservable_relabel_ae hμ hb g t u v).fun_comp
      (fun y => responseAttenuation (Real.tanh beta) y ^ 2)

theorem extensionAverage_le_restricted_average_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) :
    ∀ᵐ x ∂observationLaw μ, extensionAverage hb t inward stem (k + 1 + L) x ≤
      (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
        attenuation hb t inward v.1 (relabel (stripPrefixAut stem) x) ^ 2) /
        ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ) := by
  have hall : ∀ᵐ x ∂observationLaw μ, ∀ u v : TreeVertex d,
      orderedEdgeFactor hb t inward u v (relabel (stripPrefixAut stem) x) =
        orderedEdgeFactor hb t inward ((stripPrefixAut stem).toEquiv.symm u)
          ((stripPrefixAut stem).toEquiv.symm v) x :=
    ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun v =>
      orderedEdgeFactor_relabel_ae hμ hb t inward (stripPrefixAut stem) u v))
  filter_upwards [hall] with x hx
  have h := average_rootEdgeProduct_endpoint_le_rerooted stem hstem k L
    (fun u v => orderedEdgeFactor hb t inward u v x)
    (fun u v => orderedEdgeFactor_mem_Icc hb t inward u v x)
  have hfactor : (fun u v => orderedEdgeFactor hb t inward
      ((stripPrefixAut stem).toEquiv.symm u) ((stripPrefixAut stem).toEquiv.symm v) x) =
      (fun u v => orderedEdgeFactor hb t inward u v (relabel (stripPrefixAut stem) x)) :=
    funext (fun u => funext (fun v => (hx u v).symm))
  rw [hfactor] at h
  simp_rw [rootEdgeProduct_orderedEdgeFactor] at h
  simpa only [extensionAverage, WeightedOrbitAverage.average, div_eq_mul_inv, mul_comm] using h

theorem measure_extensionAverage_gt_le_restricted_average_ge
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) (τ : ℝ) :
    (observationLaw μ) {x | τ < extensionAverage hb t inward stem (k + 1 + L) x} ≤
      (observationLaw μ) {x | τ ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
          attenuation hb t inward v.1 x ^ 2) /
          ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ)} := by
  let F : Paths d → ℝ := fun x =>
    (∑ v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L,
      attenuation hb t inward v.1 x ^ 2) /
      ((cutDescendants (avoidingTreeCut (stemForbidden stem) k) L).card : ℝ)
  have hF : Measurable F :=
    (Finset.measurable_fun_sum _ (fun v _ =>
      (measurable_attenuation hb t inward v.1).pow_const 2)).div_const _
  have hp := measurePreserving_observationLaw_relabel hμ (stripPrefixAut stem)
  calc
    _ ≤ (observationLaw μ) {x | τ ≤ F (relabel (stripPrefixAut stem) x)} := by
      apply measure_mono_ae
      filter_upwards [extensionAverage_le_restricted_average_relabel hμ hb t inward
        stem hstem k L] with x hx
      intro h
      exact h.le.trans hx
    _ = _ := hp.measure_preimage (measurableSet_le measurable_const hF).nullMeasurableSet

end Problem367.IsingOrientedPath

end

end OAI
