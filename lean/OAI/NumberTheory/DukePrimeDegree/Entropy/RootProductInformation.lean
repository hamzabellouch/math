import OAI.NumberTheory.DukePrimeDegree.Entropy.RootInformationIntegral

namespace OAI

/-!
# Information of products of the actual root leaf measures

Rectangular information of a finite product is the sum of its root
information. Its integral is the coefficient-weighted sum of root
information integrals.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] (d : ℕ)
  (i j : ι → Fin (d + 1)) (hij : ∀ a, i a ≠ j a)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

/-- Rectangular information in the product of the actual normalized root
leaves, at independently prescribed real logarithmic scales. -/
def rootProductInformation (t : ι → ℝ) (x : X (d + 1)) : ℝ :=
  -Real.log ((Measure.pi (fun a => intrinsicRootLeaf (hij a) μ x))
    (Set.pi univ (fun a => ball 0 (Real.exp (-t a))))).toReal

include hA

lemma ae_rootProductInformation_eq_sum (t : ι → ℝ) :
    ∀ᵐ x ∂μ, rootProductInformation d i j hij μ t x =
      ∑ a, rootInformation (hij a) μ (t a) x := by
  have hfree (a : ι) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij a) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx (i a) (j a) (hij a)
  have hs := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_spec (hij a) μ (hfree a))
  have hp := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_ball_pos (hij a) μ (hfree a))
  filter_upwards [hs, hp] with x hx hpx
  let ν : ι → Measure ℝ := fun a => intrinsicRootLeaf (hij a) μ x
  let (a : ι) : IsLocallyFiniteMeasure (ν a) := (hx a).1
  change -Real.log ((Measure.pi ν) (Set.pi univ (fun a => ball 0 (Real.exp (-t a))))).toReal = _
  rw [Measure.pi_pi, ENNReal.toReal_prod, Real.log_prod]
  · simp only [rootInformation, Finset.sum_neg_distrib, ν]
  · intro a _
    exact (ENNReal.toReal_pos (hpx a _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'

lemma integrable_rootProductInformation (t : ι → ℝ) :
    Integrable (rootProductInformation d i j hij μ t) μ := by
  have hi : Integrable (fun x => ∑ a, rootInformation (hij a) μ (t a) x) μ := by
    exact integrable_finsetSum _ fun a _ => integrable_rootInformation d (hij a) μ hA (t a)
  apply hi.congr
  filter_upwards [ae_rootProductInformation_eq_sum d i j hij μ hA t] with x hx
  exact hx.symm

/-- The product leaf information has precisely the coefficient-weighted
mean occurring in the entropy formula. -/
theorem integral_rootProductInformation (t : ι → ℝ) :
    (∫ x, rootProductInformation d i j hij μ t x ∂μ) =
      ∑ a, t a * canonicalRootCoefficient d μ (i a) (j a) := by
  rw [integral_congr_ae (ae_rootProductInformation_eq_sum d i j hij μ hA t),
    integral_finsetSum _ (fun a _ => integrable_rootInformation d (hij a) μ hA (t a))]
  exact Finset.sum_congr rfl fun a _ => integral_rootInformation d (hij a) μ hA (t a)

end DukePrimeDegree

end

end OAI
