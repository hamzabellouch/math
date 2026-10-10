import OAI.Analysis.FiniteFactor.CrossedProduct.OperatorField
import OAI.Analysis.FiniteFactor.Matrix.Action

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Coordinate measurability suffices for strong measurability in l2(Z). -/
theorem fiberCoordinates_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (f : X → SourceFiberHilbert) (hf : ∀ n : ℤ, Measurable (fun x => f x n)) :
    StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, lp.single 2 n (f x n))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => (lp.single 2 n (f x n) : SourceFiberHilbert)) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hf n).stronglyMeasurable
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (f x)

/-- Every basis column of the actual field is a strongly measurable l2 vector. -/
theorem sourceOperatorField_basis_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (n : ℤ) :
    StronglyMeasurable (fun x => sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
  fiberCoordinates_stronglyMeasurable _ (fun k => sourceOperatorField_entry_measurable H k n)

theorem sourceOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) : StronglyMeasurable (fun x => sourceOperatorField H x v) := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ)))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
      (sourceOperatorField_basis_stronglyMeasurable H n).const_smul (v n)
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (sourceOperatorField H x) v

/-- Fubini puts almost every actual L2 section in l2(Z). -/
theorem source_fiber_memℓp (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, Memℓp (fun n : ℤ => f (x,n)) 2 := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  apply memℓp_gen
  have hs := integrable_count_iff.mp hx
  simpa only [norm_pow, norm_norm, ENNReal.toReal_ofNat, Real.rpow_two] using hs

/-- A fiber vector with an irrelevant zero value on the exceptional null set. -/
def sourceFiberVector (f : SourceHilbert SourceCoordinate) (x : SourceCoordinate → ℝ) :
    SourceFiberHilbert := by
  classical
  exact if h : Memℓp (fun n : ℤ => f (x,n)) 2 then ⟨fun n => f (x,n), h⟩ else 0

theorem sourceFiberVector_coe (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, sourceFiberVector f x n = f (x,n) := by
  filter_upwards [source_fiber_memℓp f] with x hx n
  simp [sourceFiberVector, hx]

/-- The constructed field acts as the original operator on every source L2
vector. Neither decomposability nor a replacement representation is assumed. -/
theorem sourceOperatorField_represents (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberVector (H f) x = sourceOperatorField H x (sourceFiberVector f x) := by
  have ha : ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
    rw [ae_all_iff]
    exact sourceMatrix_action_tsum θ hH f
  filter_upwards [sourceFiberVector_coe f, sourceFiberVector_coe (H f),
    sourceOperatorField_entries_ae θ hH, ha] with x hf hHf he ha
  apply Subtype.ext
  funext k
  rw [hHf, fiberOperator_action]
  simp_rw [he, hf]
  exact ha k

end
end FiniteFactor

end OAI
