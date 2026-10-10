import OAI.Analysis.FiniteFactor.Fiber.StrongContinuity
import OAI.Analysis.FiniteFactor.CrossedProduct.FieldRepresentation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- A bounded diagonal on the original l2(Z) fiber. -/
def fiberDiagonal (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => d k * v k,
        (lp.memℓp v).mono' (fun k => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hd k) (norm_nonneg _)).trans_eq (one_mul _))⟩
      map_add' := fun u v => by apply Subtype.ext; funext k; exact mul_add _ _ _
      map_smul' := fun c v => by apply Subtype.ext; funext k; exact mul_left_comm _ _ _ }
    1 (fun v => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num)
      intro k
      change ‖d k * v k‖ ≤ ‖v k‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hd k) (norm_nonneg _)).trans_eq (one_mul _))

@[simp] theorem fiberDiagonal_apply (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1)
    (v : SourceFiberHilbert) (k : ℤ) : fiberDiagonal d hd v k = d k * v k := rfl

theorem fiberDiagonal_norm (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) :
    ‖fiberDiagonal d hd‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem fiberDiagonal_single (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) (n : ℤ) :
    fiberDiagonal d hd (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
  classical
  apply Subtype.ext
  funext k
  change d k * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k =
    d n * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k
  by_cases h : n = k
  · subst k; rfl
  · simp [lp.single_apply, h]

theorem fiberDiagonal_continuousOn {X : Type*} [TopologicalSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1) (Q : Set X)
    (hc : ∀ k, ContinuousOn (fun x => d x k) Q) (v : SourceFiberHilbert) :
    ContinuousOn (fun x => fiberDiagonal (d x) (hd x) v) Q := by
  apply fiberField_continuousOn _ Q 1 (fun x _ => fiberDiagonal_norm _ _) _ v
  intro k
  simp_rw [fiberDiagonal_single]
  exact (hc k).smul continuousOn_const

theorem fiberDiagonal_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1)
    (hm : ∀ k, Measurable (fun x => d x k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun x => fiberDiagonal (d x) (hd x) v) := by
  apply fiberCoordinates_stronglyMeasurable
  intro k
  exact (hm k).mul_const (v k)

/-- Applying a measurable field to a measurable vector uses finite coordinate
approximations, without measurability in the operator norm topology. -/
theorem fiberField_stronglyMeasurable_apply {X : Type*} [MeasurableSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hA : ∀ v, StronglyMeasurable (fun x => A x v))
    (v : X → SourceFiberHilbert) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun x => A x (v x)) := by
  classical
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ k ∈ s, (v x k) • A x (lp.single 2 k (1 : ℂ)))
  · intro s
    have h (k : ℤ) : StronglyMeasurable (fun x => (v x k) • A x (lp.single 2 k (1 : ℂ))) :=
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous.comp_stronglyMeasurable hv).smul
        (hA (lp.single 2 k (1 : ℂ))))
    convert Finset.stronglyMeasurable_sum s (fun k _ => h k) using 1
    ext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (A x) (v x)

end
end FiniteFactor

end OAI
