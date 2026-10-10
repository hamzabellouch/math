import OAI.Geometry.RCD.Coordinates.DyadicTransformationReduction

namespace OAI

/-! # The first failing exact normalization retains every preceding frame -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_failing_dyadic_scale {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ η →
      ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) γ u v →
      (∃ t : ℝ, 0 < t ∧ t ≤ R ∧ ¬∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t β
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A) →
      ∃ d : ℕ,
        (¬∃ A : Euclidean n ≃L[ℝ] Euclidean n,
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^d) γ
            (transformedColumn (hausdorff n X) hX.quadratic u A)
            (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
          IsExactMeanNormalization (hausdorff n X) hX.quadratic
            (sobolevColumnMap (hausdorff n X) hX.quadratic u)
            (ball p (R/(2 : ℝ)^d)) measurableSet_ball A) ∧
        ∀ j < d, ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^j) γ
            (transformedColumn (hausdorff n X) hX.quadratic u A)
            (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
          IsExactMeanNormalization (hausdorff n X) hX.quadratic
            (sobolevColumnMap (hausdorff n X) hX.quadratic u)
            (ball p (R/(2 : ℝ)^j)) measurableSet_ball A := by
  classical
  obtain ⟨η,hη,hη1,hall⟩ := hX.dyadic_splitting_implies_all_scales hn β hβ
  refine ⟨η,hη,hη1,?_⟩
  intro γ hγ hγη p R hR hK u v hfirst hbad
  let Good : ℕ → Prop := fun j => ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
    FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^j) γ
      (transformedColumn (hausdorff n X) hX.quadratic u A)
      (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
    IsExactMeanNormalization (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic u)
      (ball p (R/(2 : ℝ)^j)) measurableSet_ball A
  have hex : ∃ j, ¬Good j := by
    by_contra hnot
    have hg : ∀ j, Good j := by simpa only [not_exists,not_not] using hnot
    obtain ⟨t,ht,htR,htbad⟩ := hbad
    apply htbad
    apply hall p R hR hK u v (hfirst.mono_error _ _ hγ hγη)
    · intro j
      obtain ⟨A,hA,_⟩ := hg j
      exact ⟨A,hA.mono_error _ _ hγ hγη⟩
    · exact ht
    · exact htR
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  intro j hj
  exact not_not.mp (Nat.find_min hex hj)

end RegularPointCoordinates

end

end OAI
