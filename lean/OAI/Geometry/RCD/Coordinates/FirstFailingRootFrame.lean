import OAI.Geometry.RCD.Coordinates.FirstFailingDyadicScale

namespace OAI

/-! # A genuine root frame and all ancestors at a first failing scale -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem dyadic_ancestor_radius (R : ℝ) {d j : ℕ} (hj : j ≤ d) :
    (2 : ℝ)^j*(R/(2 : ℝ)^d) = R/(2 : ℝ)^(d-j) := by
  have hp : (2 : ℝ)^d = (2 : ℝ)^(d-j)*(2 : ℝ)^j := by
    rw [← pow_add,Nat.sub_add_cancel hj]
  rw [hp]
  field_simp

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_failing_root_frame {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ δ →
      ∀ (p : X) (R : ℝ) (d : ℕ), 0 < R → 0 < d → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      (∀ j < d, ∃ S : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^j) γ
          (transformedColumn (hausdorff n X) hX.quadratic u S)
          (fun x => (S : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u)
          (ball p (R/(2 : ℝ)^j)) measurableSet_ball S) →
      ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^d) κ
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u)
          (ball p (R/(2 : ℝ)^d)) measurableSet_ball A ∧
        ∀ j ≤ d, ∃ S : Euclidean n ≃L[ℝ] Euclidean n,
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p
            ((2 : ℝ)^j*(R/(2 : ℝ)^d)) κ
            (transformedColumn (hausdorff n X) hX.quadratic u S)
            (fun x => (S : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
          IsExactMeanNormalization (hausdorff n X) hX.quadratic
            (sobolevColumnMap (hausdorff n X) hX.quadratic u)
            (ball p ((2 : ℝ)^j*(R/(2 : ℝ)^d))) measurableSet_ball S := by
  obtain ⟨η,hη,hstep⟩ := hX.comparable_radius_splitting hn κ hκ
  refine ⟨min η κ,lt_min hη hκ,min_le_right _ _,?_⟩
  intro γ hγ hγδ p R d hR hd hK u v hbefore
  let r := R/(2 : ℝ)^d
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hrK : -1 ≤ K*(2*r)^2 := by
    have hsq : (2*r)^2 ≤ (2*R)^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    by_cases hK0 : 0 ≤ K
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (mul_nonneg hK0 (sq_nonneg _))
    · exact hK.trans (mul_le_mul_of_nonpos_left hsq (le_of_not_ge hK0))
  obtain ⟨S,hS,_⟩ := hbefore (d-1) (by omega)
  have he : 2*r = R/(2 : ℝ)^(d-1) := by
    simpa only [pow_one] using dyadic_ancestor_radius R (d:=d) (j:=1) hd
  rw [← he] at hS
  obtain ⟨B,hB,hBn⟩ := hstep p r hr hrK
    (transformedColumn (hausdorff n X) hX.quadratic u S)
    (fun x => (S : Euclidean n →L[ℝ] Euclidean n).adjoint (v x))
    (hS.mono_error _ _ hγ (hγδ.trans (min_le_left _ _))) r (by linarith) le_rfl
  let A := B.trans S
  have hA := firstOrderSplitting_comp (hausdorff n X) hX.quadratic u S B v p r κ hB
  have hAn := exact_mean_normalization_comp (hausdorff n X) hX.quadratic u S B
    (ball p r) measurableSet_ball hBn
  refine ⟨A,hA,hAn,?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simpa only [pow_zero,one_mul] using (show ∃ S : Euclidean n ≃L[ℝ] Euclidean n,
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p r κ
        (transformedColumn (hausdorff n X) hX.quadratic u S)
        (fun x => (S : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p r) measurableSet_ball S
      from ⟨A,hA,hAn⟩)
  · obtain ⟨T,hT,hTn⟩ := hbefore (d-j) (by omega)
    rw [dyadic_ancestor_radius R hj]
    exact ⟨T,hT.mono_error _ _ hγ (hγδ.trans (min_le_right _ _)),hTn⟩

end RegularPointCoordinates

end

end OAI
