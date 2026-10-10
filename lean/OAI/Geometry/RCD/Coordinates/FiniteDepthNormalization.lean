import OAI.Geometry.RCD.Coordinates.ComparableRadiusSplitting

namespace OAI

/-! # Fixed finite depths cannot contain a failing normalization scale -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.finite_depth_splitting {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) δ u v →
      ∀ t : ℝ, R/(2 : ℝ)^N ≤ t → t ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t β
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A := by
  obtain ⟨δ,hδ,hgood⟩ := hX.interior_radius_splitting hn (1/(2 : ℝ)^N)
    (by positivity) ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) β hβ
  refine ⟨δ,hδ,?_⟩
  intro p R hR hK u v hfirst t ht htR
  apply hgood p R hR hK u v hfirst t _ htR
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using ht

theorem NoncollapsedRCD.failing_depth_tends_to_infinity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β) (p : ℕ → X) (R ε : ℕ → ℝ)
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n) (d : ℕ → ℕ)
    (hR : ∀ k, 0 < R k) (hK : ∀ k, -1 ≤ K*(2*R k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hfirst : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (2*R k) (ε k) (u k) (v k))
    (hbad : ∀ k, ¬∃ A : Euclidean n ≃L[ℝ] Euclidean n,
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic (p k) (R k/(2 : ℝ)^(d k)) β
        (transformedColumn (hausdorff n X) hX.quadratic (u k) A)
        (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v k x)) ∧
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic (u k))
        (ball (p k) (R k/(2 : ℝ)^(d k))) measurableSet_ball A) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  obtain ⟨δ,hδ,hgood⟩ := hX.finite_depth_splitting hn N β hβ
  filter_upwards [hεlim.eventually (eventually_lt_nhds hδ)] with k hk
  have hlarge : N < d k := by
    by_contra hnot
    have hd : d k ≤ N := le_of_not_gt hnot
    have hlo : R k/(2 : ℝ)^N ≤ R k/(2 : ℝ)^(d k) :=
      div_le_div_of_nonneg_left (hR k).le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hd)
    have hhi : R k/(2 : ℝ)^(d k) ≤ R k :=
      div_le_self (hR k).le (one_le_pow₀ (by norm_num))
    exact hbad k (hgood (p k) (R k) (hR k) (hK k) (u k) (v k)
      ((hfirst k).mono_error (hausdorff n X) hX.quadratic (hε k) hk.le)
      (R k/(2 : ℝ)^(d k)) hlo hhi)
  exact hlarge.le

end RegularPointCoordinates

end

end OAI
