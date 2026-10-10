import OAI.Geometry.RCD.Harmonic.FirstOrderCompactRepresentative

namespace OAI

/-! # One actual regular family extending all original first-order coordinates -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_regular_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    ∃ (U : Fin n → compactLaplacianCore μ Q univ) (d : Fin n → Lp ℝ 2 μ)
      (V : Fin n → C(X,ℝ)) (L A : Fin n → ℝ≥0),
      (∀ i, IsWeakLaplacian μ Q (U i).val (d i)) ∧
      (∀ i, LipschitzWith (L i) (V i)) ∧ (∀ i, HasCompactSupport (V i)) ∧
      (∀ i, SobolevSpace.toLp μ Q (U i).val =ᵐ[μ] V i) ∧
      (∀ i x, |V i x|≤A i) ∧
      (∀ i, SobolevSpace.toLp μ Q (U i).val =ᵐ[μ.restrict (ball p (6*r))] SobolevSpace.toLp μ Q (u i)) ∧
      (∀ i, d i =ᵐ[μ.restrict (ball p (6*r))] fun _ => 0) ∧
      (∀ i, EqOn (V i) (fun x => v x i) (ball p (6*r))) ∧
      (∀ i, ∀ᵐ x ∂μ.restrict (ball p (6*r)), localGamma μ Q (U i).val (U i).val x≤4) := by
  intro μ Q
  let := hX.openPos K n
  let ℓ : ℝ≥0 := ⟨1+ε,by linarith⟩
  choose U d hd hrep hd0 using fun i => hX.local_poisson_regular_extension hn (u i) 0
    (show 0 < 6*r by linarith) (show 2*(6*r)<16*r by linarith)
    ((isConstantLaplacianOn_zero_iff μ Q _ _).mpr (hs.harmonic i)) ℓ (hs.gradient i)
  choose W L _A hW hWc hWr _hA using fun i => regular_core_representative μ Q (U i)
  have hsub : ball p (6*r)⊆ball p (16*r) := ball_subset_ball (by linarith)
  have heq (i : Fin n) : EqOn (W i) (fun x => v x i) (ball p (6*r)) := by
    have he : W i =ᵐ[μ.restrict (ball p (6*r))] fun x => v x i :=
      (Filter.EventuallyEq.symm (ae_restrict_of_ae (hWr i))).trans
        ((hrep i).trans (ae_restrict_of_ae_restrict_of_subset hsub (hs.representative i)))
    exact Measure.eqOn_open_of_ae_eq he isOpen_ball (hW i).continuous.continuousOn
      (((EuclideanSpace.proj i).continuous.comp_continuousOn hs.continuous).mono hsub)
  choose B hB using fun i => (hWc i).exists_bound_of_continuous (hW i).continuous
  let A (i : Fin n) : ℝ≥0 := ⟨max (B i) 0,le_max_right _ _⟩
  have hA' (i : Fin n) (x : X) : |W i x|≤A i :=
    (show |W i x|≤B i by simpa only [Real.norm_eq_abs] using hB i x).trans (le_max_left _ _)
  refine ⟨U,d,fun i => ⟨W i,(hW i).continuous⟩,L,A,hd,hW,hWc,hWr,hA',hrep,hd0,heq,?_⟩
  intro i
  have he := localGamma_pair_congr_ae μ Q (hrep i) (hrep i)
  filter_upwards [he,ae_restrict_of_ae_restrict_of_subset hsub (hs.gradient i)] with x he hg
  rw [he]
  change localGamma μ Q (u i) (u i) x≤(1+ε)^2 at hg
  nlinarith

end RegularPointCoordinates

end

end OAI
