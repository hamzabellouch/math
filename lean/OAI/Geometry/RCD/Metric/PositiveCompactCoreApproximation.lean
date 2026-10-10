import OAI.Geometry.RCD.Coordinates.RegularDirichletCore

namespace OAI

/-! # Positive bounded approximation by the actual compact Laplacian core

Heat regularization followed by the fixed interior cutoff preserves both
positivity and the original amplitude bound. The convergence is in H1.
-/

open Set Filter MeasureTheory Topology
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.positive_compact_core_approximation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)] {Ω : Set X} (hΩ : IsOpen Ω)
    (φ : X → ℝ) {L B : ℝ≥0} (hφ : LipschitzWith L φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) (hφB : ∀ x, |φ x| ≤ B) :
    ∃ u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ k, u k ∈ compactLaplacianCore (hausdorff n X) hX.quadratic Ω) ∧
      (∀ k, ∀ᵐ x ∂hausdorff n X,
        0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x ∧
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B) ∧
      Tendsto u atTop (𝓝 (SobolevSpace.ofLipschitzCompact (hausdorff n X) hX.quadratic hφ hφc)) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let v := SobolevSpace.ofLipschitzCompact μ Q hφ hφc
  have hv : SobolevSpace.toLp μ Q v =ᵐ[μ] φ := SobolevSpace.ofLipschitzCompact_coe μ Q hφ hφc
  have hv0 : 0 ≤ SobolevSpace.toLp μ Q v :=
    (Lp.coeFn_nonneg _).mp (hv.mono fun x hx => hx.symm ▸ hφ0 x)
  have hvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B :=
    hv.mono fun x hx => hx.symm ▸ hφB x
  obtain ⟨χ,hχ,hχ1⟩ := hX.exists_open_regular_cutoff hn hΩ hφc hφs
  let M := SobolevSpace.cutoffCLM μ Q χ.lipschitz χ.compact χ.abs_le (fun x => (χ.bounds x).1)
  have hMv : M v = v := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.cutoffCLM_coe μ Q χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) v,hv] with x hx hvx
    change SobolevSpace.toLp μ Q (M v) x = SobolevSpace.toLp μ Q v x
    rw [hx,hvx]
    by_cases hz : φ x = 0
    · rw [hz,mul_zero]
    · rw [hχ1 x (subset_tsupport φ hz),one_mul]
  let t := fun k : ℕ => 1/((k:ℝ)+1)
  have ht (k : ℕ) : 0 < t k := by dsimp only [t]; positivity
  let w := fun k => heatSobolev μ Q (t k) (ht k) (SobolevSpace.toLp μ Q v)
  have hwlim : Tendsto w atTop (𝓝 v) := by
    have hh := ((heatH1_continuous μ Q v).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatH1_zero,Function.comp_def,heatH1,dite_eq_left (ht _),
      lt_self_iff_false,dite_false,w,t] using hh
  have hwB (k : ℕ) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (w k) x| ≤ B :=
    heatAt_abs_le_const μ Q (t k) B _ hvB
  refine ⟨fun k => M (w k),?_,?_,?_⟩
  · intro k
    constructor
    · obtain ⟨f,hf,hef⟩ := hX.heat_lipschitz K n hn (SobolevSpace.toLp μ Q v)
        hφ hv.symm B hφB (ht k).le
      obtain ⟨D,hD⟩ := lipschitz_mul_constant_outside_compact χ.lipschitz hf 0
        (by simpa using χ.compact) χ.abs_le
      refine ⟨fun x => χ.weight x*f x,D,hD,χ.compact.mul_right,
        tsupport_mul_subset_left.trans hχ,?_⟩
      filter_upwards [SobolevSpace.cutoffCLM_coe μ Q χ.lipschitz χ.compact χ.abs_le
        (fun x => (χ.bounds x).1) (w k),hef] with x hx hfx
      exact hx.trans (congrArg (fun a => χ.weight x*a) hfx)
    · obtain ⟨d,hd,-⟩ := (heatSobolev_weak_laplacian μ Q (t k) (ht k)
        (SobolevSpace.toLp μ Q v)).cutoff μ Q (w k) χ.sobolev _ χ.laplacian
        χ.weak_laplacian χ.lipschitz χ.compact χ.abs_le (fun x => (χ.bounds x).1)
        χ.representative (hwB k)
      exact ⟨d,hd⟩
  · intro k
    filter_upwards [SobolevSpace.cutoffCLM_coe μ Q χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) (w k),hwB k,
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q (t k) _ hv0)] with x hx hb h0
    rw [hx]
    refine ⟨mul_nonneg (χ.bounds x).1 h0,?_⟩
    rw [abs_mul,abs_of_nonneg (χ.bounds x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (χ.bounds x).2).trans hb
  · simpa only [hMv,Function.comp_def] using M.continuous.tendsto v |>.comp hwlim

end RegularPointCoordinates

end

end OAI
