import OAI.Geometry.SurfaceImmersion.Correction.OrderwiseCorrectionLimit
import OAI.Geometry.SurfaceImmersion.Atlas.GlobalPhaseGerms

namespace OAI

/-! The actual fixed-atlas correction bounds imply a smooth manifold limit
and convergence of the manifold differentials. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
open ExactCorrection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Every point is seen by at least one genuine partition weight. -/
lemma exists_weight_ne_zero (p : M) : ∃ i : A.centers, A.weight i p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp := A.partition p
  simp only [h,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hp
  norm_num at hp

omit [CompactSpace M] in
/-- Where its outer cutoff is one, the coordinate representative agrees
with the original map, for every map simultaneously. -/
lemma vectorPlaneRead_coordinateChart_of_outer_one (i : A.centers) (V : M → Space)
    {x : M} (hx : x ∈ (chart (i : M)).source) (ho : A.outer i x = 1) :
    V x = A.vectorPlaneRead i V (coordinateChart (i : M) x) := by
  change V x = localize (i : M) (A.outer i) V
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) x)))
  rw [LinearIsometryEquiv.symm_apply_apply,localize_chart _ _ _ hx,ho,one_pow,one_smul]

/-- The global atlas norm can be used directly; the summable bound only has
to hold eventually for each fixed derivative order. -/
theorem correction_limit
    {F : M → Space} {U : ℕ → M → Space} {ρ : ℕ → ℝ}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n))
    (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop, A.WeightedBound 1 m (ρ n) (U n))
    (houter : ∀ i x, x ∈ tsupport (A.weight i) →
      A.outer i =ᶠ[𝓝 x] (fun _ => 1)) :
    ContMDiff planeModel spaceModel ∞ (manifoldLimitMap F U) ∧
      ∀ p, Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p)
        atTop (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
  have hpoint (p : M) : ContMDiffAt planeModel spaceModel ∞ (manifoldLimitMap F U) p ∧
      Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p)
        atTop (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
    obtain ⟨i,hi⟩ := A.exists_weight_ne_zero p
    have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ hi
    have hpS := A.weight_support i hp
    have hpC : p ∈ (coordinateChart (i : M)).source := by
      simpa only [coordinateChart_source,chart_source] using hpS
    have hc := ((coordinateChart_smoothOn (i : M)) p hpC).contMDiffAt
      ((coordinateChart (i : M)).open_source.mem_nhds hpC)
    choose C hC hread using fun m => A.vectorPlaneRead_bound (V := Space) i m
    have hlocal (m : ℕ) : ∀ᶠ n in atTop, ∀ x,
        ‖iteratedFDeriv ℝ m (A.vectorPlaneRead i (U n)) x‖ ≤ C m*ρ n := by
      filter_upwards [hbound m] with n hn x
      have hρn : 0 ≤ ρ n :=
        (norm_nonneg _).trans ((hn i).norm_le (mem_univ (0 : JetPolynomial.Base)))
      have hb := hread m (U n) 1 (ρ n) zero_lt_one le_rfl hρn (hU n) hn
      simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using
        hb m le_rfl x (mem_univ x)
    have heq : ∀ᶠ x in 𝓝 p,
        F x = A.vectorPlaneRead i F (coordinateChart (i : M) x) ∧
        ∀ n, U n x = A.vectorPlaneRead i (U n) (coordinateChart (i : M) x) := by
      filter_upwards [houter i p hp,(chart (i : M)).open_source.mem_nhds hpS] with x ho hx
      exact ⟨A.vectorPlaneRead_coordinateChart_of_outer_one i F hx ho,
        fun n => A.vectorPlaneRead_coordinateChart_of_outer_one i (U n) hx ho⟩
    exact local_coordinate_correction_limit
      (A := fun n => A.vectorPlaneRead i (U n)) (ρ := fun m n => C m*ρ n) p hc
      (A.vectorPlaneRead_smooth i hF) (fun n => A.vectorPlaneRead_smooth i (hU n))
      (fun m => hρ.mul_left (C m)) hlocal heq
  exact ⟨fun p => (hpoint p).1,fun p => (hpoint p).2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
