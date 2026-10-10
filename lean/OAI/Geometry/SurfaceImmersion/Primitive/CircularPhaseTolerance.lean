import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseDependence

namespace OAI

/-! One compact-frame constant controls the phase perturbation before
any independent choices or cycle count. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem circularPhase_frame_bound : ∃ D : ℝ, 1 ≤ D ∧
    ∀ i j p, p ∈ tsupport (B.weight j) → ∀ (ell ell₀ : Base) (L : ℝ),
      ‖B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
        B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p)‖ ≤
        D*‖ell-ell₀‖ := by
  choose Dx hDx hx using fun i => B.covectorFrame_bound (B.circularPhase i (1,0) 0)
    (B.circularPhase_smooth i (1,0) 0)
  choose Dy hDy hy using fun i => B.covectorFrame_bound (B.circularPhase i (0,1) 0)
    (B.circularPhase_smooth i (0,1) 0)
  let D := 1+∑ i, (Dx i+Dy i)
  have hD : 1 ≤ D := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => add_nonneg (zero_le_one.trans (hDx i))
      (zero_le_one.trans (hDy i)))
    dsimp only [D]; linarith
  refine ⟨D,hD,?_⟩
  intro i j p hp ell ell₀ L
  have he : B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p) =
      (ell.1-ell₀.1) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
      (ell.2-ell₀.2) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) := by
    unfold covectorFrame
    erw [← ContinuousLinearMap.sub_comp,B.circularPhase_mfderiv_sub]
    erw [ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp]
  rw [he]
  have h1 : |ell.1-ell₀.1| ≤ ‖ell-ell₀‖ := by simpa only [Prod.fst_sub,Real.norm_eq_abs] using norm_fst_le (ell-ell₀)
  have h2 : |ell.2-ell₀.2| ≤ ‖ell-ell₀‖ := by simpa only [Prod.snd_sub,Real.norm_eq_abs] using norm_snd_le (ell-ell₀)
  have hxy : Dx i+Dy i ≤ D := by
    have := Finset.single_le_sum (fun i _ => add_nonneg (zero_le_one.trans (hDx i))
      (zero_le_one.trans (hDy i))) (Finset.mem_univ i)
    dsimp only [D]; linarith
  calc
    _ ≤ ‖(ell.1-ell₀.1) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)‖+
        ‖(ell.2-ell₀.2) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p)‖ := norm_add_le _ _
    _ ≤ ‖ell-ell₀‖*Dx i+‖ell-ell₀‖*Dy i := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul h1 (hx i j p hp) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul h2 (hy i j p hp) (norm_nonneg _) (norm_nonneg _))
    _ = (Dx i+Dy i)*‖ell-ell₀‖ := by ring
    _ ≤ D*‖ell-ell₀‖ := mul_le_mul_of_nonneg_right hxy (norm_nonneg _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
