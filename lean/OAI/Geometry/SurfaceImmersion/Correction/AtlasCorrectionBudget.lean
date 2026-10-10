import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveCorrectionSequence
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCorrectionLimit

namespace OAI

/-! The actual correction series retains its finite atlas displacement budget. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_tsum (p : M) (χ : M → ℝ) (U : ℕ → M → Space) :
    localize p χ (fun x => ∑' n, U n x) = fun x => ∑' n, localize p χ (U n) x := by
  funext x
  by_cases hx : x ∈ (chart p).target
  · simp only [localize,indicator_of_mem hx]
    exact (tsum_const_smul'' _).symm
  · simp only [localize,indicator_of_notMem hx,tsum_zero]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Bounds at a fixed finite order pass to the actual sum with the sum of
the bounds, rather than a larger coordinate-transition constant. -/
theorem weightedBound_tsum {U : ℕ → M → Space} {ρ : ℕ → ℝ} {m : ℕ}
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ n, A.WeightedBound 1 m (ρ n) (U n)) :
    A.WeightedBound 1 m (∑' n, ρ n) (fun x => ∑' n, U n x) := by
  intro i
  rw [localize_tsum]
  have hs (n : ℕ) : ContDiff ℝ ∞ (localize (i : M) (A.weight i) (U n)) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hU n)
  have hb (j : ℕ) (hj : j ≤ m) (n : ℕ) (x : JetPolynomial.Base) :
      ‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) (U n)) x‖ ≤ ρ n := by
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using
      hbound n i j hj x (mem_univ x)
  intro j hj x _
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  rw [iteratedFDeriv_tsum_apply (N := (m : ℕ∞))
    (v := fun _ => ρ) (fun n => (hs n).of_le (by simp))
    (fun _ _ => hρ) (fun k n y hk => hb k (by exact_mod_cast hk) n y)
    (by exact_mod_cast hj) x]
  exact tsum_of_norm_bounded hρ.hasSum (fun n => hb j hj n x)

end SmoothingAtlas

namespace PreparedCorrection
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
variable (c : PreparedCorrection d) (hF : ContMDiff planeModel spaceModel ∞ F)
  {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)

/-- Every constructed increment has the zeroth, first, and second derivative
budget, including the stages before the order has increased. -/
lemma increment_c2_bound (seed : c.Stage t 0) (n : ℕ) :
    d.A.WeightedBound 1 2 (c.ρ*correctionScale t n)
      (c.increment hF ht htsmall seed n) :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).small 2
    (by unfold correctionOrder; omega)

/-- The limit remains within the total C² displacement budget of its seed. -/
theorem limit_seed_displacement_bound (seed : c.Stage t 0) :
    d.A.WeightedBound 1 2 (2*c.ρ*t)
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map) := by
  have hsum := (correctionScale_summable ht.le htsmall).1.mul_left c.ρ
  have hb := d.A.weightedBound_tsum (c.increment_smooth hF ht htsmall seed)
    hsum (c.increment_c2_bound hF ht htsmall seed)
  have he : manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map =
      (fun x => ∑' n, c.increment hF ht htsmall seed n x) := by
    funext x
    simp only [Pi.sub_apply,manifoldLimitMap,add_sub_cancel_left]
  rw [he]
  intro i
  apply (hb i).mono_const
  rw [tsum_mul_left]
  calc
    c.ρ*(∑' n, correctionScale t n) ≤ c.ρ*(2*t) :=
      mul_le_mul_of_nonneg_left (correctionScale_tsum_le ht.le htsmall) c.ρ_pos.le
    _ = 2*c.ρ*t := by ring

/-- The initial margin and the convergent correction budget preserve the
same fixed C² neighborhood used to construct the entire sequence. -/
theorem limit_reference_displacement_bound (seed : c.Stage t 0) :
    d.A.WeightedBound 1 2 (c.ρ/4)
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-F) := by
  have hsum := (correctionScale_summable ht.le htsmall).1.mul_left c.ρ
  have hs := (d.A.correction_limit seed.smooth (c.increment_smooth hF ht htsmall seed)
    hsum (c.increment_eventual_bound hF ht htsmall seed) d.outer_locally_one).1
  have hseed : d.A.WeightedBound 1 2 (c.ρ/8) (seed.map-F) := by
    simpa only [stageRadius,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero] using seed.near
  have hb := d.A.weightedBound_add (seed.smooth.sub hF) (hs.sub seed.smooth)
    zero_le_one hseed (c.limit_seed_displacement_bound hF ht htsmall seed)
  have he : manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-F =
      (seed.map-F)+(manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map) := by
    abel
  rw [he]
  intro i
  apply (hb i).mono_const
  have hρ := c.ρ_pos.le
  nlinarith [mul_le_mul_of_nonneg_left htsmall c.ρ_pos.le]

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
