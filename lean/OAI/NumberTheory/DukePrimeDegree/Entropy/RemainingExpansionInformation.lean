import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductDiagonal
import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalRootTubes

namespace OAI

/-! # The mean normalization in the actual remaining-root covariance -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}

lemma remainingDilationCube_preimage (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) (ell : Fin (d+1) → ℝ) :
    (c.remainingEuclideanCoordinates hf).symm ⁻¹'
        ((c.rootDilation ell 1) ⁻¹' c.cube 1) =
      Set.univ.pi (fun p : ↥(allPositiveRoots (d+1) \ P) =>
        Metric.ball 0 (Real.exp (-(ell p.val.1-ell p.val.2)))) := by
  ext v
  simp only [Set.mem_preimage, c.remainingEuclideanCoordinates_cube hf,
    Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_ball, Real.dist_eq, sub_zero]
  apply forall_congr'
  intro p
  rw [c.remainingEuclideanCoordinates_dilation hf]
  simp only [Homeomorph.apply_symm_apply, mul_one]
  simpa only [neg_zero, Real.exp_zero, zero_add] using
    exp_scaled_abs_lt_iff (ell p.val.1-ell p.val.2) 0 (v p)

/-- Every expanding normalization rectangle has positive finite mass. -/
theorem ae_remainingExpansionMass_pos_ne_top (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ∧
      c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ≠ ∞ := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let hij (p : I) := ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hfree (p : I) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij p) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  have hs := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_spec (hij p) μ (hfree p))
  have hp := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_ball_pos (hij p) μ (hfree p))
  filter_upwards [hs, hp] with x hxs hxp
  let : ∀ p : I, IsLocallyFiniteMeasure (intrinsicRootLeaf (hij p) μ x) :=
    fun p => (hxs p).1
  rw [c.remainingTimeProduct_eq_map hP hf μ x,
    Measure.map_apply (c.remainingEuclideanCoordinates hf).symm.measurable
      ((c.cube_open 1).preimage (c.rootDilation ell 1).continuous).measurableSet,
    c.remainingDilationCube_preimage hf, Measure.pi_pi]
  constructor
  · exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun p _ => (hxp p _ (Real.exp_pos _)).ne'))
  · exact ENNReal.prod_ne_top (fun p _ => measure_ball_lt_top.ne)

/-- Logarithm of the covariance normalizing mass. It is integrable, and
its mean is the signed root-character sum, for arbitrary weights. -/
theorem remainingExpansionInformation_integrable_integral (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    let J := fun x => Real.log
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)).toReal
    Integrable J μ ∧ (∫ x, J x ∂μ) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  dsimp only
  let i := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.1
  let j := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.2
  let hij := fun p : ↥(allPositiveRoots (d+1) \ P) =>
    ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  let t := fun p : ↥(allPositiveRoots (d+1) \ P) => ell p.val.1-ell p.val.2
  have he (x : X (d+1)) : Real.log
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)).toReal =
      -rootProductInformation d i j hij μ t x := by
    rw [c.remainingTimeProduct_eq_map hP hf μ x,
      Measure.map_apply (c.remainingEuclideanCoordinates hf).symm.measurable
        ((c.cube_open 1).preimage (c.rootDilation ell 1).continuous).measurableSet,
      c.remainingDilationCube_preimage hf]
    simp only [rootProductInformation, neg_neg]
    rfl
  simp_rw [he]
  refine ⟨(integrable_rootProductInformation d i j hij μ hA t).neg, ?_⟩
  rw [integral_neg, integral_rootProductInformation d i j hij μ hA t,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [t, i, j]
  ring

end EliminationChain
end DukePrimeDegree

end

end OAI
