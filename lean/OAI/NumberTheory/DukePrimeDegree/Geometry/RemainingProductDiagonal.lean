import OAI.NumberTheory.DukePrimeDegree.Geometry.RootProductCovariance
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductSupport

namespace OAI

/-! # Diagonal covariance in actual remaining-root time coordinates -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_dilation (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) (ell : Fin n → ℝ) (r : ℝ)
    (u : c.Time) (p : ↥(allPositiveRoots n \ P)) :
    c.remainingEuclideanCoordinates hf (c.rootDilation ell r u) p =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) *
        c.remainingEuclideanCoordinates hf u p := by
  have h := c.timeVectorHomeomorph_dilation ell r u ((c.remainingIndexEquiv hf).symm p)
  have he : c.roots.get ((c.remainingIndexEquiv hf).symm p) = p.val :=
    congrArg Subtype.val ((c.remainingIndexEquiv hf).apply_symm_apply p)
  change c.timeVectorHomeomorph (c.rootDilation ell r u) ((c.remainingIndexEquiv hf).symm p) =
    Real.exp ((ell p.val.1 - ell p.val.2) * r) *
      c.timeVectorHomeomorph u ((c.remainingIndexEquiv hf).symm p)
  simpa only [he] using h

lemma remainingTimeProduct_eq_map (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    c.remainingTimeProduct hP hf μ x =
      (Measure.pi fun p : ↥(allPositiveRoots n \ P) =>
        intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x).map
          (c.remainingEuclideanCoordinates hf).symm := by
  unfold remainingTimeProduct remainingIntrinsicProduct
  rw [Measure.map_map (c.remainingWordHomeomorph hP hf).symm.measurable
    (c.remainingGroupCoordinates hP hf).symm.measurable]
  congr 1
  funext v
  simp [remainingGroupCoordinates]

lemma remainingCoordinates_unit_cube (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) :
    (c.remainingEuclideanCoordinates hf).symm ''
      (Set.univ.pi fun _ : ↥(allPositiveRoots n \ P) => Metric.ball 0 1) = c.cube 1 := by
  let E := c.remainingEuclideanCoordinates hf
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (c.remainingEuclideanCoordinates_cube hf 1 _).mpr
    intro p
    have hp := hv p (mem_univ p)
    change |E (E.symm v) p| < 1
    rw [E.apply_symm_apply]
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hp
  · intro hu
    refine ⟨E u, ?_, E.symm_apply_apply u⟩
    intro p _
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (c.remainingEuclideanCoordinates_cube hf 1 u).mp hu p

theorem ae_remainingTimeProduct_diagonal (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((c.remainingTimeProduct hP hf μ x).map (c.rootDilation ell (-t)))
          (c.cube 1) := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let E := c.remainingEuclideanCoordinates hf
  let S : (I → ℝ) → (I → ℝ) := fun v p => rootTimeScaling ell p.val.1 p.val.2 t (v p)
  let ν := fun x => Measure.pi fun p : I =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x
  let R : Set (I → ℝ) := Set.univ.pi fun _ : I => Metric.ball 0 1
  have hcov := ae_rootProduct_diagonal d (fun p : I => p.val.1) (fun p : I => p.val.2)
    (fun p => ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)
    μ hA ell hell t
  filter_upwards [hcov] with x hx
  change ν (rightAction x (diagonalOneParameter ell hell t)) =
    anchorNormalize ((ν x).map S) R at hx
  have hS : Measurable S := measurable_pi_iff.mpr fun p =>
    (rootTimeScaling ell p.val.1 p.val.2 t).measurable.comp (measurable_pi_apply p)
  have he : E.symm ∘ S = c.rootDilation ell (-t) ∘ E.symm := by
    funext v
    apply E.injective
    change E (E.symm (S v)) = E (c.rootDilation ell (-t) (E.symm v))
    rw [E.apply_symm_apply]
    funext p
    rw [c.remainingEuclideanCoordinates_dilation hf]
    change Real.exp ((ell p.val.2 - ell p.val.1) * t) * v p =
      Real.exp ((ell p.val.1 - ell p.val.2) * (-t)) * E (E.symm v) p
    rw [E.apply_symm_apply]
    congr 2
    ring
  rw [c.remainingTimeProduct_eq_map hP hf, c.remainingTimeProduct_eq_map hP hf]
  change (ν (rightAction x (diagonalOneParameter ell hell t))).map E.symm =
    anchorNormalize (((ν x).map E.symm).map (c.rootDilation ell (-t))) (c.cube 1)
  have hnorm : (anchorNormalize ((ν x).map S) R).map E.symm =
      anchorNormalize (((ν x).map S).map E.symm) (E.symm '' R) := by
    simpa only [Homeomorph.toMeasurableEquiv_coe] using
      (anchorNormalize_map_equiv ((ν x).map S) E.symm.toMeasurableEquiv R).symm
  rw [hx, hnorm, c.remainingCoordinates_unit_cube hf]
  congr 1
  rw [Measure.map_map E.symm.measurable hS,
    Measure.map_map (c.rootDilation ell (-t)).measurable E.symm.measurable, he]

end EliminationChain
end DukePrimeDegree

end

end OAI
