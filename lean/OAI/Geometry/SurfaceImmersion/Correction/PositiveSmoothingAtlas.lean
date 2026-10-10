import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Every smoothing atlas admits nonnegative square-partition weights with
exactly the same supports and outer cutoffs. This makes the associated
primitive amplitudes positive on their open nonzero loci. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def positiveWeightNormalizer (p : M) : ℝ :=
  ∑ i : A.centers, ((A.weight i p)^2)^2

lemma positiveWeightNormalizer_pos (p : M) : 0 < A.positiveWeightNormalizer p := by
  have hn : 0 ≤ A.positiveWeightNormalizer p :=
    Finset.sum_nonneg (fun i _ => sq_nonneg ((A.weight i p)^2))
  by_contra hp
  have hz : A.positiveWeightNormalizer p = 0 := le_antisymm (not_lt.mp hp) hn
  have hi : ∀ i : A.centers, A.weight i p = 0 := by
    intro i
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg ((A.weight j p)^2))).mp hz
    exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp (hsum i (Finset.mem_univ i)))
  have hpart := A.partition p
  simp only [hi,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hpart
  norm_num at hpart

lemma positiveWeightNormalizer_smooth :
    ContMDiff planeModel 𝓘(ℝ) ∞ A.positiveWeightNormalizer :=
  contMDiff_finsetSum (fun i _ => ((A.weight_smooth i).pow 2).pow 2)

def positiveWeight (i : A.centers) (p : M) : ℝ :=
  (A.weight i p)^2 / Real.sqrt (A.positiveWeightNormalizer p)

lemma positiveWeight_smooth (i : A.centers) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.positiveWeight i) := by
  have hsqrt : ContMDiff planeModel 𝓘(ℝ) ∞
      (fun p => Real.sqrt (A.positiveWeightNormalizer p)) := by
    intro p
    exact (Real.contDiffAt_sqrt (A.positiveWeightNormalizer_pos p).ne').contMDiffAt.comp p
      (A.positiveWeightNormalizer_smooth p)
  exact ((A.weight_smooth i).pow 2).div₀ hsqrt
    (fun p => (Real.sqrt_pos.mpr (A.positiveWeightNormalizer_pos p)).ne')

lemma positiveWeight_nonneg (i : A.centers) (p : M) : 0 ≤ A.positiveWeight i p :=
  div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

lemma positiveWeight_pos_iff (i : A.centers) (p : M) :
    0 < A.positiveWeight i p ↔ A.weight i p ≠ 0 := by
  change 0 < (A.weight i p)^2 / Real.sqrt (A.positiveWeightNormalizer p) ↔ _
  rw [div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (A.positiveWeightNormalizer_pos p))]
  exact sq_pos_iff

lemma positiveWeight_ne_zero_iff (i : A.centers) (p : M) :
    A.positiveWeight i p ≠ 0 ↔ A.weight i p ≠ 0 := by
  constructor
  · intro hp hw
    exact hp (by simp only [positiveWeight,hw,zero_pow (by decide : 2 ≠ 0),zero_div])
  · intro hw
    exact (A.positiveWeight_pos_iff i p).mpr hw |>.ne'

lemma positiveWeight_tsupport (i : A.centers) :
    tsupport (A.positiveWeight i) = tsupport (A.weight i) := by
  change closure (Function.support (A.positiveWeight i)) = closure (Function.support (A.weight i))
  congr 1
  ext p
  exact A.positiveWeight_ne_zero_iff i p

lemma positiveWeight_partition (p : M) :
    (∑ i : A.centers, (A.positiveWeight i p)^2) = 1 := by
  calc
    _ = (∑ i : A.centers, ((A.weight i p)^2)^2) /
        (Real.sqrt (A.positiveWeightNormalizer p))^2 := by
      simp only [positiveWeight,div_pow,Finset.sum_div]
    _ = A.positiveWeightNormalizer p / A.positiveWeightNormalizer p := by
      rw [Real.sq_sqrt (A.positiveWeightNormalizer_pos p).le]
      rfl
    _ = 1 := div_self (A.positiveWeightNormalizer_pos p).ne'

/-- The centers and outer functions are unchanged. Only the square
partition is normalized, retaining every support exactly. -/
def positiveAtlas : SmoothingAtlas M where
  centers := A.centers
  weight := A.positiveWeight
  outer := A.outer
  weight_smooth := A.positiveWeight_smooth
  weight_support := fun i => by
    rw [A.positiveWeight_tsupport i]
    exact A.weight_support i
  outer_smooth := A.outer_smooth
  outer_support := A.outer_support
  outer_one := fun i p hp => A.outer_one i p ((A.positiveWeight_tsupport i) ▸ hp)
  partition := A.positiveWeight_partition

lemma positiveAtlas_weight_nonneg (i : A.centers) (p : M) :
    0 ≤ A.positiveAtlas.weight i p := A.positiveWeight_nonneg i p

lemma positiveAtlas_weight_tsupport (i : A.centers) :
    tsupport (A.positiveAtlas.weight i) = tsupport (A.weight i) :=
  A.positiveWeight_tsupport i

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
