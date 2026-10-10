import OAI.Probability.GaussianPropeller.PairBounds

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
@[simp] theorem mem_activeLabels (A : Fin k → Set (Space d)) (i : Fin k) :
    i ∈ activeLabels A ↔ gaussian d (A i) ≠ 0 := by
  classical
  simp [activeLabels]

omit [NeZero k] in

theorem sum_active_centroid {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i : activeLabels A, centroid (A i) = 0 := by
  classical
  rw [Finset.sum_coe_sort (activeLabels A) (fun i => centroid (A i))]
  have he : ∑ i ∈ activeLabels A, centroid (A i) = ∑ i, centroid (A i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact centroid_eq_zero_of_null (by simpa only [mem_activeLabels, not_not] using hi)
  rw [he, sum_centroid_eq_zero hA]

omit [NeZero k] in
theorem active_centroids_obtuse {A : Fin k → Set (Space d)} (hA : MinimalOptimal A) :
    Pairwise (fun i j : activeLabels A => ⟪centroid (A i), centroid (A j)⟫ < 0) := by
  intro i j hij
  exact negative_inner_of_minimal hA (fun hh => hij (Subtype.ext hh))
    ((mem_activeLabels A i).mp i.property) ((mem_activeLabels A j).mp j.property)

omit [NeZero k] in

theorem active_centroid_rank {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (i : activeLabels A) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : activeLabels A => centroid (A j)))) =
      activeCount A - 1 := by
  classical
  simpa only [Fintype.card_coe, activeCount] using GaussianPropeller.Gram.finrank_span
    (fun j : activeLabels A => centroid (A j)) (active_centroids_obtuse hA)
    (sum_active_centroid hA.1.1) i

theorem centroid_closedCell {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) :
    centroid (closedCell (fun j => centroid (A j)) i) = centroid (A i) := by
  exact setIntegral_congr_set (active_eq_closedCell_ae hA hpos hi).symm

noncomputable def residualCoefficient (z y : Space d) : ℝ := -⟪z,y⟫ / ‖z‖^2
noncomputable def residualVector (z y : Space d) : Space d := y + residualCoefficient z y • z

omit [NeZero k] in
theorem residual_orthogonal {z y : Space d} (hz : z ≠ 0) :
    ⟪z,residualVector z y⟫ = 0 := by
  simp only [residualVector, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    residualCoefficient]
  field_simp
  ring

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

theorem minimal_residual_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := residualVector z (centroid (A j))
    let s := residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l)))/(2*Real.pi*Real.sqrt (2*Real.pi)) := by
  dsimp only
  let z := centroid (A i)
  let r := residualVector z (centroid (A j))
  let s := residualVector z (centroid (A l))
  let a := residualCoefficient z (centroid (A j))
  let b := residualCoefficient z (centroid (A l))
  have ha : 0 < a := residualCoefficient_pos (negative_inner_of_minimal hA hij hi hj)
  have hb : 0 < b := residualCoefficient_pos (negative_inner_of_minimal hA hil hi hl)
  have hz : z ≠ 0 := active_centroid_ne_zero hA hpos hi
  change Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
    9*‖z‖*(1+a)*(1+b)/(2*Real.pi*Real.sqrt (2*Real.pi))
  by_cases hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2
  · apply GaussianPropeller.Pair.centroid_residual_pair
      (closedCell (fun j => centroid (A j)) i) (measurableSet_closedCell _ _)
      z r s hz (centroid_closedCell hA hpos hi)
      (residual_orthogonal hz) (residual_orthogonal hz)
      (by linarith : 0 < 1+a) (by linarith : 0 < 1+b) ?_ ?_ hd
    · intro x hx
      have hh := hx j
      change ⟪centroid (A j),x⟫ ≤ ⟪z,x⟫ at hh
      simp only [r,residualVector,inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial]
      change ⟪centroid (A j),x⟫+a*⟪z,x⟫ ≤ (1+a)*⟪z,x⟫
      linarith
    · intro x hx
      have hh := hx l
      change ⟪centroid (A l),x⟫ ≤ ⟪z,x⟫ at hh
      simp only [s,residualVector,inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial]
      change ⟪centroid (A l),x⟫+b*⟪z,x⟫ ≤ (1+b)*⟪z,x⟫
      linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hd)]
    positivity

end GaussianPropeller.Reduction

end OAI
