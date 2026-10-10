import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootBasedMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDilation

namespace OAI

/-! # Translation and diagonal covariance of based full-root measures -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootTranslate (n : ℕ) (t : UpperRootTime n) :
    UpperRootTime n ≃ₜ UpperRootTime n :=
  (upperRootWordHomeomorph n).trans
    ((Homeomorph.mulLeft (upperRootWordHomeomorph n t)).trans
      (upperRootWordHomeomorph n).symm)

lemma upperRootWord_rebase (n : ℕ) (t u : UpperRootTime n) :
    upperRootWordHomeomorph n (upperRootRebase n t u) =
      (upperRootWordHomeomorph n t)⁻¹ * upperRootWordHomeomorph n u := by
  rw [upperRootRebase_apply, Homeomorph.apply_symm_apply]

lemma upperRootWord_translate (n : ℕ) (t u : UpperRootTime n) :
    upperRootWordHomeomorph n (upperRootTranslate n t u) =
      upperRootWordHomeomorph n t * upperRootWordHomeomorph n u :=
  (upperRootWordHomeomorph n).apply_symm_apply _

lemma upperRootRebase_translate (n : ℕ) (t u v : UpperRootTime n) :
    upperRootRebase n (upperRootTranslate n t u) (upperRootTranslate n t v) =
      upperRootRebase n u v := by
  apply (upperRootWordHomeomorph n).injective
  simp only [upperRootWord_rebase, upperRootWord_translate]
  group

lemma upperRootRebase_rebase (n : ℕ) (t u v : UpperRootTime n) :
    upperRootRebase n u (upperRootRebase n t v) =
      upperRootRebase n (upperRootTranslate n t u) v := by
  apply (upperRootWordHomeomorph n).injective
  simp only [upperRootWord_rebase, upperRootWord_translate]
  group

lemma centerUpperRootMeasure_smul (n : ℕ) (ν : Measure (UpperRootTime n))
    (c : ℝ≥0∞) (t : UpperRootTime n) :
    centerUpperRootMeasure n (c • ν) t = c • centerUpperRootMeasure n ν t :=
  Measure.map_smul c (upperRootRebase n t).measurable.aemeasurable

lemma basedUpperRootMeasure_smul (n : ℕ) (ν : Measure (UpperRootTime n))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (t : UpperRootTime n) :
    basedUpperRootMeasure n (c • ν) t = basedUpperRootMeasure n ν t := by
  unfold basedUpperRootMeasure
  rw [centerUpperRootMeasure_smul, anchorNormalize_smul _ _ _ hc0 hcT]

lemma centerUpperRootMeasure_translate (n : ℕ) (ν : Measure (UpperRootTime n))
    (t u : UpperRootTime n) :
    centerUpperRootMeasure n (ν.map (upperRootTranslate n t)) (upperRootTranslate n t u) =
      centerUpperRootMeasure n ν u := by
  unfold centerUpperRootMeasure
  rw [Measure.map_map (upperRootRebase n _).measurable (upperRootTranslate n t).measurable]
  congr 1
  funext v
  exact upperRootRebase_translate n t u v

lemma basedUpperRootMeasure_translate (n : ℕ) (ν : Measure (UpperRootTime n))
    (t u : UpperRootTime n) :
    basedUpperRootMeasure n (ν.map (upperRootTranslate n t)) (upperRootTranslate n t u) =
      basedUpperRootMeasure n ν u := by
  unfold basedUpperRootMeasure
  rw [centerUpperRootMeasure_translate]

lemma centerUpperRootMeasure_center (n : ℕ) (ν : Measure (UpperRootTime n))
    (t u : UpperRootTime n) :
    centerUpperRootMeasure n (centerUpperRootMeasure n ν t) u =
      centerUpperRootMeasure n ν (upperRootTranslate n t u) := by
  unfold centerUpperRootMeasure
  rw [Measure.map_map (upperRootRebase n u).measurable (upperRootRebase n t).measurable]
  congr 1
  funext v
  exact upperRootRebase_rebase n t u v

lemma basedUpperRootMeasure_center (n : ℕ) (ν : Measure (UpperRootTime n))
    (t u : UpperRootTime n) :
    basedUpperRootMeasure n (centerUpperRootMeasure n ν t) u =
      basedUpperRootMeasure n ν (upperRootTranslate n t u) := by
  unfold basedUpperRootMeasure
  rw [centerUpperRootMeasure_center]

lemma centerUpperRootMeasure_unit_lt_top (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (t : UpperRootTime n) :
    centerUpperRootMeasure n ν t ((completeRootChain n).cube 1) < ∞ := by
  let : IsLocallyFiniteMeasure (centerUpperRootMeasure n ν t) :=
    centerUpperRootMeasure_locallyFinite n ν t
  exact (measure_mono ((completeRootChain n).cube_subset_closedCube 1)).trans_lt
    ((completeRootChain n).closedCube_compact 1).measure_lt_top

lemma basedUpperRootMeasure_rebase (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (t u : UpperRootTime n) (ht : t ∈ ν.support) :
    basedUpperRootMeasure n (basedUpperRootMeasure n ν t) u =
      basedUpperRootMeasure n ν (upperRootTranslate n t u) := by
  change basedUpperRootMeasure n
    ((centerUpperRootMeasure n ν t ((completeRootChain n).cube 1))⁻¹ •
      centerUpperRootMeasure n ν t) u = _
  rw [basedUpperRootMeasure_smul n _ _
    (ENNReal.inv_ne_zero.mpr (centerUpperRootMeasure_unit_lt_top n ν t).ne)
    (ENNReal.inv_ne_top.mpr (centerUpperRootMeasure_unit_pos n ν t ht).ne')]
  exact basedUpperRootMeasure_center n ν t u

lemma upperRootRebase_dilation (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (t u : UpperRootTime n) :
    upperRootRebase n ((completeRootChain n).rootDilation ell r t)
        ((completeRootChain n).rootDilation ell r u) =
      (completeRootChain n).rootDilation ell r (upperRootRebase n t u) := by
  apply (upperRootWordHomeomorph n).injective
  apply Subtype.ext
  rw [upperRootWord_rebase]
  change ((upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell r t)).val)⁻¹ *
    (upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell r u)).val = _
  rw [upperRootWord_diagonal n ell hell r t, upperRootWord_diagonal n ell hell r u,
    upperRootWord_diagonal n ell hell r (upperRootRebase n t u), upperRootWord_rebase]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [diagonalOneParameter_neg]
  group

lemma centerUpperRootMeasure_dilation (n : ℕ) (ν : Measure (UpperRootTime n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (r : ℝ) (t : UpperRootTime n) :
    centerUpperRootMeasure n (ν.map ((completeRootChain n).rootDilation ell r))
        ((completeRootChain n).rootDilation ell r t) =
      (centerUpperRootMeasure n ν t).map ((completeRootChain n).rootDilation ell r) := by
  unfold centerUpperRootMeasure
  rw [Measure.map_map (upperRootRebase n _).measurable
      ((completeRootChain n).rootDilation ell r).measurable,
    Measure.map_map ((completeRootChain n).rootDilation ell r).measurable
      (upperRootRebase n t).measurable]
  congr 1
  funext u
  exact upperRootRebase_dilation n ell hell r t u

lemma basedUpperRootMeasure_dilation (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (r : ℝ) (t : UpperRootTime n) (ht : t ∈ ν.support) :
    basedUpperRootMeasure n (ν.map ((completeRootChain n).rootDilation ell r))
        ((completeRootChain n).rootDilation ell r t) =
      anchorNormalize ((basedUpperRootMeasure n ν t).map
        ((completeRootChain n).rootDilation ell r)) ((completeRootChain n).cube 1) := by
  unfold basedUpperRootMeasure
  rw [centerUpperRootMeasure_dilation n ν ell hell]
  unfold anchorNormalize
  rw [Measure.map_smul _ ((completeRootChain n).rootDilation ell r).measurable.aemeasurable]
  exact (anchorNormalize_smul _ _ _
    (ENNReal.inv_ne_zero.mpr (centerUpperRootMeasure_unit_lt_top n ν t).ne)
    (ENNReal.inv_ne_top.mpr (centerUpperRootMeasure_unit_pos n ν t ht).ne')).symm

end DukePrimeDegree

end

end OAI
