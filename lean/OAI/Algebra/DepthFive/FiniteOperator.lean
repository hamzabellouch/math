import OAI.Algebra.DepthFive.OperatorRank
import OAI.Algebra.DepthFive.MixedOperator
import OAI.Algebra.DepthFive.RankMeasure
import OAI.Algebra.DepthFive.MixedOperatorBidegree

namespace OAI

/-! The finite-source rank measure and its product decomposition. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The full substitution operator restricted to a fixed bidegree source.
Keeping the ambient polynomial codomain avoids unnecessary degree transports. -/
def rawOperatorFamily (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) :=
  RankMeasure.restrictFamily (mixedOperator isV).toLinearMap
    (bidegreeSubmodule isV a b)

@[simp] theorem rawOperatorFamily_apply (isV : σ → Bool) (a b : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    rawOperatorFamily isV a b q p = mixedOperator isV q p := rfl

/-- Project the defining polynomial to bidegree `(k,m)` before substitution. -/
def bidegreeOperatorFamily (isV : σ → Bool) (a b k m : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) :=
  (rawOperatorFamily isV a b).comp (bidegreeComponent isV k m)

@[simp] theorem bidegreeOperatorFamily_apply (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    bidegreeOperatorFamily isV a b k m q p =
      mixedOperator isV (bidegreeComponent isV k m q) p := rfl

/-- The rank measure from the manuscript, with an ambient codomain. -/
def bidegreeRank (isV : σ → Bool) (a b k m : ℕ) (q : MvPolynomial σ K) : ℕ :=
  RankMeasure.measure (bidegreeOperatorFamily isV a b k m) q

@[simp] theorem bidegreeRank_zero (isV : σ → Bool) (a b k m : ℕ) :
    bidegreeRank (K := K) isV a b k m 0 = 0 :=
  RankMeasure.measure_zero _

 theorem bidegreeRank_smul (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) (c : K) (hc : c ≠ 0) :
    bidegreeRank isV a b k m (c • q) = bidegreeRank isV a b k m q :=
  RankMeasure.measure_smul _ c hc q

 theorem bidegreeRank_add_le [Finite σ] (isV : σ → Bool) (a b k m : ℕ)
    (q r : MvPolynomial σ K) :
    bidegreeRank isV a b k m (q + r) ≤
      bidegreeRank isV a b k m q + bidegreeRank isV a b k m r :=
  RankMeasure.measure_add_le _ q r

 theorem bidegreeRank_sum_le [Finite σ] {ι : Type*} (s : Finset ι)
    (isV : σ → Bool) (a b k m : ℕ) (q : ι → MvPolynomial σ K) :
    bidegreeRank isV a b k m (∑ i ∈ s, q i) ≤
      ∑ i ∈ s, bidegreeRank isV a b k m (q i) :=
  RankMeasure.measure_sum_le _ s q

 theorem bidegreeRank_eq_raw_of_mem (isV : σ → Bool) (a b k m : ℕ)
    {q : MvPolynomial σ K} (hq : q ∈ bidegreeSubmodule isV k m) :
    bidegreeRank isV a b k m q =
      RankMeasure.mapRank (rawOperatorFamily isV a b q) := by
  unfold bidegreeRank RankMeasure.measure bidegreeOperatorFamily
  rw [LinearMap.comp_apply, bidegreeComponent_eq_self hq]

/-- The projected product map is a sum of maps with fixed factor bidegrees. -/
theorem bidegreeOperatorFamily_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (isV : σ → Bool) (a b k m : ℕ) (e : ι → ℕ)
    (q : ι → MvPolynomial σ K) (hq : ∀ j, (q j).IsHomogeneous (e j)) :
    bidegreeOperatorFamily isV a b k m (∏ j, q j) =
      ∑ d : (∀ j : ι, Fin (e j + 1)),
        if (∑ j : ι, (d j : ℕ)) = k ∧ (∑ j : ι, (e j - (d j : ℕ))) = m then
          rawOperatorFamily isV a b
            (∏ j, bidegreeComponent isV (d j) (e j - d j) (q j))
        else 0 := by
  classical
  change rawOperatorFamily isV a b
      (bidegreeComponent isV k m (∏ j, q j)) = _
  rw [bidegreeComponent_product isV e q hq, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

/-- Subadditivity reduces product rank to the constrained assignments. -/
theorem bidegreeRank_product_le [Finite σ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (isV : σ → Bool) (a b k m : ℕ) (e : ι → ℕ)
    (q : ι → MvPolynomial σ K) (hq : ∀ j, (q j).IsHomogeneous (e j)) :
    bidegreeRank isV a b k m (∏ j, q j) ≤
      ∑ d : (∀ j : ι, Fin (e j + 1)),
        if (∑ j : ι, (d j : ℕ)) = k ∧ (∑ j : ι, (e j - (d j : ℕ))) = m then
          RankMeasure.mapRank (rawOperatorFamily isV a b
            (∏ j, bidegreeComponent isV (d j) (e j - d j) (q j)))
        else 0 := by
  classical
  unfold bidegreeRank RankMeasure.measure
  rw [bidegreeOperatorFamily_product isV a b k m e q hq]
  convert RankMeasure.mapRank_sum_le Finset.univ
    (fun d : (∀ j : ι, Fin (e j + 1)) =>
      if (∑ j : ι, (d j : ℕ)) = k ∧ (∑ j : ι, (e j - (d j : ℕ))) = m then
        rawOperatorFamily isV a b
          (∏ j, bidegreeComponent isV (d j) (e j - d j) (q j))
      else 0) using 1
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

/-- Replacing an ambient codomain with any subspace containing the image
preserves the rank measure exactly. -/
theorem rawOperatorFamily_rank_codRestrict (isV : σ → Bool) (a b : ℕ)
    (q : MvPolynomial σ K) (T : Submodule K (MvPolynomial σ K))
    (hT : ∀ p : bidegreeSubmodule (K := K) isV a b,
      rawOperatorFamily isV a b q p ∈ T) :
    RankMeasure.mapRank ((rawOperatorFamily isV a b q).codRestrict T hT) =
      RankMeasure.mapRank (rawOperatorFamily isV a b q) := by
  have h := RankMeasure.mapRank_subtype_comp T
    ((rawOperatorFamily isV a b q).codRestrict T hT)
  exact h.symm

/-- The finite-dimensional operator with its exact target bidegree.
The map is zero when `k > a`, so no degree-inequality argument is needed. -/
def finiteMixedOperator (isV : σ → Bool) (a b k m : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K]
        bidegreeSubmodule (K := K) isV (a - k) (b + m)) where
  toFun q := (bidegreeOperatorFamily isV a b k m q).codRestrict
    (bidegreeSubmodule isV (a - k) (b + m)) (fun p =>
      mixedOperator_mem_bidegreeSubmodule_all isV
        (bidegreeComponent_mem isV k m q) p.property)
  map_add' q r := by
    ext p : 2
    exact LinearMap.congr_fun (map_add (bidegreeOperatorFamily isV a b k m) q r) p
  map_smul' c q := by
    ext p : 2
    exact LinearMap.congr_fun (map_smul (bidegreeOperatorFamily isV a b k m) c q) p

@[simp] theorem finiteMixedOperator_apply_coe (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    (finiteMixedOperator isV a b k m q p : MvPolynomial σ K) =
      mixedOperator isV (bidegreeComponent isV k m q) p := rfl

/-- On a polynomial of bidegree `(k,m)`, projection is redundant. -/
theorem finiteMixedOperator_apply_of_mem (isV : σ → Bool) (a b k m : ℕ)
    {q : MvPolynomial σ K} (hq : q ∈ bidegreeSubmodule isV k m)
    (p : bidegreeSubmodule (K := K) isV a b) :
    (finiteMixedOperator isV a b k m q p : MvPolynomial σ K) =
      mixedOperator isV q p := by
  rw [finiteMixedOperator_apply_coe, bidegreeComponent_eq_self hq]

/-- The intrinsic finite-dimensional map and the ambient-codomain rank agree. -/
theorem finiteMixedOperator_rank (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) :
    RankMeasure.mapRank (finiteMixedOperator isV a b k m q) =
      bidegreeRank isV a b k m q := by
  have h := RankMeasure.mapRank_subtype_comp
    (bidegreeSubmodule (K := K) isV (a - k) (b + m))
    (finiteMixedOperator isV a b k m q)
  exact h.symm

end Problem335

end

end OAI
