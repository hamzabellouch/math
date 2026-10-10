import OAI.NumberTheory.DukePrimeDegree.Entropy.ContractingCutItineraries
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogTopology
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLogContraction
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootBasedMeasure

namespace OAI

/-! # Actual diagonal cut itineraries contain root neighborhoods

For each logarithmic distance observable one can choose a cut with
summable boundary returns. The proved matrix contraction then places a
whole upper-root neighborhood in almost every infinite itinerary atom.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRoot_orbit_iterate_diagonal {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (k : ℕ)
    (x : X n) (t : UpperRootTime n) :
    (fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain n).word t)) =
      rightAction ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)
        ((completeRootChain n).word ((completeRootChain n).rootDilation ell k t)) := by
  have hp : (diagonalOneParameter ell hell (-1))^k=diagonalOneParameter ell hell (-(k:ℝ)) := by
    rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
  simp only [rightAction_iterate,hp]
  simpa only [neg_neg, upperRootWordHomeomorph_apply] using
    upperRoot_orbit_diagonal n ell hell (-(k:ℝ)) x t

theorem quotientLogDistance_upperRoot_iterate_bound {d : ℕ}
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    {R : ℝ} (hR : 0 < R) (hsmall : 3*(d+1:ℝ)*R ≤ 1)
    (z x : X (d+1)) (k : ℕ) {t : UpperRootTime (d+1)}
    (ht : t ∈ (completeRootChain (d+1)).cube R) :
    |quotientLogDistance z
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word t))) -
      quotientLogDistance z
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)| ≤
      Real.exp (-ε*(k:ℝ)) := by
  rw [upperRoot_orbit_iterate_diagonal]
  exact (quotientLogDistance_right_bound z _ _).trans
    (upperRoot_logLength_contraction ell ε hε hgap hR hsmall (Nat.cast_nonneg _) ht)

theorem exists_cut_with_upperRoot_itinerary_neighborhoods (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (z : X (d+1)) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ᵐ x ∂μ,
      ∀ᶠ t in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        (quotientLogDistance z
          ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
            (rightAction x ((completeRootChain (d+1)).word t))) < r ↔
        quotientLogDistance z
          ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) < r) := by
  let T : X (d+1) → X (d+1) := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    change μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=μ
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hsum : Summable (fun k : ℕ => Real.exp (-ε*(k:ℝ))) := by
    simpa only [mul_comm] using (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hε))
  obtain ⟨r,hr,hgood⟩ := exists_cut_with_contracting_itinerary_neighborhoods μ hT
    (continuous_rightAction _) (continuous_quotientLogDistance (d+1) z)
    (fun k : ℕ => Real.exp (-ε*(k:ℝ))) hsum (fun _ => (Real.exp_pos _).le) hab
  refine ⟨r,hr,?_⟩
  filter_upwards [hgood] with x hx
  let R : ℝ := 1/(6*(d+1:ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : 3*(d+1:ℝ)*R ≤ 1 := by
    dsimp [R]
    have hn : (d+1:ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  let F : UpperRootTime (d+1) → X (d+1) := fun t => rightAction x ((completeRootChain (d+1)).word t)
  have hbase : F (completeRootChain (d+1)).zeroTime=x := by
    simp only [F,EliminationChain.word_zeroTime,rightAction_one]
  have hF : ContinuousAt F (completeRootChain (d+1)).zeroTime :=
    ((continuous_rightOrbit (d+1) x).comp (upperRootWord_isEmbedding (d+1)).continuous).continuousAt
  exact hx F (completeRootChain (d+1)).zeroTime hbase hF
    ((completeRootChain (d+1)).cube R)
    (((completeRootChain (d+1)).cube_open R).mem_nhds
      ((completeRootChain (d+1)).zeroTime_mem_cube hR))
    (fun k t ht => quotientLogDistance_upperRoot_iterate_bound ell hell ε hε hgap hR hsmall z x k ht)

end DukePrimeDegree

end

end OAI
