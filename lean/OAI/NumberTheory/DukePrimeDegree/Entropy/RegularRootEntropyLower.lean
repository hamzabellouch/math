import OAI.NumberTheory.DukePrimeDegree.Entropy.KernelFutureInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.StationaryCoverObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.AtomicRootEntropyZero

namespace OAI

/-! # An unconditional lower bound by actual expanding-root information -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The stationary whole-future kernel is constructed here; its existence,
normalization and disintegration properties are not additional inputs. -/
theorem positive_root_sum_le_diagonal_entropy (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
      (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2) ≤
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨H,Q,κ,hH,hQ,hκ,_,_,_,_,hstat,hself,hversion,hmass,_⟩ :=
    exists_cover_stationary_wholeFutureKernel d ell hell hgap μ (by norm_num : (0:ℝ)<1)
  let : IsMarkovKernel κ := hκ
  let c := completeRootChain (d+1)
  have hP : InitialRootPattern (∅ : Finset (Fin (d+1) × Fin (d+1))) := by
    intro p hp
    simp at hp
  have hb := c.wholeFuture_rootSum_le_metricEntropy d hP (completeRootChain_final (d+1))
    μ hA ell hell Q hQ κ hstat hself hversion hmass
  let f : Fin (d+1) × Fin (d+1) → ℝ := fun p =>
    (ell p.2-ell p.1) * canonicalRootCoefficient d μ p.1 p.2
  have hs : (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) =
      ∑ p : allPositiveRoots (d+1), f p := by
    rw [← Finset.sum_subtype (allPositiveRoots (d+1) \ ∅) (by intro p; rfl) f,
      ← Finset.sum_subtype (allPositiveRoots (d+1)) (by intro p; rfl) f,
      Finset.sdiff_empty]
  change ENNReal.ofReal (∑ p : ↥(allPositiveRoots (d+1) \ ∅), f p) ≤ _ at hb
  rw [hs] at hb
  exact hb

/-- Zero metric entropy and zero actual expanding-root information are
 equivalent for these regular weights. -/
theorem diagonal_entropy_zero_iff_positive_coefficients_zero (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0 ↔
      ∀ p : allPositiveRoots (d+1), canonicalRootCoefficient d μ p.val.1 p.val.2=0 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hweight (p : allPositiveRoots (d+1)) : 0 < ell p.val.2-ell p.val.1 :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) (hgap p)
  constructor
  · intro hz p
    have hb := positive_root_sum_le_diagonal_entropy d ell hell hgap μ
    rw [hz] at hb
    have hs : (∑ q : allPositiveRoots (d+1),
        (ell q.val.2-ell q.val.1) * canonicalRootCoefficient d μ q.val.1 q.val.2) ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp (le_antisymm hb (by positivity))
    have hp : (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 ≤ 0 :=
      (Finset.single_le_sum (fun q _ => mul_nonneg (hweight q).le
        (canonicalRootCoefficient_nonneg d μ q.val.1 q.val.2)) (Finset.mem_univ p)).trans hs
    exact le_antisymm (by nlinarith [hweight p])
      (canonicalRootCoefficient_nonneg d μ p.val.1 p.val.2)
  · intro hz
    apply diagonal_entropy_zero_of_atomic_positive_roots d ell hell hgap μ
    intro p
    let q : allPositiveRoots (d+1) := ⟨p.val,(Finset.mem_sdiff.mp p.prop).1⟩
    exact (canonicalRootCoefficient_zero_iff d μ hA p.val.1 p.val.2
      (ne_of_lt (Finset.mem_filter.mp q.prop).2)).mp (hz q)

end DukePrimeDegree

end

end OAI
