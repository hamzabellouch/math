import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanSelectedSupport
import OAI.NumberTheory.Ostmann.Construction.CounterpartCutoff

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem remainingNormalization_ne_zero (T : List SourceSlot) :
    C.remainingNormalization T ≠ 0 := by
  intro hz
  have hm : ∀ z : RemainingSample C.sources T C.giant,
      (remainingPrior C.sources T C.giant).mass z = 0 := by
    intro z
    rw [C.remaining_mass_normalization T z, hz]
    simp
  have ht := (remainingPrior C.sources T C.giant).mass_total
  simp only [hm, Finset.sum_const_zero] at ht
  norm_num at ht

theorem weighted_counterpart_zero_of_small_mass_zero
    (y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (hy : (assignmentPrior C.sources _).mass (smallAssignment C y) = 0)
    (p : ℕ) (q : C.giant.Sample) :
    (externalPivotWeight C.giantCenter p : ℂ) * counterpart C y (q.val : ℤ) = 0 := by
  have hm : (remainingPrior C.sources _ C.giant).mass (q, smallAssignment C y) = 0 := by
    change C.giant.law.mass q * (assignmentPrior C.sources _).mass (smallAssignment C y) = 0
    rw [hy, mul_zero]
  have he := C.remaining_mass_scalar_extraction (Seed (k:=k) (L:=L))
    (fun _ h => h) (l+1) l (C.compensationLogScale l) (stepGap BD Bz k L l) p
    (outerAssignment C y) (q, smallAssignment C y)
  rw [hm, mul_zero] at he
  have hr : externalPivotWeight C.giantCenter p *
      remainingCounterpart C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant
        ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
        (C.compensationLogScale l) C.giantCenter (C.cells.center (bulkSize k L/2))
        (outerAssignment C y) (q,smallAssignment C y) = 0 := by
    have hn := mul_ne_zero (remainingNormalization_ne_zero C
      (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))
      (Real.exp_ne_zero (-(stepGap BD Bz k L l)))
    apply (mul_eq_zero.mp ?_).resolve_left hn
    simpa only [mul_assoc] using he.symm
  rw [counterpart_nat_eq_remainingCounterpart C y q, ← Complex.ofReal_mul, hr,
    Complex.ofReal_zero]

theorem originalMixedMean_zero_of_small_mass_zero
    (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C)
    (hy : (assignmentPrior C.sources _).mass (smallAssignment C y) = 0) :
    originalMixedMean C outside x y s t c e = 0 := by
  unfold originalMixedMean
  rw [mixedMean_eq_weighted]
  apply Finset.sum_eq_zero
  intro z hz
  have he := weighted_counterpart_zero_of_small_mass_zero C y hy z.1.val z.2
  simp only [mixedWeight, mixedP, mixedQ, sourceIntegrand, Complex.ofReal_mul]
  have hz' (a b c d r : ℂ) (h : a*c=0) : (a*b)*((d*c)*r)=0 := by
    calc
      _ = (a*c)*(b*d*r) := by ring
      _ = 0 := by rw [h, zero_mul]
  exact hz' _ _ _ _ _ he

theorem smallAssignment_mass_zero_of_right_mass_zero
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (hx : (assignmentPrior C.sources _).mass x ≠ 0)
    (hu : outerAssignment C y = outerAssignment C x)
    (hy : (assignmentPrior C.sources _).mass y = 0) :
    (assignmentPrior C.sources _).mass (smallAssignment C y) = 0 := by
  rw [restoringAssignment_mass_eq C.sources (l+1) _ x] at hx
  rw [restoringAssignment_mass_eq C.sources (l+1) _ y] at hy
  change (assignmentPrior C.sources _).mass (outerAssignment C y) *
    (assignmentPrior C.sources _).mass (smallAssignment C y) = 0 at hy
  rw [hu] at hy
  exact (mul_eq_zero.mp hy).resolve_left (mul_ne_zero_iff.mp hx).1

theorem originalMixedMean_zero_of_right_mass_zero
    (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C)
    (hx : (assignmentPrior C.sources _).mass x ≠ 0)
    (hu : outerAssignment C y = outerAssignment C x)
    (hy : (assignmentPrior C.sources _).mass y = 0) :
    originalMixedMean C outside x y s t c e = 0 :=
  originalMixedMean_zero_of_small_mass_zero C outside x y s t c e
    (smallAssignment_mass_zero_of_right_mass_zero C x y hx hu hy)

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
