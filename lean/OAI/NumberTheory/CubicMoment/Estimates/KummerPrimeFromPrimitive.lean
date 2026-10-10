import OAI.NumberTheory.CubicMoment.Estimates.KummerChebyshevFromPrimitive
import OAI.NumberTheory.CubicMoment.Estimates.PrimeChebyshevDeweight
import OAI.NumberTheory.CubicMoment.Estimates.PublishedKummerPrime
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! The raw Kummer prime input follows from primitive finite-character
Hecke completion, with all prime-sum estimates and deweighting derived. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primeCancellationWeight_le_heckeError {c Q X : ℝ} (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hL : 1 ≤ Real.log X) :
    primeCancellationWeight c Q X ≤ heckeExponentialError c X Q := by
  have hP := (primeLogSize_bounds hQ hXp hL).1
  have hpow : (Real.log (X*Q))^2 ≤ (Real.log (X*Q))^4 := by nlinarith [sq_nonneg ((Real.log (X*Q))^2-1)]
  unfold primeCancellationWeight heckeExponentialError primeContourDenominator
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hXp.le) (Real.exp_pos _).le

theorem kummer_unweighted_from_primitive (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ 1 < X0 ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3=v) →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeCutoffSum (fun p => cubicSymbol p v) X‖ ≤
        B*primeCancellationWeight c (810*norm v) X := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := kummer_chebyshev_from_primitive hpub hperiod
  refine ⟨2*B+18,c/2,max (Y0^2) (Real.exp 2),by positivity,by positivity,?_,?_⟩
  · exact (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<2)).trans_le (le_max_right _ _)
  intro v hv hnc X hX
  have hXp : 0 < X := (Real.exp_pos 2).trans_le ((le_max_right _ _).trans hX)
  have hL : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hroot : Y0 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le ((le_max_left _ _).trans hX)
  have hQ : 1 ≤ 810*norm v := by nlinarith [one_le_norm hv]
  exact primeChebyshev_deweight (fun p => cubicSymbol p v)
    (fun p hp => norm_cubicSymbol_le_one hp.1 v) hB.le hc.le (by linarith) hQ hXp hL hroot
    (fun t ht => hbound v hv hnc t ht)

theorem kummerPrimeSiegelWalfisz_of_primitive (hpub : PrimitiveResidueHeckeInput) :
    KummerPrimeSiegelWalfisz := by
  obtain ⟨B,c,Y0,hB,hc,hY0,hbound⟩ :=
    kummer_unweighted_from_primitive hpub cubicSupplementaryPeriodicity_proved
  intro A D _hA _hD
  have herr := heckeExponentialError_logSaving (K := 810) (A := A) (D := D) hc (by norm_num)
  obtain ⟨X1,hX1⟩ := eventually_atTop.mp herr
  refine ⟨16*B,max Y0 (max X1 (Real.exp 2)),by positivity,hY0.trans_le (le_max_left _ _),?_⟩
  intro X hX v hv hnc hcon
  have hXY : Y0 ≤ X := (le_max_left _ _).trans hX
  have hXX : X1 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hXe
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) hXe
    rw [Real.log_exp] at hh
    linarith
  have hQ : 1 ≤ 810*norm v := by nlinarith [one_le_norm hv]
  calc
    _ ≤ B*primeCancellationWeight c (810*norm v) X := hbound v hv hnc X hXY
    _ ≤ B*heckeExponentialError c X (810*norm v) :=
      mul_le_mul_of_nonneg_left (primeCancellationWeight_le_heckeError hQ hXp hL) hB.le
    _ ≤ B*(16*X/(Real.log X)^D) := mul_le_mul_of_nonneg_left
      (hX1 X hXX _ hQ (mul_le_mul_of_nonneg_left hcon (by norm_num))) hB.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
