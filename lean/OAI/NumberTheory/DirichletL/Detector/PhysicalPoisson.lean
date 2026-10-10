import OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition ConcreteTraceCRT
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_frequency_congr (s : O) (hs : s≠0) (h k : O)
    (he : h-k ∈ (Ideal.span {s}:Ideal O)) : sexticGauss s hs h = sexticGauss s hs k := by
  have hmk := Ideal.Quotient.eq.mpr he
  simp only [sexticGauss, hmk]

def physicalQuotient (C : CalibrationData) (A s : O) (hs : s≠0)
    (m : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m)

lemma physicalQuotient_mk (C : CalibrationData) (A s : O) (hs : s≠0) (m : O) :
    physicalQuotient C A s hs (Ideal.Quotient.mk _ m) =
      calibratedNumerator C A m * sexticGauss s hs (-m) := by
  have hd : (C.generator*A)*s ∣ representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m ∈
      (Ideal.span {C.generator*A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right (C.generator*A) s).trans hd)
  have hs' : -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) ∈
      (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative ((C.generator*A)*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s (C.generator*A)).trans hd)
  unfold physicalQuotient
  rw [calibratedNumerator_congr C A _ m hA, sexticGauss_frequency_congr s hs _ (-m) hs']

theorem physical_row_poisson (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
      ((K / elementNorm (C.generator*A) : ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C A s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)) := by
  let c := (C.generator*A)*s
  have hc : c≠0 := mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have ht := actual_compact_radial_paper_poisson_trace W hWc hWs K hK c hc
    (physicalQuotient C A s hs)
  change (∑' m : O, physicalQuotient C A s hs (Ideal.Quotient.mk _ m) *
    W (‖eisEmbedding m‖^2/K)) =
    (K/‖eisEmbedding c‖^2:ℝ) • ∑' H : O,
      (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
        quotientTrace c hc (Ideal.Quotient.mk _ H*r)) *
        paperRadialFourier W (K*‖eisEmbedding H‖^2/‖eisEmbedding c‖^2) at ht
  have hf (H : O) : (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
      quotientTrace c hc (Ideal.Quotient.mk _ H*r)) =
        (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
    rw [← actualPhysicalFourier_eq C A s hA hs H]
    exact (tsum_fintype _).symm
  simp_rw [physicalQuotient_mk, eisEmbedding_norm_sq_eq_absNorm_span, hf] at ht
  change (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) * W (elementNorm m/K)) =
    (K/elementNorm c:ℝ) • ∑' H : O,
      ((Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H) *
        paperRadialFourier W (K*elementNorm H/elementNorm c) at ht
  rw [ht]
  simp only [mul_assoc, tsum_mul_left, Complex.real_smul, Complex.ofReal_div]
  have hn : (elementNorm s:ℂ)≠0 := by
    simp only [elementNorm, Complex.ofReal_natCast]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  have hnorm : elementNorm c = elementNorm (C.generator*A) * elementNorm s := by
    dsimp only [elementNorm, c]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]
  simp only [← mul_assoc C.generator A s]
  rw [hnorm, Complex.ofReal_mul]
  simp only [elementNorm, Complex.ofReal_natCast] at hn ⊢
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
