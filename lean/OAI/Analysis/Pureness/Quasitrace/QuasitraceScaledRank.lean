import OAI.Analysis.Pureness.Quasitrace.QuasitraceNormalization

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralQuasitraceFamily_scaled_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (c : ℝ≥0) (n : ℕ) (M : Positive (FinMatrix A n)) :
    Filter.Tendsto (fun k => ENNReal.ofReal
      ((((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n).scale c
        (Positive.power (Positive.rootExponent k) M).1).re)) Filter.atTop
      (nhds ((c : ℝ≥0∞)*d (finitePositiveClass n M))) := by
  have h := (ENNReal.continuous_const_mul (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top).continuousAt.tendsto.comp
    (finiteSpectralQuasitraceFamily_root_rank d hd hlsc hfinite n M)
  have he (k : ℕ) : ENNReal.ofReal
      ((((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n).scale c
        (Positive.power (Positive.rootExponent k) M).1).re) =
      (c : ℝ≥0∞)*ENNReal.ofReal
        (((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n
          (Positive.power (Positive.rootExponent k) M).1).re) := by
    change ENNReal.ofReal (((c : ℂ)*_).re) = _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact (ENNReal.ofReal_mul c.2).trans
      (congrArg (fun v : ℝ≥0∞ => v*ENNReal.ofReal
        (((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n
          (Positive.power (Positive.rootExponent k) M).1).re)) ENNReal.ofReal_coe_nnreal)
  simp only [he]
  change Filter.Tendsto (fun k => (c : ℝ≥0∞)*ENNReal.ofReal
    (((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n
      (Positive.power (Positive.rootExponent k) M).1).re)) Filter.atTop _ at h
  exact h
end CuntzPureness

end

end OAI
