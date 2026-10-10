import OAI.Probability.DilutedSpin.RootOverlapVariance

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

noncomputable def mixedDeviation (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) : ℝ :=
  ∫ z, (P z).expect (fun w => |F z w-(∫ y, (P y).expect (F y) ∂μ)|) ∂μ

lemma mixedDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) :
    0 ≤ mixedDeviation μ Ω P F := integral_nonneg (fun z => (P z).expect_nonneg (fun _ => abs_nonneg _))

lemma expect_centered_sq (Ω : Type) [Fintype Ω] (P : FiniteLaw Ω) (F : Ω → ℝ) (c : ℝ) :
    P.expect (fun w => (F w-c)^2)=P.expect (fun w => (F w)^2)-2*c*P.expect F+c^2 := by
  calc
    _ = P.expect (fun w => (F w)^2-(2*c)*F w+c^2) := P.expect_congr (fun w => by ring)
    _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]

lemma mixedDeviation_le_variance (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (habs : Integrable (fun z => (P z).expect (fun w => |F z w-(∫ y, (P y).expect (F y) ∂μ)|)) μ)
    {t : ℝ} (ht : 0<t) :
    mixedDeviation μ Ω P F ≤ mixedVariance μ Ω P F/(2*t)+t/2 := by
  let c := ∫ y, (P y).expect (F y) ∂μ
  have hi : Integrable (fun z => (P z).expect (fun w => (F z w-c)^2)) μ := by
    simp_rw [expect_centered_sq]
    exact (hFsq.sub (hF.const_mul (2*c))).add (integrable_const (c^2))
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  unfold mixedDeviation
  calc
    _ ≤ ∫ z, (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2 ∂μ := by
      apply integral_mono habs ((hi.div_const (2*t)).add (integrable_const (t/2)))
      intro z
      change (P z).expect (fun w => |F z w-c|) ≤ (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2
      rw [← expect_div,← expect_const (P z) (t/2),← expect_add]
      apply expect_mono
      intro w
      have hs := sq_nonneg (|F z w-c|-t)
      have ha := sq_abs (F z w-c)
      apply (mul_le_mul_iff_left₀ (by positivity : 0<2*t)).mp
      calc
        |F z w-c| * (2*t) ≤ (F z w-c)^2+t^2 := by nlinarith
        _ = ((F z w-c)^2/(2*t)+t/2)*(2*t) := by field_simp
    _ = _ := by rw [integral_add (hi.div_const (2*t)) (integrable_const (t/2)),integral_div,integral_const]; simp only [probReal_univ,one_smul]; rfl

end DilutedSpinGlass.FiniteLaw

end

end OAI
