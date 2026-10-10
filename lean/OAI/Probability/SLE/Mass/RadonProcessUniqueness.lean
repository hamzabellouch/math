import OAI.Probability.SLE.Mass.MassKernelUniqueness
import OAI.Probability.SLE.Mass.RadonTestDetermines

namespace OAI

/-! Countably many positive compact tests give one common full-measure event
on which all times of two random Radon processes agree. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [LocallyCompactSpace X] in
lemma compact_test_integral_pos_sub_neg (μ : Measure X) [μ.Regular] (f : C_c(X,ℝ)) :
    (∫ x, f x ∂μ) = (∫ x, (f ⊔ 0) x ∂μ)-(∫ x, ((-f) ⊔ 0) x ∂μ) := by
  rw [← integral_sub (f ⊔ 0).integrable ((-f) ⊔ 0).integrable]
  apply integral_congr_ae
  filter_upwards [] with x
  change f x = max (f x) 0-max (-f x) 0
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]

theorem random_radon_process_eq_of_positive_tests
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : LocalTestFamily X) (N M : ℝ≥0 → Ω → Measure X)
    (hNr : ∀ t ω, (N t ω).Regular) (hMr : ∀ t ω, (M t ω).Regular)
    (htest : ∀ f : C_c(X,ℝ), (∀ x, 0 ≤ f x) →
      ∀ᵐ ω ∂P, ∀ t, (∫ x, f x ∂N t ω) = ∫ x, f x ∂M t ω) :
    ∀ᵐ ω ∂P, ∀ t, N t ω = M t ω := by
  have hp (j : ℕ) := htest (D.test j ⊔ 0) (fun x => le_max_right _ _)
  have hn (j : ℕ) := htest ((-D.test j) ⊔ 0) (fun x => le_max_right _ _)
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hn] with ω hωp hωn
  intro t
  let := hNr t ω
  let := hMr t ω
  apply D.measure_eq_of_test_integrals
  intro j
  rw [compact_test_integral_pos_sub_neg (N t ω) (D.test j),
    compact_test_integral_pos_sub_neg (M t ω) (D.test j),hωp j t,hωn j t]

end SLEExactGauge

end

end OAI
