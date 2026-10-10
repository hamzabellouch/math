import OAI.Analysis.LipschitzHilbert.Trees.SourceSimplexLp
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Bounded logarithmic-coefficient exhaustions preserve the uniform
Lp estimate. Integrability of the full power is proved by monotone
Lebesgue integration, before passing back to the real integral. -/

noncomputable section
open MeasureTheory Set Filter
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourceExhaustion (R : X → ℝ) (n : ℕ) : Set X := {x | R x ≤ (n:ℝ)}

theorem sourceExhaustion_measurable (R : X → ℝ) (hR : Measurable R) (n : ℕ) :
    MeasurableSet (sourceExhaustion R n) := measurableSet_le hR measurable_const

omit [MeasurableSpace X] in
theorem sourceExhaustion_mono (R : X → ℝ) : Monotone (sourceExhaustion R) := by
  intro n m hnm x hx
  change R x ≤ (n:ℝ) at hx
  change R x ≤ (m:ℝ)
  exact hx.trans (by exact_mod_cast hnm)

omit [MeasurableSpace X] in
theorem sourceExhaustion_covers (R : X → ℝ) : (⋃ n, sourceExhaustion R n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n,hn⟩ := exists_nat_ge (R x)
  exact mem_iUnion.mpr ⟨n,hn⟩

theorem source_lp_of_exhaustion (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
    (hF : Measurable F) (p C : ℝ) (hp : 0 < p) (hC : 0 ≤ C)
    (A : ℕ → Set X) (hmono : Monotone A)
    (hcover : (⋃ n, A n) = univ)
    (henergy : ∀ n, IntegrableOn (fun x => ‖F x‖^p) (A n) μ)
    (hbound : ∀ n, (∫ x in A n, ‖F x‖^p ∂μ)^(1/p) ≤ C) :
    Integrable (fun x => ‖F x‖^p) μ ∧ (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ C := by
  have hnonneg (x : X) : 0 ≤ ‖F x‖^p := Real.rpow_nonneg (norm_nonneg _) _
  have hpower (n : ℕ) : (∫ x in A n, ‖F x‖^p ∂μ) ≤ C^p := by
    have hI : 0 ≤ ∫ x in A n, ‖F x‖^p ∂μ := integral_nonneg hnonneg
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hI (1/p)) (hbound n) hp.le
    rw [← Real.rpow_mul hI,one_div_mul_cancel hp.ne',Real.rpow_one] at h
    exact h
  have hlin : (∫⁻ x, ENNReal.ofReal (‖F x‖^p) ∂μ) ≤ ENNReal.ofReal (C^p) := by
    have hi := setLIntegral_iUnion_of_directed (μ := μ)
      (fun x => ENNReal.ofReal (‖F x‖^p)) hmono.directed_le
    rw [hcover,Measure.restrict_univ] at hi
    rw [hi]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (henergy n) (Eventually.of_forall hnonneg)]
    exact ENNReal.ofReal_le_ofReal (hpower n)
  have hint : Integrable (fun x => ‖F x‖^p) μ := by
    refine ⟨(hF.norm.pow_const p).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg)).mpr
      (hlin.trans_lt ENNReal.ofReal_lt_top)
  have hglobal : (∫ x, ‖F x‖^p ∂μ) ≤ C^p := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp hlin
  refine ⟨hint,?_⟩
  have h := Real.rpow_le_rpow (integral_nonneg hnonneg) hglobal (one_div_pos.mpr hp).le
  rwa [← Real.rpow_mul hC,mul_one_div_cancel hp.ne',Real.rpow_one] at h

end LipschitzHilbert

end

end OAI
