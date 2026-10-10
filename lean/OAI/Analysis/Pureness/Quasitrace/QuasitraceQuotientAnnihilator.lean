import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSupport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma hereditary_mul_eq_zero {h c y : T.CauchyQuotient hadd}
    (hc : c ∈ hereditaryCarrier h) (hy : h*y=0) : c*y=0 := by
  have hz : IsClosed {c : T.CauchyQuotient hadd | c*y=0} :=
    isClosed_eq (continuous_id.mul continuous_const) continuous_const
  apply (closure_minimal ?_ hz) hc
  rintro _ ⟨w,rfl⟩
  change (h*w*h)*y=0
  rw [mul_assoc (h*w),hy,mul_zero]

lemma quotient_normalizedRoot_commute (h : Positive (T.CauchyQuotient hadd))
    (y : T.CauchyQuotient hadd) (hy : Commute h.1 y) (n : ℕ) : Commute (normalizedRoot h.1 n) y := by
  have hn : Commute (normalizePositive h.1) y := hy.smul_left (‖h.1‖⁻¹ : ℝ)
  rw [T.quotient_normalizedRoot_eq,T.quotient_root_eq_cfc]
  exact hn.cfc_real _

include hsqrt in

lemma exists_quotient_support_annihilator (h : Positive (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, IsSelfAdjoint p ∧ p*p=p ∧ p*h.1=h.1 ∧
      (∀ y, h.1*y=0 ↔ p*y=0) ∧
      (∀ y, Commute h.1 y → Commute p y) := by
  obtain ⟨p,hpn,hsa,hid,hph,hhp,hher,hp⟩ := T.exists_quotient_support_projection hadd hsqrt h
  have hb (n : ℕ) : ‖normalizedRoot h.1 n‖ ≤ 1 := by
    rw [T.quotient_normalizedRoot_eq]
    exact Positive.power_norm_le_one _ (Positive.rootExponent_pos n) _ (normalizePositive_norm_le _)
  refine ⟨p,hsa,hid,hph,?_,?_⟩
  · intro y
    constructor
    · intro hy
      have hzero (n : ℕ) : normalizedRoot h.1 n*y=0 :=
        T.hereditary_mul_eq_zero hadd (normalizedRoot_mem_hereditary h.2 (self_mem_hereditary _ h.2) h.2 n) hy
      have hyc : Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt y y) atTop (nhds 0) := by
        simp only [T.quotientDistance_self]; exact tendsto_const_nhds
      have ht := T.quotient_metric_limit_mul hadd hsqrt hp hyc 1 zero_le_one hb
      simp only [hzero] at ht
      have he : T.quotientDistance hadd hsqrt 0 (p*y)=0 := tendsto_nhds_unique tendsto_const_nhds ht
      exact ((T.quotientDistance_eq_zero_iff hadd hsqrt 0 (p*y)).mp he).symm
    · intro hy
      calc
        h.1*y = (h.1*p)*y := by rw [hhp]
        _ = 0 := by rw [mul_assoc,hy,mul_zero]
  · intro y hy
    exact T.quotient_metric_limit_commute hadd hsqrt hp 1 zero_le_one hb y
      (fun n => T.quotient_normalizedRoot_commute hadd h y hy n)
end CuntzPureness.PositiveQuasitrace

end

end OAI
