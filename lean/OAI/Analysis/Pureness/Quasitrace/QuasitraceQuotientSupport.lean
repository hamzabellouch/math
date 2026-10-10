import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRootProjection
import OAI.Analysis.Pureness.Divisibility.HereditaryApproximateUnit

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_metric_limit_commute {u : ℕ → T.CauchyQuotient hadd} {x : T.CauchyQuotient hadd}
    (hu : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (y : T.CauchyQuotient hadd) (hc : ∀ n, Commute (u n) y) : Commute x y := by
  have hy : Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt y y) atTop (nhds 0) := by
    simpa only [T.quotientDistance_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
  have hl := T.quotient_metric_limit_mul hadd hsqrt hu hy C hC hb
  have hr := T.quotient_metric_limit_mul hadd hsqrt hy hu ‖y‖ (norm_nonneg _) (fun _ => le_rfl)
  simp only [(hc _).eq] at hl
  exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ hl hr

lemma quotient_normalizedRoot_eq (h : Positive (T.CauchyQuotient hadd)) (n : ℕ) :
    normalizedRoot h.1 n =
      (Positive.power (Positive.rootExponent n) ⟨normalizePositive h.1,normalizePositive_nonneg _ h.2⟩).1 := by
  simp only [normalizedRoot,Positive.power,Positive.rootExponent,one_div]

lemma exists_quotient_support_projection (h : Positive (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, ‖p‖ ≤ 1 ∧ IsSelfAdjoint p ∧ p*p=p ∧
      p*h.1=h.1 ∧ h.1*p=h.1 ∧
      (∀ c, c ∈ hereditaryCarrier h.1 → p*c=c) ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (normalizedRoot h.1 n) p) atTop (nhds 0) := by
  let a : Positive (T.CauchyQuotient hadd) := ⟨normalizePositive h.1,normalizePositive_nonneg _ h.2⟩
  obtain ⟨p,hpn,hsa,hid,hp⟩ := T.exists_quotient_root_projection hadd hsqrt a (normalizePositive_norm_le _)
  have hp' : Tendsto (fun n => T.quotientDistance hadd hsqrt (normalizedRoot h.1 n) p) atTop (nhds 0) := by
    simpa only [T.quotient_normalizedRoot_eq] using hp
  have hb (n : ℕ) : ‖normalizedRoot h.1 n‖ ≤ 1 := by
    rw [T.quotient_normalizedRoot_eq]
    exact Positive.power_norm_le_one _ (Positive.rootExponent_pos n) a (normalizePositive_norm_le _)
  have he (c : T.CauchyQuotient hadd)
      (hc : Tendsto (fun n => normalizedRoot h.1 n*c) atTop (nhds c)) : p*c=c := by
    have hct : Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt c c) atTop (nhds 0) := by
      simp only [T.quotientDistance_self]; exact tendsto_const_nhds
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _
      (T.quotient_metric_limit_mul hadd hsqrt hp' hct 1 zero_le_one hb)
      (T.quotient_norm_limit_is_metric_limit hadd hsqrt hc)
  have hph := he h.1 (normalizedRoot_mul_self_tendsto h.1 h.2)
  have hhp : h.1*p=h.1 := by
    have hstar := congrArg star hph
    simpa only [star_mul,hsa.star_eq,h.2.isSelfAdjoint.star_eq] using hstar
  exact ⟨p,hpn,hsa,hid,hph,hhp,fun c hc => he c
    (normalizedRoot_mul_hereditary_tendsto h.1 h.2 c hc),hp'⟩
end CuntzPureness.PositiveQuasitrace

end

end OAI
