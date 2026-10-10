import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRootCauchy
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetricLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_root_odd_square (x : Positive (T.CauchyQuotient hadd)) (n : ℕ) :
    (Positive.power (Positive.rootExponent (2*n+1)) x).1 *
      (Positive.power (Positive.rootExponent (2*n+1)) x).1 =
        (Positive.power (Positive.rootExponent n) x).1 := by
  change CFC.nnrpow x.1 _ * CFC.nnrpow x.1 _ = CFC.nnrpow x.1 _
  simp only [CFC.nnrpow_eq_pow]
  rw [← CFC.nnrpow_add (Positive.rootExponent_pos _) (Positive.rootExponent_pos _)]
  congr 1
  unfold Positive.rootExponent
  push_cast
  field_simp
  ring

lemma quotient_root_limit_projection (x : Positive (T.CauchyQuotient hadd)) (hx : ‖x.1‖ ≤ 1)
    (p : T.CauchyQuotient hadd)
    (hp : Tendsto (fun n => T.quotientDistance hadd hsqrt (Positive.power (Positive.rootExponent n) x).1 p) atTop (nhds 0)) :
    IsSelfAdjoint p ∧ p*p=p := by
  have hs := T.quotient_metric_limit_selfAdjoint hadd hsqrt hp
    (fun n => (Positive.power (Positive.rootExponent n) x).2.isSelfAdjoint)
  have hn : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2*n+1) tendsto_id
  have hsub := hp.comp hn
  have hmul := T.quotient_metric_limit_mul hadd hsqrt hsub hsub 1 zero_le_one
    (fun n => Positive.power_norm_le_one _ (Positive.rootExponent_pos (2*n+1)) x hx)
  simp only [T.quotient_root_odd_square] at hmul
  exact ⟨hs,T.quotient_metric_limit_unique hadd hsqrt _ _ _ hmul hp⟩

lemma exists_quotient_root_projection (x : Positive (T.CauchyQuotient hadd)) (hx : ‖x.1‖ ≤ 1) :
    ∃ p : T.CauchyQuotient hadd, ‖p‖ ≤ 1 ∧ IsSelfAdjoint p ∧ p*p=p ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (Positive.power (Positive.rootExponent n) x).1 p) atTop (nhds 0) := by
  obtain ⟨p,hpn,hp⟩ := T.exists_quotient_root_limit hadd hsqrt x hx
  obtain ⟨hsa,hid⟩ := T.quotient_root_limit_projection hadd hsqrt x hx p hp
  exact ⟨p,hpn,hsa,hid,hp⟩
end CuntzPureness.PositiveQuasitrace

end

end OAI
