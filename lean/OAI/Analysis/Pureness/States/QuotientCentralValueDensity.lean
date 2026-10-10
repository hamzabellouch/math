import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientValueMetricLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

theorem scaled_quotientValue_mul_of_embedding (c k : ℂ) (p : T.CauchyQuotient hadd)
    (he : ∀ a : D, c*T.quotientValue hadd hsqrt (p*T.quotientEmbedding hadd a) =
      k*(c*T.quotientValue hadd hsqrt (T.quotientEmbedding hadd a)))
    (x : T.CauchyQuotient hadd) :
    c*T.quotientValue hadd hsqrt (p*x) = k*(c*T.quotientValue hadd hsqrt x) := by
  obtain ⟨u, rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  let v := fun n => T.quotientEmbedding hadd (u.1 n)
  have hv := T.quotientEmbedding_representative_tendsto hadd hsqrt u
  have hb (n : ℕ) : ‖v n‖ ≤ ‖u.1‖ :=
    (NonUnitalStarAlgHom.norm_apply_le (T.quotientEmbedding hadd) (u.1 n)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 n)
  have hpv := T.quotient_metric_limit_mul hadd hsqrt
    (u := fun _ => p) (x := p) (by
      simp only [T.quotientDistance_self]
      exact tendsto_const_nhds) hv ‖p‖ (norm_nonneg _) (fun _ => le_rfl)
  have hpb (n : ℕ) : ‖p*v n‖ ≤ ‖p‖*‖u.1‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))
  have hl := (T.quotientValue_bounded_metric_limit hadd hsqrt hpv
    (‖p‖*‖u.1‖) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpb).const_mul c
  have hr := ((T.quotientValue_bounded_metric_limit hadd hsqrt hv
    ‖u.1‖ (norm_nonneg _) hb).const_mul c).const_mul k
  have heq : (fun n => c*T.quotientValue hadd hsqrt (p*v n)) =
      (fun n => k*(c*T.quotientValue hadd hsqrt (v n))) := by
    funext n
    exact he (u.1 n)
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr
end CuntzPureness.PositiveQuasitrace

end

end OAI
