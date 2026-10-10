import OAI.Analysis.Pureness.Projections.PartialIsometryMatch
import OAI.Analysis.Pureness.Projections.QuotientPartialIsometryLimits
import OAI.Analysis.Pureness.Projections.QuotientProjectionNormality

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

theorem exists_quotient_match_sequence_sup
    {p q : T.CauchyQuotient hadd} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : ℕ → ProjectionMatch p q) (hm : Monotone u) :
    ∃ w : ProjectionMatch p q,
      Tendsto (fun n => T.quotientDistance hadd hsqrt (u n).val w.val) atTop (nhds 0) ∧
      (∀ n, u n ≤ w) ∧ (∀ v, (∀ n, u n ≤ v) → w ≤ v) ∧
      Tendsto (fun n => (T.quotientValue hadd hsqrt (star (u n).val*(u n).val)).re)
        atTop (nhds (T.quotientValue hadd hsqrt (star w.val*w.val)).re) := by
  have hb (n : ℕ) : ‖(u n).val‖ ≤ 1 := partial_isometry_norm_le_one _ (u n).initial
  obtain ⟨v,hv,hl,hext,hup⟩ := T.exists_quotient_compatible_partial_isometry_limit hadd hsqrt
    (fun n => (u n).val) (fun n => (u n).initial)
    (fun m n h => (hm h).1) (fun m n h => (hm h).2)
  have hs := T.quotient_metric_limit_star hadd hsqrt hl
  have hei := T.quotient_metric_limit_mul hadd hsqrt hs hl 1 zero_le_one
    (fun n => by simpa only [norm_star] using hb n)
  have hgr := T.quotient_metric_limit_mul hadd hsqrt hl hs 1 zero_le_one hb
  have hg : IsStarProjection (v*star v) :=
    (partial_isometry_range_projection v (star v*v) (partial_isometry_mul_initial v hv) rfl
      1 (IsStarProjection.one _) (one_mul v)).1
  have hc (a : T.CauchyQuotient hadd) :
      Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt a a) atTop (nhds 0) := by
    simp only [T.quotientDistance_self]; exact tendsto_const_nhds
  have hbound {a : ℕ → T.CauchyQuotient hadd} {b c : T.CauchyQuotient hadd}
      (ha : ∀ n, IsStarProjection (a n)) (hbc : IsStarProjection b) (hcc : IsStarProjection c)
      (hlim : Tendsto (fun n => T.quotientDistance hadd hsqrt (a n) b) atTop (nhds 0))
      (hle : ∀ n, a n ≤ c) : b ≤ c := by
    apply (hbc.le_iff_mul_eq_left hcc).mpr
    have hlm := T.quotient_metric_limit_mul hadd hsqrt hlim (hc c) 1 zero_le_one
      (fun n => T.quotient_projection_norm_le_one hadd (ha n))
    simp only [((ha _).le_iff_mul_eq_left hcc).mp (hle _)] at hlm
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ hlm hlim
  let w : ProjectionMatch p q := ⟨v,hv,hg,
    hbound (fun n => (u n).initial) hv hq hei (fun n => (u n).initial_le),
    hbound (fun n => (u n).range) hg hp hgr (fun n => (u n).range_le)⟩
  refine ⟨w,hl,(fun n => ⟨hup n,hext n⟩),?_,?_⟩
  · intro x hx
    refine ⟨hbound (fun n => (u n).initial) hv x.initial hei (fun n => (hx n).1),?_⟩
    have hlm := T.quotient_metric_limit_mul hadd hsqrt (hc x.val) hei 1 zero_le_one
      (fun _ => partial_isometry_norm_le_one _ x.initial)
    simp only [(hx _).2] at hlm
    exact T.quotient_metric_limit_unique hadd hsqrt _ _ _ hlm hl
  · exact Complex.continuous_re.tendsto _ |>.comp
      (T.quotientValue_bounded_metric_limit hadd hsqrt hei 1 zero_le_one
        (fun n => T.quotient_projection_norm_le_one hadd (u n).initial))

theorem quotient_match_eq_of_le_of_value_le
    {p q : T.CauchyQuotient hadd} {u v : ProjectionMatch p q} (hle : u ≤ v)
    (hv : (T.quotientValue hadd hsqrt (star v.val*v.val)).re ≤
      (T.quotientValue hadd hsqrt (star u.val*u.val)).re) : u=v := by
  have he := T.quotient_projection_eq_of_le_of_value_le hadd hsqrt u.initial v.initial hle.1 hv
  apply ProjectionMatch.ext
  have hx := hle.2
  rw [he,partial_isometry_mul_initial v.val v.initial] at hx
  exact hx.symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
