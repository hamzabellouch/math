import OAI.Analysis.Pureness.Projections.QuotientMatchLimits
import Mathlib.Order.Zorn

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

theorem quotient_match_chain_bounded
    {p q : T.CauchyQuotient hadd} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (S : Set (ProjectionMatch p q)) (hS : IsChain (· ≤ ·) S) (hne : S.Nonempty) :
    BddAbove S := by
  let f (u : ProjectionMatch p q) := (T.quotientValue hadd hsqrt (star u.val*u.val)).re
  have hf : Monotone f := fun u v h =>
    T.quotient_projection_value_mono hadd hsqrt u.initial v.initial h.1
  let V := f '' S
  have hvne : V.Nonempty := hne.image f
  have hb : BddAbove V := by
    refine ⟨(T.quotientValue hadd hsqrt q).re,?_⟩
    rintro _ ⟨u,hu,rfl⟩
    exact T.quotient_projection_value_mono hadd hsqrt u.initial hq u.initial_le
  have hvle (u : S) : f u.1 ≤ sSup V := le_csSup hb ⟨u.1,u.2,rfl⟩
  have happrox (n : ℕ) : ∃ u : S, sSup V-1/((n:ℝ)+1) < f u.1 := by
    obtain ⟨_,⟨u,hu,rfl⟩,hr⟩ := exists_lt_of_lt_csSup hvne
      (show sSup V-1/((n:ℝ)+1)<sSup V from sub_lt_self _ (by positivity))
    exact ⟨⟨u,hu⟩,hr⟩
  choose a ha using happrox
  have hjoin (u v : S) : ∃ w : S, u.1 ≤ w.1 ∧ v.1 ≤ w.1 := by
    rcases hS.total u.2 v.2 with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩
  choose join hj₁ hj₂ using hjoin
  let u : ℕ → S := fun n => Nat.rec (a 0) (fun n v => join v (a (n+1))) n
  have hm : Monotone (fun n => (u n).1) :=
    monotone_nat_of_le_succ (fun n => hj₁ (u n) (a (n+1)))
  have hau (n : ℕ) : (a n).1 ≤ (u n).1 := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hj₂ (u n) (a (n+1))
  have hvlim : Tendsto (fun n => f (u n).1) atTop (nhds (sSup V)) := by
    have hlo : Tendsto (fun n : ℕ => sSup V-1/((n:ℝ)+1)) atTop (nhds (sSup V-0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlo) tendsto_const_nhds
      (fun n => (ha n).le.trans (hf (hau n))) (fun n => hvle (u n))
  obtain ⟨w,_,hup,hmin,hwlim⟩ := T.exists_quotient_match_sequence_sup hadd hsqrt hp hq
    (fun n => (u n).1) hm
  have hwv : f w=sSup V := tendsto_nhds_unique hwlim hvlim
  refine ⟨w,?_⟩
  intro x hx
  by_cases h : ∃ n, x ≤ (u n).1
  · obtain ⟨n,hn⟩ := h
    exact hn.trans (hup n)
  · have hux (n : ℕ) : (u n).1 ≤ x :=
      (hS.total (u n).2 hx).resolve_right (fun hh => h ⟨n,hh⟩)
    have hwx := hmin x hux
    have he : w=x := T.quotient_match_eq_of_le_of_value_le hadd hsqrt hwx
      (show f x ≤ f w by rw [hwv]; exact hvle ⟨x,hx⟩)
    exact le_of_eq he.symm

include hsqrt in

theorem exists_quotient_maximal_match
    {p q : T.CauchyQuotient hadd} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ u : ProjectionMatch p q, ∀ v, u ≤ v → v ≤ u := by
  let : Nonempty (ProjectionMatch p q) := ⟨ProjectionMatch.zero hp hq⟩
  exact exists_maximal_of_nonempty_chains_bounded
    (fun S hS hne => T.quotient_match_chain_bounded hadd hsqrt hp hq S hS hne) le_trans
end CuntzPureness.PositiveQuasitrace

end

end OAI
