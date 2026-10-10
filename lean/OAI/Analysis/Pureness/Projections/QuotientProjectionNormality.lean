import OAI.Analysis.Pureness.Projections.QuotientProjectionJoins

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_projection_value_mono {p q : T.CauchyQuotient hadd}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q) :
    (T.quotientValue hadd hsqrt p).re ≤ (T.quotientValue hadd hsqrt q).re :=
  (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt
    (x := ⟨p,hp.nonneg⟩) (y := ⟨q,hq.nonneg⟩) hpq)).1

theorem exists_quotient_directed_projection_sup
    (S : Set (T.CauchyQuotient hadd)) (hne : S.Nonempty)
    (hproj : ∀ p ∈ S, IsStarProjection p) (hdir : DirectedOn (· ≤ ·) S) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ q, IsStarProjection q → (∀ a ∈ S, a ≤ q) → p ≤ q) ∧
      (T.quotientValue hadd hsqrt p).re = sSup ((fun q => (T.quotientValue hadd hsqrt q).re) '' S) := by
  let v (p : T.CauchyQuotient hadd) := (T.quotientValue hadd hsqrt p).re
  let V := v '' S
  have hvne : V.Nonempty := hne.image v
  have hb : BddAbove V := by
    refine ⟨v 1, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact T.quotient_projection_value_mono hadd hsqrt (hproj p hp) (IsStarProjection.one _)
      (sub_nonneg.mp (hproj p hp).one_sub.nonneg)
  have hvle (p : S) : v p.1 ≤ sSup V := le_csSup hb ⟨p.1, p.2, rfl⟩
  have happrox (n : ℕ) : ∃ p : S, sSup V-1/((n:ℝ)+1) < v p.1 := by
    obtain ⟨r, ⟨p, hp, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hvne
      (show sSup V-1/((n:ℝ)+1) < sSup V from sub_lt_self _ (by positivity))
    exact ⟨⟨p, hp⟩, hr⟩
  choose a ha using happrox
  have hjoin (p q : S) : ∃ r : S, p.1 ≤ r.1 ∧ q.1 ≤ r.1 := by
    obtain ⟨r, hr, hpr, hqr⟩ := hdir p.1 p.2 q.1 q.2
    exact ⟨⟨r, hr⟩, hpr, hqr⟩
  choose join hj₁ hj₂ using hjoin
  let u : ℕ → S := fun n => Nat.rec (a 0) (fun n p => join p (a (n+1))) n
  have hmono : Monotone (fun n => (u n).1) :=
    monotone_nat_of_le_succ (fun n => hj₁ (u n) (a (n+1)))
  have hau (n : ℕ) : (a n).1 ≤ (u n).1 := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hj₂ (u n) (a (n+1))
  have hlow (n : ℕ) : sSup V-1/((n:ℝ)+1) ≤ v (u n).1 :=
    (ha n).le.trans (T.quotient_projection_value_mono hadd hsqrt
      (hproj _ (a n).2) (hproj _ (u n).2) (hau n))
  have hvlim : Tendsto (fun n => v (u n).1) atTop (nhds (sSup V)) := by
    have hlo : Tendsto (fun n : ℕ => sSup V-1/((n:ℝ)+1)) atTop (nhds (sSup V-0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlo) tendsto_const_nhds
      hlow (fun n => hvle (u n))
  obtain ⟨p, hp, hlim, hup, hmin⟩ := T.exists_quotient_projection_sup hadd hsqrt
    (fun n => (u n).1) (fun n => hproj _ (u n).2) hmono
  have value_limit {w : ℕ → T.CauchyQuotient hadd} {q : T.CauchyQuotient hadd}
      (hw : ∀ n, IsStarProjection (w n))
      (hl : Tendsto (fun n => T.quotientDistance hadd hsqrt (w n) q) atTop (nhds 0)) :
      Tendsto (fun n => v (w n)) atTop (nhds (v q)) :=
    Complex.continuous_re.tendsto _ |>.comp
      (T.quotientValue_bounded_metric_limit hadd hsqrt hl 1 zero_le_one
        (fun n => T.quotient_projection_norm_le_one hadd (hw n)))
  have hvp : v p = sSup V := tendsto_nhds_unique
    (value_limit (fun n => hproj _ (u n).2) hlim) hvlim
  refine ⟨p, hp, ?_, (fun q hq hSq => hmin q hq (fun n => hSq _ (u n).2)), hvp⟩
  intro q hq
  let w : ℕ → S := fun n => Nat.rec (join ⟨q,hq⟩ (u 0))
    (fun n r => join r (u (n+1))) n
  have hwm : Monotone (fun n => (w n).1) :=
    monotone_nat_of_le_succ (fun n => hj₁ (w n) (u (n+1)))
  have huw (n : ℕ) : (u n).1 ≤ (w n).1 := by
    cases n with
    | zero => exact hj₂ ⟨q,hq⟩ (u 0)
    | succ n => exact hj₂ (w n) (u (n+1))
  obtain ⟨r, hr, hrlim, hwr, _⟩ := T.exists_quotient_projection_sup hadd hsqrt
    (fun n => (w n).1) (fun n => hproj _ (w n).2) hwm
  have hpr : p ≤ r := hmin r hr (fun n => (huw n).trans (hwr n))
  have hvr : v r ≤ sSup V := le_of_tendsto
    (value_limit (fun n => hproj _ (w n).2) hrlim) (Filter.Eventually.of_forall (fun n => hvle (w n)))
  have heq : p = r := T.quotient_projection_eq_of_le_of_value_le hadd hsqrt hp hr hpr
    (by change v r ≤ v p; rw [hvp]; exact hvr)
  exact ((hj₁ ⟨q,hq⟩ (u 0)).trans (hwr 0)).trans_eq heq.symm

theorem quotientValue_directed_projection_sup
    (S : Set (T.CauchyQuotient hadd)) (hne : S.Nonempty)
    (hproj : ∀ p ∈ S, IsStarProjection p) (hdir : DirectedOn (· ≤ ·) S)
    (p : T.CauchyQuotient hadd) (hp : IsStarProjection p)
    (hup : ∀ q ∈ S, q ≤ p)
    (hmin : ∀ q, IsStarProjection q → (∀ a ∈ S, a ≤ q) → p ≤ q) :
    (T.quotientValue hadd hsqrt p).re = sSup ((fun q => (T.quotientValue hadd hsqrt q).re) '' S) := by
  obtain ⟨r, hr, hur, hmr, hv⟩ := T.exists_quotient_directed_projection_sup hadd hsqrt S hne hproj hdir
  have he : p = r := le_antisymm (hmin r hr hur) (hmr p hp hup)
  exact he ▸ hv
end CuntzPureness.PositiveQuasitrace

end

end OAI
