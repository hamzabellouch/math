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

include hsqrt in

lemma exists_quotient_annihilator_maximum (S : Set (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧ (∀ a ∈ S, a*p=0) ∧
      ∀ q, IsStarProjection q → (∀ a ∈ S, a*q=0) → q ≤ p := by
  let P := {p : T.CauchyQuotient hadd // IsStarProjection p ∧ ∀ a ∈ S, a*p=0}
  let v (p : T.CauchyQuotient hadd) := (T.quotientValue hadd hsqrt p).re
  let V : Set ℝ := Set.range (fun p : P => v p.1)
  have hne : V.Nonempty := ⟨v 0, ⟨⟨0,IsStarProjection.zero _,by simp⟩,rfl⟩⟩
  have hb : BddAbove V := by
    refine ⟨v 1,?_⟩
    rintro _ ⟨p,rfl⟩
    exact (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt
      (x := ⟨p.1,p.2.1.nonneg⟩) (y := ⟨1,zero_le_one⟩)
      (show p.1 ≤ 1 from sub_nonneg.mp p.2.1.one_sub.nonneg))).1
  have hvle (p : P) : v p.1 ≤ sSup V := le_csSup hb ⟨p,rfl⟩
  have happrox (n : ℕ) : ∃ p : P, sSup V-1/((n:ℝ)+1) < v p.1 := by
    have hlt : sSup V-1/((n:ℝ)+1) < sSup V := sub_lt_self _ (by positivity)
    obtain ⟨r,⟨p,rfl⟩,hp⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨p,hp⟩
  choose a ha using happrox
  have hjoin (p q : P) : ∃ r : P, p.1 ≤ r.1 ∧ q.1 ≤ r.1 := by
    obtain ⟨r,hr,hpr,hqr,_,hann⟩ := T.exists_quotient_projection_join hadd hsqrt p.2.1 q.2.1
    exact ⟨⟨r,hr,fun x hx => (hann x).mpr ⟨p.2.2 x hx,q.2.2 x hx⟩⟩,hpr,hqr⟩
  choose join hj₁ hj₂ using hjoin
  let u : ℕ → P := fun n => Nat.rec (a 0) (fun n p => join p (a (n+1))) n
  have hstep (n : ℕ) : (u n).1 ≤ (u (n+1)).1 := hj₁ (u n) (a (n+1))
  have hmono : Monotone (fun n => (u n).1) := monotone_nat_of_le_succ hstep
  have hau (n : ℕ) : (a n).1 ≤ (u n).1 := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hj₂ (u n) (a (n+1))
  have hlow (n : ℕ) : sSup V-1/((n:ℝ)+1) ≤ v (u n).1 := (ha n).le.trans
    (Complex.le_def.mp (T.quotientValue_positive_mono hadd hsqrt
      (x := ⟨(a n).1,(a n).2.1.nonneg⟩) (y := ⟨(u n).1,(u n).2.1.nonneg⟩) (hau n))).1
  have hvlim : Tendsto (fun n => v (u n).1) atTop (nhds (sSup V)) := by
    have hlo : Tendsto (fun n : ℕ => sSup V-1/((n:ℝ)+1)) atTop (nhds (sSup V-0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [sub_zero] at hlo
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds hlow (fun n => hvle (u n))
  obtain ⟨p,hp,hlim,_,_⟩ := T.exists_quotient_projection_sup hadd hsqrt
    (fun n => (u n).1) (fun n => (u n).2.1) hmono
  have hpann : ∀ x ∈ S, x*p=0 := by
    intro x hx
    have hc : Tendsto (fun _ : ℕ => T.quotientDistance hadd hsqrt x x) atTop (nhds 0) := by
      simp only [T.quotientDistance_self]; exact tendsto_const_nhds
    have ht := T.quotient_metric_limit_mul hadd hsqrt hc hlim ‖x‖ (norm_nonneg _) (fun _ => le_rfl)
    simp only [(u _).2.2 x hx] at ht
    have he : T.quotientDistance hadd hsqrt 0 (x*p)=0 := tendsto_nhds_unique tendsto_const_nhds ht
    exact ((T.quotientDistance_eq_zero_iff hadd hsqrt _ _).mp he).symm
  have hvp : v p=sSup V := by
    have ht := (Complex.continuous_re.tendsto _).comp
      (T.quotientValue_bounded_metric_limit hadd hsqrt hlim 1 zero_le_one
        (fun n => T.quotient_projection_norm_le_one hadd (u n).2.1))
    exact tendsto_nhds_unique ht hvlim
  refine ⟨p,hp,hpann,?_⟩
  intro q hq hqann
  obtain ⟨r,hr,hpr,hqr,_,hann⟩ := T.exists_quotient_projection_join hadd hsqrt hp hq
  have hrann : ∀ x ∈ S, x*r=0 := fun x hx => (hann x).mpr ⟨hpann x hx,hqann x hx⟩
  have hvr : v r ≤ v p := by rw [hvp]; exact hvle ⟨r,hr,hrann⟩
  have heq := T.quotient_projection_eq_of_le_of_value_le hadd hsqrt hp hr hpr hvr
  exact hqr.trans_eq heq.symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
