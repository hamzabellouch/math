import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedPartial
import OAI.Combinatorics.KMedian.Rounding.ExceptionalStar
import OAI.Combinatorics.KMedian.Probability.SupportedLaw

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T : Type} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

 theorem sum_indicator (S : Finset T) : (∑ t, indicator S t)=(S.card:ℝ) := by
  simp only [indicator, sum_boole, filter_univ_mem]

theorem negative_star_law (D : E → Finset T) (a p : E → ℝ) (m : E → ℕ)
    (ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hneg : ∀ e, a e < ((D e).card:ℝ))
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (S : Ω → E → Finset T) (O : Ω → E → ℝ),
        (∀ ω, 0 < μ.weight ω →
          (∀ e, S ω e ⊆ D e) ∧
          (∀ e, O ω e=(m e:ℝ) ∨ O ω e=(m e:ℝ)+1) ∧
          (∀ e t, (m e:ℝ)+indicator (S ω e) t ≤ O ω e) ∧
          (∑ e, (a e*O ω e-(((D e).card:ℝ)*(m e:ℝ)+((S ω e).card:ℝ)))) ≤
            (∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))+2) ∧
        (∀ e t, μ.prob (fun ω => t ∈ S ω e)=if t ∈ D e then p e else 0) ∧
        (∀ e f, e ≠ f → ∀ t u,
          μ.expect (fun ω => indicator (S ω e) t*indicator (S ω f) u) ≤
            (if t ∈ D e then p e else 0)*(if u ∈ D f then p f else 0)) := by
  classical
  let β := fun e => ((D e).card:ℝ)-a e
  obtain ⟨Ξ,instΞ,hex⟩ := exists_partial_law p β hp0 hp1 (fun e => sub_pos.mpr (hneg e))
  let := instΞ
  obtain ⟨ν,Q,hs,hm,hpair⟩ := hex
  let Ξ' := {ξ : Ξ // 0 < ν.weight ξ}
  let ν' : FiniteLaw Ξ' := ν.supported
  have hq0 : ∀ ξ : Ξ', ∀ e, 0 ≤ Q ξ.1 e := fun ξ => (hs ξ.1 ξ.2).1
  have hq1 : ∀ ξ : Ξ', ∀ e, Q ξ.1 e ≤ 1 := fun ξ => (hs ξ.1 ξ.2).2.1
  choose κ hκ hκmean hκpair using (fun ξ : Ξ' =>
    exceptional_activation_law D (Q ξ.1) a (hq0 ξ) (hq1 ξ) ha0 ha1 (hs ξ.1 ξ.2).2.2.1)
  let μ := ν'.joint κ
  refine ⟨Ξ' × (E → Finset T),inferInstance,μ,fun ω => ω.2,
    fun ω e => (m e:ℝ)+upperBit (Q ω.1.1 e),?_,?_,?_⟩
  · intro ω hω
    have hk := (FiniteLaw.support_joint ν' κ ω hω).2
    have hprop := hκ ω.1 ω.2 hk
    refine ⟨hprop.1,?_,?_,?_⟩
    · intro e
      dsimp only
      unfold upperBit
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl (add_zero _)
    · intro e t
      exact add_le_add le_rfl (hprop.2.1 e t)
    · have hw : (∑ e, (a e-((D e).card:ℝ))*Q ω.1.1 e)=
          ∑ e, (a e-((D e).card:ℝ))*p e := by
        have hh := (hs ω.1.1 ω.1.2).2.2.2
        have hq : ∀ x : E → ℝ, (∑ e, (a e-((D e).card:ℝ))*x e)= -(∑ e, β e*x e) := by
          intro x
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro e _
          dsimp only [β]
          ring
        rw [hq, hq, hh]
      have he : (∑ e, (a e*((m e:ℝ)+upperBit (Q ω.1.1 e))-
          (((D e).card:ℝ)*(m e:ℝ)+((ω.2 e).card:ℝ)))) =
          (∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))+
          ∑ e, (a e*(upperBit (Q ω.1.1 e)-Q ω.1.1 e)+
            ((D e).card:ℝ)*Q ω.1.1 e-((ω.2 e).card:ℝ)) := by
        conv_lhs =>
          arg 2; ext e
          equals (a e-((D e).card:ℝ))*(m e:ℝ)+(a e-((D e).card:ℝ))*Q ω.1.1 e+
            (a e*(upperBit (Q ω.1.1 e)-Q ω.1.1 e)+
            ((D e).card:ℝ)*Q ω.1.1 e-((ω.2 e).card:ℝ)) => ring
        simp only [sum_add_distrib, hw, mul_add]
      rw [he]
      exact add_le_add le_rfl hprop.2.2
  · intro e t
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_joint]
    change ν'.expect (fun ξ => (κ ξ).prob (fun S => t ∈ S e))=_
    simp_rw [hκmean]
    by_cases ht : t ∈ D e
    · simp only [ite_eq_left ht]
      exact (ν.expect_supported (fun ξ => Q ξ e)).trans (hm e)
    · simp only [ite_eq_right ht, FiniteLaw.expect_const]
  · intro e f hef t u
    rw [FiniteLaw.expect_joint]
    simp_rw [hκpair _ e f hef t u]
    by_cases ht : t ∈ D e <;> by_cases hu : u ∈ D f
    · simp only [ite_eq_left ht,ite_eq_left hu]
      exact (ν.expect_supported (fun ξ => Q ξ e*Q ξ f)).le.trans (hpair e f hef)
    all_goals simp only [ht,hu,ite_true,ite_false,zero_mul,mul_zero,FiniteLaw.expect_const,le_refl]

theorem activation_count_pair {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (X Y : Ω → ℝ) {m n p q : ℝ} (_hm : 0 ≤ m) (_hn : 0 ≤ n)
    (hX : μ.expect X=p) (hY : μ.expect Y=q)
    (hXY : μ.expect (fun ω => X ω*Y ω) ≤ p*q) :
    μ.expect (fun ω => (m+X ω)*(n+Y ω)) ≤ (m+p)*(n+q) := by
  have he : ∀ ω, (m+X ω)*(n+Y ω)=m*n+m*Y ω+n*X ω+X ω*Y ω := fun ω => by ring
  simp_rw [he,FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul,hX,hY]
  nlinarith only [hXY]

end MetricKMedian.Preparation
end
end

end OAI
