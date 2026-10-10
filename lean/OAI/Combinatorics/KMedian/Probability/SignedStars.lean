import Mathlib
import OAI.Combinatorics.KMedian.Probability.SignedPartial
import OAI.Combinatorics.KMedian.Probability.NegativeStars
import OAI.Combinatorics.KMedian.Probability.FiniteClipping

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T : Type} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

theorem signed_star_law (D : E → Finset T) (a p : E → ℝ) (m : E → ℕ)
    (ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (S : Ω → E → Finset T) (O N : Ω → E → ℝ),
        (∀ ω, 0 < μ.weight ω →
          (∀ e, S ω e ⊆ D e) ∧
          (∀ e, O ω e=(m e:ℝ) ∨ O ω e=(m e:ℝ)+1) ∧
          (∀ e, N ω e=(m e:ℝ) ∨ N ω e=(m e:ℝ)+1) ∧
          (∀ e, p e=0 → O ω e=(m e:ℝ)) ∧
          (∀ e, N ω e ≤ O ω e) ∧
          (∀ e t, (m e:ℝ)+indicator (S ω e) t ≤ O ω e) ∧
          (∑ e, (a e*O ω e-(((D e).card:ℝ)*(m e:ℝ)+((S ω e).card:ℝ)))) ≤
            (∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))+3) ∧
        (∀ e, μ.expect (fun ω => N ω e)=(m e:ℝ)+p e) ∧
        (∀ e f, e ≠ f → μ.expect (fun ω => N ω e*N ω f) ≤
          ((m e:ℝ)+p e)*((m f:ℝ)+p f)) ∧
        (∀ e t, μ.prob (fun ω => t ∈ S ω e)=if t ∈ D e then p e else 0) ∧
        (∀ e f, e ≠ f → ∀ t u,
          μ.expect (fun ω => indicator (S ω e) t*indicator (S ω f) u) ≤
            (if t ∈ D e then p e else 0)*(if u ∈ D f then p f else 0)) := by
  classical
  let u := fun e => a e-((D e).card:ℝ)
  obtain ⟨Ξ,instΞ,hex⟩ := exists_signed_partial_law p u hp0 hp1 (by
    intro e _
    exact (sub_le_self _ (Nat.cast_nonneg _)).trans (ha1 e))
  let := instΞ
  obtain ⟨ν,Q,hs,hm,hpair⟩ := hex
  let Ξ' := {ξ : Ξ // 0 < ν.weight ξ}
  let ν' : FiniteLaw Ξ' := ν.supported
  have hq0 : ∀ ξ : Ξ', ∀ e, 0 ≤ Q ξ.1 e := fun ξ => (hs ξ.1 ξ.2).1
  have hq1 : ∀ ξ : Ξ', ∀ e, Q ξ.1 e ≤ 1 := fun ξ => (hs ξ.1 ξ.2).2.1
  have hmq : ∀ e, ν'.expect (fun ξ => Q ξ.1 e)=p e := fun e =>
    (ν.expect_supported (fun ξ => Q ξ e)).trans (hm e)
  have hqzero : ∀ ξ : Ξ', ∀ e, p e=0 → Q ξ.1 e=0 := by
    intro ξ e he
    exact ν'.nonneg_expect_zero_support (fun ξ => Q ξ.1 e) (fun ξ => hq0 ξ e)
      ((hmq e).trans he) ξ ξ.2
  choose κs hκs hκsm hκsp using (fun ξ : Ξ' =>
    exceptional_activation_law D (Q ξ.1) a (hq0 ξ) (hq1 ξ) ha0 ha1 (hs ξ.1 ξ.2).2.2.1)
  let κn : Ξ' → FiniteLaw (E → Bool) := fun ξ => FiniteLaw.bernoulli (Q ξ.1) (hq0 ξ) (hq1 ξ)
  let κ := fun ξ => (κs ξ).independent (κn ξ)
  let μ := ν'.joint κ
  let bit : (E → Bool) → E → ℝ := fun ω e => if ω e=true then 1 else 0
  have hmcoin : ∀ ξ e, (κn ξ).expect (fun ω => bit ω e)=Q ξ.1 e := fun ξ =>
    FiniteLaw.bernoulli_marginal (Q ξ.1) (hq0 ξ) (hq1 ξ)
  have hpcoin : ∀ ξ e f, e ≠ f →
      (κn ξ).expect (fun ω => bit ω e*bit ω f)=Q ξ.1 e*Q ξ.1 f := by
    intro ξ e f hef
    have he : ∀ ω, bit ω e*bit ω f=if ω e=true ∧ ω f=true then (1:ℝ) else 0 := by
      intro ω; dsimp only [bit]; split_ifs <;> simp_all
    simp_rw [he]
    exact FiniteLaw.bernoulli_pair (Q ξ.1) (hq0 ξ) (hq1 ξ) hef
  have hkn : ∀ ξ e, (κ ξ).expect (fun z => bit z.2 e)=Q ξ.1 e := by
    intro ξ e
    exact ((κs ξ).independent_right (κn ξ) (fun z => bit z e)).trans (hmcoin ξ e)
  have hknp : ∀ ξ e f, e ≠ f → (κ ξ).expect (fun z => bit z.2 e*bit z.2 f)=Q ξ.1 e*Q ξ.1 f := by
    intro ξ e f hef
    exact ((κs ξ).independent_right (κn ξ) (fun z => bit z e*bit z f)).trans (hpcoin ξ e f hef)
  have hks : ∀ ξ e t, (κ ξ).expect (fun z => if t ∈ z.1 e then 1 else 0)=
      if t ∈ D e then Q ξ.1 e else 0 := by
    intro ξ e t
    exact ((κs ξ).independent_left (κn ξ) (fun z => if t ∈ z e then 1 else 0)).trans (hκsm ξ e t)
  have hksp : ∀ ξ e f, e ≠ f → ∀ t v,
      (κ ξ).expect (fun z => indicator (z.1 e) t*indicator (z.1 f) v)=
        (if t ∈ D e then Q ξ.1 e else 0)*(if v ∈ D f then Q ξ.1 f else 0) := by
    intro ξ e f hef t v
    exact ((κs ξ).independent_left (κn ξ) (fun z => indicator (z e) t*indicator (z f) v)).trans
      (hκsp ξ e f hef t v)
  have hmn : ∀ e, μ.expect (fun ω => bit ω.2.2 e)=p e := by
    intro e
    rw [FiniteLaw.expect_joint]
    simp_rw [hkn]
    exact hmq e
  have hpn : ∀ e f, e ≠ f → μ.expect (fun ω => bit ω.2.2 e*bit ω.2.2 f) ≤ p e*p f := by
    intro e f hef
    rw [FiniteLaw.expect_joint]
    simp_rw [hknp _ e f hef]
    exact (ν.expect_supported (fun ξ => Q ξ e*Q ξ f)).le.trans (hpair e f hef)
  refine ⟨Ξ' × ((E → Finset T) × (E → Bool)),inferInstance,μ,fun ω => ω.2.1,
    fun ω e => (m e:ℝ)+upperBit (Q ω.1.1 e),fun ω e => (m e:ℝ)+bit ω.2.2 e,?_,?_,?_,?_,?_⟩
  · intro ω hω
    have hprod := (FiniteLaw.support_joint ν' κ ω hω).2
    have hsupport := FiniteLaw.support_independent (κs ω.1) (κn ω.1) ω.2 hprod
    have hprop := hκs ω.1 ω.2.1 hsupport.1
    refine ⟨hprop.1,?_,?_,?_,?_,?_,?_⟩
    · intro e
      dsimp only
      unfold upperBit
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl (add_zero _)
    · intro e
      dsimp only [bit]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl (add_zero _)
    · intro e he
      simp only [hqzero ω.1 e he,upperBit,lt_self_iff_false,ite_false,add_zero]
    · intro e
      apply add_le_add le_rfl
      by_cases hq : 0 < Q ω.1.1 e
      · simp only [upperBit,ite_eq_left hq,bit]
        split_ifs <;> norm_num
      · have hzero : Q ω.1.1 e=0 := le_antisymm (le_of_not_gt hq) (hq0 ω.1 e)
        have hn := (κn ω.1).prob_zero_support (fun v => v e=true)
          ((hmcoin ω.1 e).trans hzero) ω.2.2 hsupport.2
        simp only [bit,ite_eq_right hn,upperBit,ite_eq_right hq,le_refl]
    · intro e t
      exact add_le_add le_rfl (hprop.2.1 e t)
    · have hw := (hs ω.1.1 ω.1.2).2.2.2
      have he : (∑ e, (a e*((m e:ℝ)+upperBit (Q ω.1.1 e))-
          (((D e).card:ℝ)*(m e:ℝ)+((ω.2.1 e).card:ℝ)))) =
          (∑ e, u e*(m e:ℝ))+(∑ e, u e*Q ω.1.1 e)+
          ∑ e, (a e*(upperBit (Q ω.1.1 e)-Q ω.1.1 e)+
            ((D e).card:ℝ)*Q ω.1.1 e-((ω.2.1 e).card:ℝ)) := by
        rw [← sum_add_distrib,← sum_add_distrib]
        apply sum_congr rfl
        intro e _
        dsimp only [u]
        ring
      have hb : (∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))=
          (∑ e, u e*(m e:ℝ))+(∑ e, u e*p e) := by
        simp only [mul_add,sum_add_distrib,u]
      dsimp only
      rw [he,hb]
      linarith only [hw,hprop.2.2]
  · intro e
    simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,hmn]
  · intro e f hef
    exact activation_count_pair μ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (hmn e) (hmn f) (hpn e f hef)
  · intro e t
    unfold FiniteLaw.prob
    rw [FiniteLaw.expect_joint]
    simp_rw [hks]
    by_cases ht : t ∈ D e
    · simp only [ite_eq_left ht]
      exact hmq e
    · simp only [ite_eq_right ht,FiniteLaw.expect_const]
  · intro e f hef t v
    rw [FiniteLaw.expect_joint]
    simp_rw [hksp _ e f hef t v]
    by_cases ht : t ∈ D e <;> by_cases hv : v ∈ D f
    · simp only [ite_eq_left ht,ite_eq_left hv]
      exact (ν.expect_supported (fun ξ => Q ξ e*Q ξ f)).le.trans (hpair e f hef)
    all_goals simp only [ht,hv,ite_true,ite_false,zero_mul,mul_zero,FiniteLaw.expect_const,le_refl]

end MetricKMedian.Preparation
end
end

end OAI
