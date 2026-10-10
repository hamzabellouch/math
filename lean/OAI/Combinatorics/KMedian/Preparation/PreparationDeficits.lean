import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Probability.NegativeStars

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T Ω : Type} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
  [Fintype Ω]

noncomputable def activation (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (t : T) (e : E) (ω : Ω) : ℝ :=
  if t ∈ D e then (m e:ℝ)+indicator (S ω e) t else 0

noncomputable def deficit (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (g : ℝ) (t : T) (ω : Ω) : ℝ :=
  g*∑ e, activation D m S t e ω

omit [Fintype E] [DecidableEq E] [Fintype T] [Fintype Ω] in
 theorem activation_nonneg (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (t : T) (e : E) (ω : Ω) :
    0 ≤ activation D m S t e ω := by
  unfold activation indicator
  split_ifs <;> positivity

omit [DecidableEq E] [Fintype T] in

theorem activation_deficit_moments (μ : FiniteLaw Ω) (D : E → Finset T)
    (m : E → ℕ) (p : E → ℝ) (S : Ω → E → Finset T) (g : ℝ)
    (hmean : ∀ e t, μ.prob (fun ω => t ∈ S ω e)=if t ∈ D e then p e else 0)
    (hpair : ∀ e f, e ≠ f → ∀ t v,
      μ.expect (fun ω => indicator (S ω e) t*indicator (S ω f) v) ≤
        (if t ∈ D e then p e else 0)*(if v ∈ D f then p f else 0)) :
    ∀ t, μ.expect (deficit D m S g t)=g*(∑ e, if t ∈ D e then (m e:ℝ)+p e else 0) ∧
      μ.variance (deficit D m S g t) ≤ g^2*(∑ e, if t ∈ D e then (m e:ℝ)+p e else 0) := by
  intro t
  let q := fun e => if t ∈ D e then (m e:ℝ)+p e else 0
  have hm : ∀ e, μ.expect (activation D m S t e)=q e := by
    intro e
    change μ.expect (fun ω => if t ∈ D e then (m e:ℝ)+indicator (S ω e) t else 0)=q e
    by_cases ht : t ∈ D e
    · simp only [ite_eq_left ht,FiniteLaw.expect_add,FiniteLaw.expect_const,q]
      have he := hmean e t
      simp only [ite_eq_left ht] at he
      exact congrArg ((m e:ℝ)+·) he
    · simp only [ite_eq_right ht,FiniteLaw.expect_const,q]
  have hv : ∀ e, μ.variance (activation D m S t e) ≤ q e := by
    intro e
    apply μ.adjacent_variance (activation D m S t e)
      (m := if t ∈ D e then (m e:ℝ) else 0) (by split_ifs <;> positivity) _ (hm e)
    intro ω _
    unfold activation indicator
    split_ifs <;> simp
  have hp : ∀ e f, e ≠ f → μ.expect (fun ω => activation D m S t e ω*activation D m S t f ω) ≤ q e*q f := by
    intro e f hef
    by_cases he : t ∈ D e <;> by_cases hf : t ∈ D f
    · simp only [activation,ite_eq_left he,ite_eq_left hf,q]
      have hme := hmean e t
      have hmf := hmean f t
      have hpf := hpair e f hef t t
      simp only [ite_eq_left he,ite_eq_left hf] at hme hmf hpf
      exact activation_count_pair μ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        hme hmf hpf
    all_goals simp only [activation,he,hf,ite_true,ite_false,zero_mul,mul_zero,FiniteLaw.expect_const,q,le_refl]
  constructor
  · change μ.expect (fun ω => g*∑ e, activation D m S t e ω)=_
    rw [FiniteLaw.expect_mul,FiniteLaw.expect_sum]
    simp only [hm,q]
  · exact (FiniteLaw.variance_mul μ (fun ω => ∑ e, activation D m S t e ω) g).le.trans
      (mul_le_mul_of_nonneg_left (μ.variance_sum_le (activation D m S t) q q hm hv hp) (sq_nonneg g))

omit [DecidableEq E] in

theorem sum_activations (D : E → Finset T) (m : E → ℕ) (S : E → Finset T)
    (hS : ∀ e, S e ⊆ D e) :
    (∑ t, ∑ e, if t ∈ D e then (m e:ℝ)+indicator (S e) t else 0)=
      ∑ e, (((D e).card:ℝ)*(m e:ℝ)+((S e).card:ℝ)) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  have he : ∀ t, (if t ∈ D e then (m e:ℝ)+indicator (S e) t else 0)=
      (if t ∈ D e then (m e:ℝ) else 0)+indicator (S e) t := by
    intro t
    by_cases ht : t ∈ D e
    · simp only [ite_eq_left ht]
    · have hst : t ∉ S e := fun hs => ht (hS e hs)
      simp only [ite_eq_right ht,indicator,ite_eq_right hst,add_zero]
  simp_rw [he]
  rw [sum_add_distrib,sum_indicator]
  congr 1
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]

omit [Fintype Ω] [DecidableEq E] in

theorem actual_opening_budget (D : E → Finset T) (a p : E → ℝ) (m : E → ℕ)
    (S : Ω → E → Finset T) (O : Ω → E → ℝ) (c : T → ℝ)
    {g γ B : ℝ} (hg : 0 ≤ g) (ω : Ω)
    (hS : ∀ e, S ω e ⊆ D e)
    (hraw : (∑ e, (a e*O ω e-(((D e).card:ℝ)*(m e:ℝ)+((S ω e).card:ℝ)))) ≤
      (∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))+3)
    (hplanned : (Fintype.card T:ℝ)+g*(∑ e, (a e-((D e).card:ℝ))*((m e:ℝ)+p e))=B-γ*∑ t, c t)
    (hgood : (∑ t, (deficit D m S g t ω-min (deficit D m S g t ω) (1/2))) ≤ γ*∑ t, c t) :
    ((Fintype.card T:ℝ)+g*∑ e, a e*O ω e)-(∑ t, min (deficit D m S g t ω) (1/2)) ≤ B+3*g := by
  have hz : (∑ t, deficit D m S g t ω)=g*∑ e, (((D e).card:ℝ)*(m e:ℝ)+((S ω e).card:ℝ)) := by
    simp only [deficit,activation,← mul_sum]
    rw [sum_activations D m (S ω) hS]
  have hr := mul_le_mul_of_nonneg_left hraw hg
  rw [sum_sub_distrib] at hr hgood
  rw [hz] at hgood
  rw [mul_sub,mul_add] at hr
  linarith only [hr,hgood,hplanned]

end MetricKMedian.Preparation
end
end

end OAI
