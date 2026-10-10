import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureContexts

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.event_union_le (p : Law α) (E F : Finset α) :
    p.event (E ∪ F) ≤ p.event E+p.event F := by
  unfold Law.event
  have h : ∀ x, (if x ∈ E ∪ F then p.mass x else 0) ≤
      (if x ∈ E then p.mass x else 0)+(if x ∈ F then p.mass x else 0) := by
    intro x
    by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he,hf,p.nonneg]
  simpa only [sum_add_distrib, sum_ite_mem_eq] using
    (sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) => h x))

lemma Law.event_mono (p : Law α) {E F : Finset α} (h : E ⊆ F) : p.event E ≤ p.event F :=
  sum_le_sum_of_subset_of_nonneg h (fun x _ _ => p.nonneg x)

def conditionalHeavy (p : Law (α × β)) (L K : ℝ) (b : β) : ℝ :=
  (p.condFst b).event (univ.filter (fun a => Real.exp (K-L) < p.mass (a,b)))

def goodSecond (p : Law (α × β)) (M L K ρ : ℝ) (b : β) : Prop :=
  Real.exp (-K)/M ≤ p.snd.mass b ∧ conditionalHeavy p L K b ≤ ρ

theorem badSecond_mass (p : Law (α × β)) (S : Finset (α × β))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset β)
    (hD : ∀ b, b ∉ D → p.snd.mass b = 0)
    (M L K ρ : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hK : 0 < K) (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b => ¬goodSecond p M L K ρ b)) ≤
      Real.exp (-K)+(L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
  have hsub : univ.filter (fun b => ¬goodSecond p M L K ρ b) ⊆
      univ.filter (fun b => p.snd.mass b < Real.exp (-K)/M) ∪
      univ.filter (fun b => ρ < conditionalHeavy p L K b) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and,goodSecond,not_and_or,not_le,mem_union] at hb ⊢
    exact hb
  have hsmall := p.snd.small_atoms D hD (c := Real.exp (-K)/M) (by positivity)
  have hs2 : D.card*(Real.exp (-K)/M) ≤ Real.exp (-K) := by
    calc
      _ ≤ M*(Real.exp (-K)/M) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  have hheavy := p.bad_conditional_mass (univ.filter (fun x => Real.exp (K-L) < p.mass x)) hρ
  have hheavy' : p.snd.event (univ.filter (fun b => ρ < conditionalHeavy p L K b)) ≤
      (L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
    have he := p.heavy_atoms S hs L hK
    have hh := hheavy.trans (div_le_div_of_nonneg_right he hρ.le)
    convert hh using 1 <;> try rfl
    · simp only [conditionalHeavy,mem_filter,mem_univ,true_and]
      with_unfolding_all rfl
    · rw [div_div]
  exact (p.snd.event_mono hsub).trans ((p.snd.event_union_le _ _).trans
    (add_le_add (hsmall.trans hs2) hheavy'))

def goodSecondHigh (p : Law (α × β)) (M L K ρ R : ℝ) (b : β) : Prop :=
  goodSecond p M L K ρ b ∧ p.snd.mass b ≤ Real.exp (K-R)

theorem badSecondHigh_mass (p : Law (α × β)) (S : Finset (α × β))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset β)
    (hD : ∀ b, b ∉ D → p.snd.mass b = 0)
    (M L K ρ R : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hK : 0 < K) (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b => ¬goodSecondHigh p M L K ρ R b)) ≤
      Real.exp (-K)+(L-entropy p+S.card*Real.exp (-L))/(K*ρ)+
        (R-entropy p.snd+D.card*Real.exp (-R))/K := by
  have hsub : univ.filter (fun b => ¬goodSecondHigh p M L K ρ R b) ⊆
      univ.filter (fun b => ¬goodSecond p M L K ρ b) ∪
      univ.filter (fun b => Real.exp (K-R) < p.snd.mass b) := by
    intro b hb
    simpa only [mem_filter,mem_univ,true_and,goodSecondHigh,not_and_or,not_le,mem_union] using hb
  exact (p.snd.event_mono hsub).trans ((p.snd.event_union_le _ _).trans
    (add_le_add (badSecond_mass p S hs D hD M L K ρ hM hcard hK hρ)
      (p.snd.heavy_atoms D hD R hK)))
end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem endpoint_entropy_from_fibers (p : Law (α × β)) (D : β → Finset α)
    (hD : ∀ a b, a ∉ D b → p.mass (a,b) = 0) (J : ℝ)
    (hJ : ∀ b, Real.log (D b).card ≤ J) : entropy p-J ≤ entropy p.snd := by
  have hh : (∑ b, p.snd.mass b*entropy (p.condFst b)) ≤ J := by
    calc
      _ ≤ ∑ b, p.snd.mass b*J := by
        apply sum_le_sum
        intro b _
        by_cases hb : p.snd.mass b = 0
        · rw [hb,zero_mul,zero_mul]
        · apply mul_le_mul_of_nonneg_left _ (p.snd.nonneg b)
          apply (entropy_le_log_card (p.condFst b) (D b) ?_).trans (hJ b)
          intro a ha
          rw [p.condFst_mass b hb,hD a b ha,zero_div]
      _ = _ := by rw [← sum_mul,p.snd.total,one_mul]
  rw [entropy_chain]
  linarith
end SharpLogRamsey.Selection

end

end OAI
