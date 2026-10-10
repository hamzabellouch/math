import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingMessage

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

omit [Fintype Ω] [Fintype Γ] [Fintype M] in

lemma subset_budget_deficit (p : Law (ι → α)) (S : Finset ι) (J : ι → ℝ)
    (hJ : ∀ i, entropy (p.marginal i) ≤ J i) :
    0 ≤ (∑ i∈S, J i)-entropy (p.restrict S) ∧
    (∑ i∈S, J i)-entropy (p.restrict S) ≤ (∑ i, J i)-entropy p := by
  have hcap (T : Finset ι) : entropy (p.restrict T) ≤ ∑ i∈T, J i := by
    apply (entropy_subadditive_pi _).trans
    simp only [Law.marginal_restrict]
    rw [sum_subtype T (fun _ => Iff.rfl)]
    exact sum_le_sum (fun i _ => hJ i)
  let f := fun x : ι → α => ((fun i:S => x i),(fun i:↥(Sᶜ) => x i))
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    by_cases hi : i∈S
    · exact congr_fun (congrArg Prod.fst hxy) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.snd hxy) ⟨i,by simpa using hi⟩
  have h1 : (p.map f).fst=p.restrict S := by rw [←Law.map_fst,Law.map_map]; rfl
  have h2 : (p.map f).snd=p.restrict Sᶜ := by rw [←Law.map_snd,Law.map_map]; rfl
  have ht := entropy_subadditive (p.map f)
  rw [entropy_map_eq_of_injective p f hf,h1,h2] at ht
  have hs := sum_add_sum_compl S J
  exact ⟨sub_nonneg.mpr (hcap S),by linarith [hcap Sᶜ]⟩

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι] in
lemma cheap_budget_sum (E S : Finset ι) (J : ℝ) (hS : Disjoint S E) :
    (∑ i∈S, if i∈E then (0:ℝ) else J) = S.card*J := by
  rw [sum_congr rfl (fun i hi => ite_eq_right (disjoint_left.mp hS hi))]
  simp

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] in
lemma cheap_budget_total (E : Finset ι) (J : ℝ) :
    (∑ i, if i∈E then (0:ℝ) else J) = ((Fintype.card ι:ℝ)-E.card)*J := by
  rw [sum_ite,sum_const_zero,zero_add,sum_const,nsmul_eq_mul]
  have hc : (univ.filter (fun i => i∉E)).card=Fintype.card ι-E.card := by
    rw [←sdiff_eq_filter,card_sdiff_of_subset (subset_univ _),card_univ]
  rw [hc,Nat.cast_sub (card_le_univ _)]

lemma marking_subset_pointwise (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (J₀ : ℝ)
    (hc : ∀ x, p.mass x≠0 → ∀ i, i∉E (mask x) →
      F x i∈cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i∉E θ.2.2 → Real.log (cheap θ i).card≤J₀)
    (z : (ι → Option α) × (Γ × M))
    (hz : (p.map (markingMessage C mask E F)).mass z≠0)
    (S : Finset ι) (hS : Disjoint S (E z.2.2)) :
    let ν := (p.cond (markingMessage C mask E F) z).map F
    0 ≤ S.card*J₀-entropy (ν.restrict S) ∧
      S.card*J₀-entropy (ν.restrict S) ≤
        ((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀-entropy ν := by
  let θ := markingMessage C mask E F
  let ν := (p.cond θ z).map F
  have hd (i : ι) : entropy (ν.marginal i) ≤ if i∈E z.2.2 then 0 else J₀ := by
    have hm : entropy (ν.marginal i) ≤ Real.log (markingDecodedDomains E cheap z i).card := by
      change entropy (((p.cond θ z).map F).map (fun f => f i)) ≤ _
      rw [Law.map_map]
      apply entropy_mapped_support
      intro x hx
      obtain ⟨hp,he⟩ := p.cond_support θ z hz x hx
      simpa only [Function.comp_apply,←he] using
        markingDecodedDomains_mem C mask E F cheap x (hc x hp) i
    apply hm.trans
    by_cases hi : i∈E z.2.2
    · simp only [markingDecodedDomains,ite_eq_left hi]
      cases z.1 i <;> simp
    · simpa only [markingDecodedDomains,ite_eq_right hi] using hcheap z i hi
  have hh := subset_budget_deficit ν S (fun i => if i∈E z.2.2 then 0 else J₀) hd
  rw [cheap_budget_sum _ _ _ hS,cheap_budget_total] at hh
  exact hh

theorem marking_subset_deficit (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (Jprev J₀ : ℝ)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev)
    (hc : ∀ x, p.mass x≠0 → ∀ i, i∉E (mask x) →
      F x i∈cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i∉E θ.2.2 → Real.log (cheap θ i).card≤J₀)
    (S : ((ι → Option α) × (Γ × M)) → Finset ι)
    (hS : ∀ z, Disjoint (S z) (E z.2.2)) :
    let θ := markingMessage C mask E F
    let δ := fun z => (S z).card*J₀-
      entropy (((p.cond θ z).map F).restrict (S z))
    0 ≤ ∑ z, (p.map θ).mass z*δ z ∧
      (∑ z, (p.map θ).mass z*δ z) ≤ entropy (p.map C)+Real.log (Fintype.card M)+
        Fintype.card ι*J₀-entropy (p.map F)+
        (∑ x, p.mass x*((E (mask x)).card:ℝ))*(Jprev-J₀) := by
  dsimp only
  let θ := markingMessage C mask E F
  have hpt z hz := marking_subset_pointwise p C mask E F cheap J₀ hc hcheap z hz (S z) (hS z)
  constructor
  · apply sum_nonneg
    intro z _
    by_cases hz : (p.map θ).mass z=0
    · simp only [θ] at hz
      simp [hz]
    · exact mul_nonneg ((p.map θ).nonneg z) (hpt z hz).1
  · have hp := entropy_context_bound p θ F (fun z => entropy ((p.cond θ z).map F))
        (fun _ _ => le_rfl)
    have hm := marking_message_entropy p C mask E F D Jprev hD hprev
    have he : (∑ z, (p.map θ).mass z * (((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀)) =
        ((Fintype.card ι:ℝ)-∑ x, p.mass x*((E (mask x)).card:ℝ))*J₀ := by
      rw [p.sum_map θ]
      change (∑ x, p.mass x * (((Fintype.card ι:ℝ)-(E (mask x)).card)*J₀)) = _
      simp_rw [←mul_assoc,mul_sub]
      rw [←sum_mul,sum_sub_distrib,←sum_mul,p.total,one_mul]
    have hh : ∑ z, (p.map θ).mass z*((S z).card*J₀-
        entropy (((p.cond θ z).map F).restrict (S z))) ≤
        ∑ z, (p.map θ).mass z*(((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀-
          entropy ((p.cond θ z).map F)) := by
      apply sum_le_sum
      intro z _
      by_cases hz : (p.map θ).mass z=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hpt z hz).2 ((p.map θ).nonneg z)
    simp only [mul_sub,sum_sub_distrib,he] at hh
    change _ ≤ _
    dsimp only [θ] at hp hh
    simp only [mul_sub,sum_sub_distrib]
    linarith

end
end SharpLogRamsey.Selection

end

end OAI
