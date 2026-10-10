import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UnionMarking

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]
local instance subsetDeficitDecEq : DecidableEq ι := Classical.decEq _
local instance subsetDeficitSubDecEq (S : Finset ι) : DecidableEq S := Classical.decEq _

lemma entropy_subset_split (p : Law (ι → β)) (S : Finset ι) :
    entropy p ≤ entropy (map p (fun x => fun i : S => x i.val)) +
      ∑ i∈Sᶜ,entropy (map p (fun x => x i)) := by
  let f := fun x : ι → β => fun i : S => x i.val
  let g := fun x : ι → β => fun i : (Sᶜ : Finset ι) => x i.val
  have hinj : Function.Injective (fun x => (f x,g x)) := by
    intro x y h
    funext i
    by_cases hi : i∈S
    · exact congrFun (congrArg Prod.fst h) ⟨i,hi⟩
    · exact congrFun (congrArg Prod.snd h) ⟨i,Finset.mem_compl.mpr hi⟩
  have hh := entropy_subadditive (pair p f g)
  rw [show entropy (pair p f g)=entropy p from entropy_map_injective p _ hinj,
    first_pair,second_pair] at hh
  have ht := totalCorrelation_nonneg (map p g)
  simp only [totalCorrelation,map_comp,Function.comp_def] at ht
  have he : (∑ i : (Sᶜ : Finset ι),entropy (map p (fun x => g x i))) =
      ∑ i∈Sᶜ,entropy (map p (fun x => x i)) := by
    exact Finset.sum_coe_sort Sᶜ (fun i => entropy (map p (fun x => x i)))
  rw [he] at ht
  linarith

theorem subset_deficit_le_active (p : Law (ι → β)) (U S : Finset ι)
    (hSU : S⊆U) (hf : FixedOutside p U) (J : ℝ)
    (hc : ∀ i∈U,entropy (map p (fun x => x i))≤J) :
    (S.card:ℝ)*J-entropy (map p (fun x => fun i : S => x i.val)) ≤
      activeDeficit p U J := by
  have hh := entropy_subset_split p S
  have he : (∑ i∈Sᶜ,entropy (map p (fun x => x i))) =
      ∑ i∈U\S,entropy (map p (fun x => x i)) := by
    symm
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
    · intro i hi hnot
      apply hf.entropy_zero
      intro hU
      exact hnot (Finset.mem_sdiff.mpr ⟨hU,Finset.mem_compl.mp hi⟩)
  rw [he] at hh
  have hb : (∑ i∈U\S,entropy (map p (fun x => x i))) ≤ ((U\S).card:ℝ)*J := by
    calc
      _ ≤ ∑ i∈U\S,J := Finset.sum_le_sum fun i hi => hc i (Finset.mem_sdiff.mp hi).1
      _ = _ := by simp
  have hn : ((U\S).card:ℝ)+(S.card:ℝ)=U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hSU
  calc
    _ ≤ (S.card:ℝ)*J + ((U\S).card:ℝ)*J - entropy p := by linarith
    _ = activeDeficit p U J := by
      dsimp [activeDeficit]
      rw [←add_mul,add_comm (S.card:ℝ),hn]
end

open scoped Classical BigOperators
variable {ι β κ : Type*} [Fintype ι] [Fintype β] [Fintype κ]
local instance unionPosteriorDecEq : DecidableEq ι := Classical.decEq _

abbrev UnionTranscript (ι β : Type*) :=
  (ι → RankTypes × Bool × Bool) × (ι → Option β)

def unionMessage (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) : UnionTranscript ι β :=
  (unionMask r E₁ E₂ x,unionRecord id E₁ E₂ x)

def unspecified (m : UnionTranscript ι β) : Finset ι :=
  Finset.univ.filter fun i=>m.2 i=none

omit [Fintype β] in
lemma unspecified_unionMessage (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) :
    unspecified (unionMessage r E₁ E₂ x)=(E₁ x ∪ E₂ x)ᶜ := by
  ext i
  simp only [unspecified,Finset.mem_filter,Finset.mem_univ,true_and,unionMessage,
    unionRecord,Finset.mem_compl, id_eq]
  split_ifs <;> simp_all

omit [Fintype β] in
lemma unspecified_card (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) :
    ((unspecified (unionMessage r E₁ E₂ x)).card:ℝ)+((E₁ x ∪ E₂ x).card:ℝ)=
      Fintype.card ι := by
  rw [unspecified_unionMessage]
  exact_mod_cast Finset.card_compl_add_card (E₁ x ∪ E₂ x)

lemma unionMessage_fixedOutside (p : Law (κ × (ι → β)))
    (r : (ι → β) → ι → RankTypes) (E₁ E₂ : (ι → β) → Finset ι)
    (c : κ) (m : UnionTranscript ι β)
    (hm : 0<first (withMessage p (unionMessage r E₁ E₂)) (c,m)) :
    FixedOutside (fiber (withMessage p (unionMessage r E₁ E₂)) (c,m)) (unspecified m) := by
  intro i hi
  have hn : m.2 i≠none := fun h=>hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨b,?_⟩
  intro x hx
  have hmx := (fiber_withMessage_support p (unionMessage r E₁ E₂) c m hm x hx).2
  have hrec : unionRecord id E₁ E₂ x i=some b := by
    rw [←hb]
    exact congrFun (congrArg Prod.snd hmx) i
  dsimp [unionRecord] at hrec
  split_ifs at hrec
  exact Option.some.inj hrec

theorem union_deficit_bound (p : Law (κ × (ι → β)))
    (r : (ι → β) → ι → RankTypes) (E₁ E₂ : (ι → β) → Finset ι)
    (S : κ → ι → Finset β) (cap J : ℝ) (hcap : 1≤cap)
    (hS : ∀ c i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c x,0<p (c,x) → ∀ i,x i∈S c i) :
    mean (first (withMessage p (unionMessage r E₁ E₂)))
      (fun z=>activeDeficit (fiber (withMessage p (unionMessage r E₁ E₂)) z)
        (unspecified z.2) J) ≤
      (Fintype.card ι:ℝ)*J-entropy (second p)+entropy (first p)+
        (Fintype.card ι:ℝ)*Real.log 800+
        mean (second p) (fun x=>((E₁ x ∪ E₂ x).card:ℝ))*(Real.log cap-J) := by
  apply message_deficit_bound p (unionMessage r E₁ E₂) unspecified
    (fun x=>((E₁ x ∪ E₂ x).card:ℝ)) J (Real.log cap)
    ((Fintype.card ι:ℝ)*Real.log 800) (unspecified_card r E₁ E₂)
  exact union_marking_entropy p r id E₁ E₂ S cap hcap hS hsupp
end SharpRamseyFive.FiniteEntropy

end

end OAI
