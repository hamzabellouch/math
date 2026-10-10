import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.ReverseCap
import OAI.Combinatorics.RamseyFive.Entropy.BlockSelected
import OAI.Combinatorics.RamseyFive.Streams.SelectedTuple

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

def retainedIndices {n l : ℕ} (hl : l≤n) (S : Finset (Fin n)) : Fin l ↪o Fin n :=
  if h : l≤S.card then (Fin.castLEOrderEmb h).trans (S.orderEmbOfFin rfl)
  else Fin.castLEOrderEmb hl

lemma retainedIndices_mem {n l : ℕ} (hl : l≤n) (S : Finset (Fin n))
    (hs : l≤S.card) (i : Fin l) : retainedIndices hl S i∈S := by
  simp only [retainedIndices,dite_eq_left hs,RelEmbedding.coe_trans,Function.comp_apply]
  exact S.orderEmbOfFin_mem rfl _

def retainedTuple {n l : ℕ} (hl : l≤n) (x : Fin n→β) (S : Finset (Fin n)) : Fin l→β :=
  x ∘ retainedIndices hl S

lemma retainedTuple_occurs {n l : ℕ} (hl : l≤n) (x : Fin n→β) (S : Finset (Fin n)) :
    x∈SelectedTuple.occurrences (retainedTuple hl x S) := by
  let e := retainedIndices hl S
  let I : Finset (Fin n) := Finset.univ.map e.toEmbedding
  have hI : I.card=l := by simp [I]
  have he : I.orderEmbOfFin hI=e := by
    symm
    apply Finset.orderEmbOfFin_unique' hI
    intro j
    simp [I]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨I,hI⟩,Finset.mem_univ _,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,fun j=>by rw [he];rfl⟩

theorem extraction_probability {n l : ℕ} (p : Law α) (S : α→Finset (Fin n))
    (hl : l<n)
    (hm : mean p (fun a=>((S a)ᶜ.card:ℝ))≤((n:ℝ)-l)/10) :
    (9:ℝ)/10≤eventMass p (Finset.univ.filter fun a=>l≤(S a).card) := by
  have hz : 0<(n:ℝ)-l := sub_pos.mpr (by exact_mod_cast hl)
  have h := markov_success p (fun a=>((S a)ᶜ.card:ℝ))
    (fun _=>Nat.cast_nonneg _) ((n:ℝ)-l) hz hm
  have he : (Finset.univ.filter fun a=>((S a)ᶜ.card:ℝ)≤(n:ℝ)-l)=
      (Finset.univ.filter fun a=>l≤(S a).card) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_compl,Fintype.card_fin]
    have hs : (S a).card≤n := by simpa using Finset.card_le_univ (S a)
    rw [Nat.cast_sub hs]
    constructor
    · intro hh
      have hh' : (l:ℝ)≤(S a).card := by linarith
      exact_mod_cast hh'
    · intro hh
      have hh' : (l:ℝ)≤(S a).card := by exact_mod_cast hh
      linarith
  rwa [he] at h

theorem extracted_domains {n l : ℕ} (hl : l≤n) (p : Law α)
    (x : α→Fin n→β) (S : α→Finset (Fin n)) (ctx : α→κ) (D : κ→Finset β)
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card)) :
    ∀ z,0< map (conditionOn p _ hE) (fun a=>(ctx a,retainedTuple hl (x a) (S a))) z →
      ∀ i,z.2 i∈D z.1 := by
  intro z hz i
  obtain ⟨a,ha,rfl⟩:=map_positive _ _ z hz
  obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
  exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i)

theorem context_tuple_entropy {ι : Type*} [Fintype ι] (p : Law (κ×(ι→β))) (D : κ→Finset β)
    (L M : ℝ) (hctx : entropy (first p)≤L)
    (hs : ∀ z,0<p z→∀ i,z.2 i∈D z.1)
    (hc : ∀ c,0<first p c→Real.log (D c).card≤M) :
    entropy (second p)≤L+Fintype.card ι*M := by
  have he : entropy p≤L+Fintype.card ι*M := by
    rw [entropy_chain]
    apply add_le_add hctx
    calc
      _ ≤ ∑ c,first p c*((Fintype.card ι:ℝ)*M) := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hz : 0<first p c
        · apply mul_le_mul_of_nonneg_left _ ((first p).nonneg c)
          have hd : InDomains (fiber p c) (fun _=>D c) := by
            intro x hx i
            exact hs (c,x) (by rw [mass_eq_first_mul_fiber];exact mul_pos hz hx) i
          have ht:=totalCorrelation_nonneg (fiber p c)
          have hm : (∑ i:ι,entropy (map (fiber p c) (fun x=>x i)))≤Fintype.card ι*M := by
            calc
              _ ≤ ∑ i:ι,M := Finset.sum_le_sum fun i _=>hd.entropy_cap M (fun _=>hc c hz) i
              _ = _ := by simp
          dsimp only [totalCorrelation] at ht
          linarith
        · have hzero : first p c=0 := le_antisymm (le_of_not_gt hz) ((first p).nonneg c)
          simp [hzero]
      _ = _ := by rw [←Finset.sum_mul,(first p).sum_one,one_mul]
  have hh := entropy_map_le p Prod.snd
  have hmap : map p Prod.snd=second p := by
    ext b
    simp only [map,second,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_eq_single b]
    · rw [ite_eq_left rfl]
    · intro a _ ha
      rw [ite_eq_right ha]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  rw [hmap] at hh
  exact hh.trans he

local instance extractedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem extracted_entropy {n l : ℕ} (hl : l≤n) (p : Law α)
    (x : α→Fin n→β) (S : α→Finset (Fin n)) (ctx : α→κ) (D : κ→Finset β)
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ)
    (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ c,Real.log (D c).card≤M) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a) (S a)))≤L+l*M := by
  have hh := context_tuple_entropy (pair (conditionOn p _ hE) ctx
    (fun a=>retainedTuple hl (x a) (S a))) D L M
    (by simpa only [first_pair] using hctx)
    (extracted_domains hl p x S ctx D hdom hE) (fun c _=>hc c)
  simpa only [second_pair,Fintype.card_fin] using hh

omit [Fintype β] in
lemma log_card_le {N : ℕ} (hN : 1≤N) (S : Finset β) (hS : S.card≤N) :
    Real.log S.card≤Real.log N := by
  by_cases hz : S.card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hN)
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hS)

end
end SharpRamseyFive.FiniteEntropy

end OAI
