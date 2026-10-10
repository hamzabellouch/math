import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Finset Classical
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def BelowChain (r : α → α → Prop) (x : α) (c : Finset α) : Prop :=
  (c : Set α).Pairwise (fun u v => r u v ∨ r v u) ∧ ∀ y∈c,r y x

def rank (r : α → α → Prop) (x : α) : ℕ :=
  (univ.filter (BelowChain r x)).sup Finset.card

omit [DecidableEq α] in
lemma rank_realized (r : α → α → Prop) (x : α) :
    ∃ c : Finset α,BelowChain r x c ∧ c.card=rank r x := by
  have hempty : BelowChain r x ∅ := by simp [BelowChain]
  obtain ⟨c,hc,he⟩ := exists_mem_eq_sup (univ.filter (BelowChain r x))
    (show (univ.filter (BelowChain r x)).Nonempty from ⟨∅,by simp [hempty]⟩) Finset.card
  exact ⟨c,(mem_filter.mp hc).2,he.symm⟩

lemma rank_lt (r : α → α → Prop)
    (hr : ∀ ⦃first middle last : α⦄, r first middle → r middle last → r first last)
    (hi : ∀ point, ¬r point point)
    {x y : α} (hxy : r x y) : rank r x<rank r y := by
  obtain ⟨c,hc,he⟩ := rank_realized r x
  have hxc : x∉c := fun hx => hi x (hc.2 x hx)
  have hchain : BelowChain r y (insert x c) := by
    constructor
    · rw [coe_insert,Set.pairwise_insert]
      exact ⟨hc.1,fun z hz hzx => ⟨Or.inr (hc.2 z hz),Or.inl (hc.2 z hz)⟩⟩
    · intro z hz
      rcases mem_insert.mp hz with rfl|hz
      · exact hxy
      · exact hr (hc.2 z hz) hxy
  have hle : (insert x c).card  ≤  rank r y := le_sup (f:=Finset.card) (by simp [hchain])
  rw [card_insert_of_notMem hxc,he] at hle
  omega

theorem chain_or_antichain (r : α → α → Prop)
    (hr : ∀ ⦃first middle last : α⦄, r first middle → r middle last → r first last)
    (hi : ∀ point, ¬r point point)
    (n : ℕ) (hcard : n*n  ≤  Fintype.card α) :
    ∃ c : Finset α,n ≤ c.card ∧
      ((c : Set α).Pairwise (fun x y => r x y ∨ r y x) ∨ (c : Set α).Pairwise (fun x y => ¬r x y ∧ ¬r y x)) := by
  by_cases hlong : ∃ c : Finset α,n ≤ c.card ∧ (c : Set α).Pairwise (fun x y => r x y ∨ r y x)
  · obtain ⟨c,hc,hp⟩ := hlong
    exact ⟨c,hc,Or.inl hp⟩
  · have hsmall (x : α) : rank r x<n := by
      obtain ⟨c,hc,he⟩ := rank_realized r x
      by_contra h
      exact hlong ⟨c,he.symm ▸ le_of_not_gt h,hc.1⟩
    by_cases hn : n=0
    · exact ⟨∅,by simp [hn],Or.inl (by simp)⟩
    let f : α → Fin n := fun x => ⟨rank r x,hsmall x⟩
    have hex : ∃ k : Fin n,n ≤ (univ.filter (fun x => f x=k)).card := by
      by_contra h
      push Not at h
      have hsum := sum_card_fiberwise_eq_card_filter (s:=univ) (t:=univ) f
      have hlt : (∑ k : Fin n,(univ.filter (fun x => f x=k)).card)<∑ _k : Fin n,n :=
        sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)))
          (fun k hk => h k)
      have he : (∑ k : Fin n,(univ.filter (fun x => f x=k)).card)=Fintype.card α := by simpa using hsum
      have hlt' : (∑ k : Fin n,(univ.filter (fun x => f x=k)).card)<n*n := by simpa using hlt
      omega
    obtain ⟨k,hk⟩ := hex
    refine ⟨univ.filter (fun x => f x=k),hk,Or.inr ?_⟩
    intro x hx y hy hxy
    have he : rank r x=rank r y := congrArg Fin.val ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    exact ⟨fun h => (rank_lt r hr hi h).ne he,fun h => (rank_lt r hr hi h).ne he.symm⟩

def Chain (r : α → α → Prop) (c : Finset α) : Prop :=
  (c : Set α).Pairwise (fun x y => r x y ∨ r y x)
def Anti (r : α → α → Prop) (c : Finset α) : Prop :=
  (c : Set α).Pairwise (fun x y => ¬r x y ∧ ¬r y x)

omit [Fintype α] in
lemma chain_or_antichain_subset (r : α → α → Prop)
    (hr : ∀ ⦃first middle last : α⦄, r first middle → r middle last → r first last)
    (hi : ∀ point, ¬r point point)
    (s : Finset α) (n : ℕ) (hn : n*n ≤ s.card) :
    ∃ c ⊆ s,n ≤ c.card ∧ (Chain r c ∨ Anti r c) := by
  have hcard : n*n ≤ Fintype.card s := by simpa using hn
  obtain ⟨c,hc,hp⟩ := chain_or_antichain (fun x y : s => r x.val y.val)
    (fun _ _ _ h1 h2 => hr h1 h2) (fun x => hi x.val) n hcard
  refine ⟨c.image Subtype.val,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact y.property
  · simpa only [card_image_of_injective _ Subtype.val_injective] using hc
  · rcases hp with hp|hp
    · left
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact hp ha hb (fun he => hxy (congrArg Subtype.val he))
    · right
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact hp ha hb (fun he => hxy (congrArg Subtype.val he))

omit [Fintype α] [DecidableEq α] in
lemma Chain.mono {r : α → α → Prop} {s t : Finset α} (hs : Chain r s) (ht : t ⊆ s) : Chain r t :=
  fun _ hx _ hy hxy => hs (ht hx) (ht hy) hxy
omit [Fintype α] [DecidableEq α] in
lemma Anti.mono {r : α → α → Prop} {s t : Finset α} (hs : Anti r s) (ht : t ⊆ s) : Anti r t :=
  fun _ hx _ hy hxy => hs (ht hx) (ht hy) hxy

def Agree (r₁ r₂ : α → α → Prop) (x y : α) : Prop := r₁ x y ∧ r₂ x y

def Reverse (r₁ r₂ : α → α → Prop) (x y : α) : Prop := r₁ x y ∧ r₂ y x

omit [Fintype α] [DecidableEq α] in
lemma reverse_of_two_chains {r₁ r₂ : α → α → Prop} {s : Finset α}
    (h₁ : Chain r₁ s) (h₂ : Chain r₂ s) (ha : Anti (Agree r₁ r₂) s) : Chain (Reverse r₁ r₂) s := by
  intro x hx y hy hxy
  have hna := ha hx hy hxy
  rcases h₁ hx hy hxy with hxy₁|hyx₁
  · rcases h₂ hx hy hxy with hxy₂|hyx₂
    · exact False.elim (hna.1 ⟨hxy₁,hxy₂⟩)
    · exact Or.inl ⟨hxy₁,hyx₂⟩
  · rcases h₂ hx hy hxy with hxy₂|hyx₂
    · exact Or.inr ⟨hyx₁,hxy₂⟩
    · exact False.elim (hna.2 ⟨hyx₁,hyx₂⟩)

omit [Fintype α] in
theorem two_order_extraction (r₁ r₂ : α → α → Prop)
    (ht₁ : ∀ ⦃first middle last : α⦄, r₁ first middle → r₁ middle last → r₁ first last)
    (hi₁ : ∀ point, ¬r₁ point point)
    (ht₂ : ∀ ⦃first middle last : α⦄, r₂ first middle → r₂ middle last → r₂ first last)
    (hi₂ : ∀ point, ¬r₂ point point)
    (s : Finset α) (n : ℕ) (hn : n^8 ≤ s.card) :
    ∃ c ⊆ s,n ≤ c.card ∧ (Anti r₁ c ∨ Anti r₂ c ∨ Chain (Agree r₁ r₂) c ∨ Chain (Reverse r₁ r₂) c) := by
  have hn2 : n ≤ n^2 := by nlinarith
  have hn4 : n ≤ n^4 := hn2.trans (by nlinarith [sq_nonneg (n:ℤ)])
  obtain ⟨a,has,ha,hac|haa⟩ := chain_or_antichain_subset r₁ ht₁ hi₁ s (n^4) (by nlinarith [hn])
  swap
  · exact ⟨a,has,hn4.trans ha,Or.inl haa⟩
  obtain ⟨b,hba,hb,hbc|hba'⟩ := chain_or_antichain_subset r₂ ht₂ hi₂ a (n^2) (by nlinarith [ha])
  swap
  · exact ⟨b,hba.trans has,hn2.trans hb,Or.inr (Or.inl hba')⟩
  have hat : ∀ ⦃first middle last : α⦄,
      Agree r₁ r₂ first middle → Agree r₁ r₂ middle last → Agree r₁ r₂ first last :=
    fun _ _ _ hp hq => ⟨ht₁ hp.1 hq.1,ht₂ hp.2 hq.2⟩
  have hai : ∀ point, ¬Agree r₁ r₂ point point := fun point hp => hi₁ point hp.1
  obtain ⟨c,hcb,hc,hcc|hca⟩ := chain_or_antichain_subset (Agree r₁ r₂) hat hai b n (by nlinarith [hb])
  · exact ⟨c,(hcb.trans hba).trans has,hc,Or.inr (Or.inr (Or.inl hcc))⟩
  · exact ⟨c,(hcb.trans hba).trans has,hc,Or.inr (Or.inr (Or.inr
      (reverse_of_two_chains (hac.mono (hcb.trans hba)) (hbc.mono hcb) hca)))⟩

end
end OrdinaryCorrelations.Rerooting

end

end OAI
