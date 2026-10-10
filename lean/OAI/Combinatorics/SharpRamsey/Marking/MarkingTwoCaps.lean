import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingCaps

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def twoDomain (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  projectiveCheapDomain W m ∩ (projectiveCheapDomain W' m').map pairDuality.symm.toEmbedding

omit [Finite K] in
lemma twoDomain_forward (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    twoDomain W W' m m' ⊆ projectiveCheapDomain W m := inter_subset_left

omit [Finite K] in
lemma twoDomain_reverse (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    (twoDomain W W' m m').map pairDuality.toEmbedding ⊆ projectiveCheapDomain W' m' := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
  obtain ⟨h,h',he⟩ := mem_map.mp (mem_inter.mp hg).2
  have he' : pairDuality g=h := by rw [←he]; exact pairDuality.apply_symm_apply h
  simpa only [Equiv.coe_toEmbedding,he'] using h'

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma shadow_reverse_first (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (D.map pairDuality.toEmbedding).image Prod.fst = D.image Prod.snd := by
  ext a
  simp only [mem_image,mem_map]
  constructor
  · rintro ⟨f,⟨g,hg,hgf⟩,he⟩
    subst f
    exact ⟨g,hg,he⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨pairDuality g,⟨g,hg,rfl⟩,rfl⟩

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma shadow_reverse_second_card (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    ((D.map pairDuality.toEmbedding).image Prod.snd).card = (D.image Prod.fst).card := by
  have he : (D.map pairDuality.toEmbedding).image Prod.snd =
      (D.image Prod.fst).map bidual.toEmbedding := by
    ext b
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨f,⟨g,hg,hgf⟩,he⟩
      subst f
      exact ⟨g.1,⟨g,hg,rfl⟩,he⟩
    · rintro ⟨a,⟨g,hg,hga⟩,he⟩
      subst a
      refine ⟨pairDuality g,⟨g,hg,rfl⟩,he⟩
  rw [he,card_map]

theorem twoPopular_caps {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (hm : m.2=.popular) (hm' : m'.2=.popular) :
    let D := twoDomain W W' m m'
    ((D.image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m.1.val ∧
    ((D.image Prod.snd).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m'.1.val ∧
    (∀ b,((D.filter (fun f => f.1=b)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-m.1.val)) ∧
    (∀ a,((D.filter (fun f => f.2=a)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-m'.1.val)) := by
  dsimp only
  have hd' : Module.finrank K (Module.Dual K V)=d+1 := by rwa [Subspace.dual_finrank_eq]
  refine ⟨?_,?_,?_,?_⟩
  · exact (show (((twoDomain W W' m m').image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.fst).card by
        exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))).trans
      (cheapPopular_first_card W m hm)
  · rw [←shadow_reverse_first]
    exact (show ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.fst).card by
        exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))).trans
      (cheapPopular_first_card W' m' hm')
  · intro b
    exact (show (((twoDomain W W' m m').filter (fun f => f.1=b)).card:ℝ) ≤
      ((projectiveCheapDomain W m).filter (fun f => f.1=b)).card by
        exact_mod_cast card_le_card (filter_subset_filter _ (twoDomain_forward W W' m m'))).trans
      (cheapPopular_fiber_card hdim W m hm b)
  · intro a
    have hsub : ((twoDomain W W' m m').filter (fun f => f.2=a)).map pairDuality.toEmbedding ⊆
        (projectiveCheapDomain W' m').filter (fun f => f.1=a) := by
      intro f hf
      obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
      obtain ⟨hg,hga⟩ := mem_filter.mp hg
      exact mem_filter.mpr ⟨twoDomain_reverse W W' m m' (mem_map.mpr ⟨g,hg,rfl⟩),hga⟩
    have hc := card_le_card hsub
    rw [card_map] at hc
    exact (show (((twoDomain W W' m m').filter (fun f => f.2=a)).card:ℝ) ≤
      ((projectiveCheapDomain W' m').filter (fun f => f.1=a)).card by exact_mod_cast hc).trans
      (cheapPopular_fiber_card hd' W' m' hm' a)

theorem twoPoor_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (hm : m.2=.poor ∨ m'.2=.poor) :
    (((twoDomain W W' m m').image Prod.fst).card:ℝ)*
    ((twoDomain W W' m m').image Prod.snd).card ≤ 16*(Nat.card K:ℝ)^(n+3) := by
  have hf : (((twoDomain W W' m m').image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.fst).card := by
    exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))
  have hs : (((twoDomain W W' m m').image Prod.snd).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.snd).card := by
    exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))
  rcases hm with hm|hm
  · exact (mul_le_mul hf hs (by positivity) (by positivity)).trans (cheapPoor_product hdim W m hm)
  · have hd' : Module.finrank K (Module.Dual K V)=n+3 := by rwa [Subspace.dual_finrank_eq]
    have hf' : ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.fst).card := by
      exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))
    have hs' : ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.snd).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.snd).card := by
      exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))
    rw [shadow_reverse_first] at hf'
    rw [shadow_reverse_second_card] at hs'
    rw [mul_comm]
    exact (mul_le_mul hf' hs' (by positivity) (by positivity)).trans (cheapPoor_product hd' W' m' hm)

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma nonempty_cheap_not_expensive (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (h : (projectiveCheapDomain W m).Nonempty) : m.2≠.expensive := by
  intro hm
  unfold projectiveCheapDomain at h
  split_ifs at h
  · rw [hm] at h
    exact not_nonempty_empty h
  · exact not_nonempty_empty h

theorem twoDomain_cases {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    m.2=.poor ∨ m'.2=.poor ∨
      (m.2=.popular ∧ m'.2=.popular ∧ 1 ≤ m.1.val ∧ m.1.val≤d ∧ 1 ≤ m'.1.val ∧ m'.1.val≤d) := by
  have hf : (projectiveCheapDomain W m).Nonempty := h.mono (twoDomain_forward W W' m m')
  have hr : (projectiveCheapDomain W' m').Nonempty :=
    (h.map (f:=pairDuality.toEmbedding)).mono (twoDomain_reverse W W' m m')
  have hf' := nonempty_cheap_not_expensive W m hf
  have hr' := nonempty_cheap_not_expensive W' m' hr
  by_cases hp : m.2=.poor
  · exact Or.inl hp
  by_cases hp' : m'.2=.poor
  · exact Or.inr (Or.inl hp')
  have hpop : m.2=.popular := by cases h : m.2 <;> simp_all
  have hpop' : m'.2=.popular := by cases h : m'.2 <;> simp_all
  have h₁ := cheapPopular_rank_pos W m hpop hf
  have h₂ := cheapPopular_rank_pos W' m' hpop' hr
  have h₁' : m.1.val < d+1 := lt_of_lt_of_eq h₁.2 hdim
  have h₂' : m'.1.val < d+1 := lt_of_lt_of_eq h₂.2 (Subspace.dual_finrank_eq.trans hdim)
  exact Or.inr (Or.inr ⟨hpop,hpop',h₁.1,by omega,h₂.1,by omega⟩)

end
end SharpLogRamsey.Marking

end

end OAI
