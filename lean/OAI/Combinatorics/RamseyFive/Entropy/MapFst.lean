import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PermissibleLevels
import OAI.Combinatorics.RamseyFive.Entropy.BlockReveal

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma map_fst (p : Law (α×β)) : map p Prod.fst=first p := by
  apply Law.ext
  funext a
  simp [map,first,Fintype.sum_prod_type,Finset.sum_comm]

lemma map_snd (p : Law (α×β)) : map p Prod.snd=second p := by
  apply Law.ext
  funext b
  simp [map,second,Fintype.sum_prod_type]

lemma pair_self_apply (p : Law α) (f : α→β) (b : β) (a : α) :
    pair p f id (b,a)=if f a=b then p a else 0 := by
  simp only [pair,map]
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro c hc hca
    have hne : (f c,id c)≠(b,a) := fun h=>hca (congrArg Prod.snd h)
    simp [hca]
  · simp

lemma partition_first (p : Law α) (f : α→β) : first (pair p f id)=map p f :=
  first_pair p f id

lemma partition_entropy (p : Law α) (f : α→β) :
    entropy p=entropy (map p f)+∑b,map p f b*entropy (fiber (pair p f id) b) := by
  have he : entropy (pair p f id)=entropy p :=
    entropy_map_injective p _ (fun _ _ h=>congrArg Prod.snd h)
  rw [←he,entropy_chain,partition_first]

lemma partition_support_subset (p : Law α) (f : α→β) (b : β)
    (hb : 0 < map p f b) :
    support (fiber (pair p f id) b)⊆(support p).filter (fun a=>f a=b) := by
  intro a ha
  have hfa := (mem_support _ _).mp ha
  have hfst : 0 < first (pair p f id) b := by simpa only [partition_first] using hb
  have hp : 0 < pair p f id (b,a) := by
    rw [mass_eq_first_mul_fiber]
    exact mul_pos hfst hfa
  rw [pair_self_apply] at hp
  split_ifs at hp with hh
  · exact Finset.mem_filter.mpr ⟨(mem_support _ _).mpr hp,hh⟩
  · exact (lt_irrefl 0 hp).elim

theorem entropy_partition_bound (p : Law α) (f : α→β) (C : β→ℝ)
    (hC : ∀b,0 < map p f b →
      Real.log (((support p).filter (fun a=>f a=b)).card:ℝ)≤C b) :
    entropy p≤entropy (map p f)+∑b,map p f b*C b := by
  rw [partition_entropy p f]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro b _
  by_cases hz : map p f b=0
  · simp [hz]
  · have hp : 0 < map p f b := lt_of_le_of_ne ((map p f).nonneg _) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    have hh : ((support (fiber (pair p f id) b)).card:ℝ)≤
        ((support p).filter (fun a=>f a=b)).card := by
      exact_mod_cast Finset.card_le_card (partition_support_subset p f b hp)
    exact (entropy_support_cap _ _ hh).trans (hC b hp)

end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def endpointLevels (p : Law (α×β)) (z : α×β) :
    Level (first p)×Level (second p) := (levelIndex (first p) z.1,levelIndex (second p) z.2)
noncomputable def levelPairLaw (p : Law (α×β)) := map p (endpointLevels p)

lemma first_levelPairLaw (p : Law (α×β)) : first (levelPairLaw p)=levelLaw (first p) := by
  calc
    _ = map (levelPairLaw p) Prod.fst := (map_fst _).symm
    _ = map p (fun z=>levelIndex (first p) z.1) := map_comp p _ _
    _ = map (map p Prod.fst) (levelIndex (first p)) := (map_comp p Prod.fst (levelIndex (first p))).symm
    _ = _ := congrArg (fun μ : Law α=>map μ (levelIndex (first p))) (map_fst p)

lemma second_levelPairLaw (p : Law (α×β)) : second (levelPairLaw p)=levelLaw (second p) := by
  calc
    _ = map (levelPairLaw p) Prod.snd := (map_snd _).symm
    _ = map p (fun z=>levelIndex (second p) z.2) := map_comp p _ _
    _ = map (map p Prod.snd) (levelIndex (second p)) := (map_comp p Prod.snd (levelIndex (second p))).symm
    _ = _ := congrArg (fun μ : Law β=>map μ (levelIndex (second p))) (map_snd p)

lemma sum_levelPair_fst (p : Law (α×β)) (w : Level (first p)→ℝ) :
    (∑n,levelPairLaw p n*w n.1)=∑n,levelLaw (first p) n*w n := by
  simpa only [map_fst,first_levelPairLaw] using (sum_map (levelPairLaw p) Prod.fst w).symm

lemma sum_levelPair_snd (p : Law (α×β)) (w : Level (second p)→ℝ) :
    (∑n,levelPairLaw p n*w n.2)=∑n,levelLaw (second p) n*w n := by
  simpa only [map_snd,second_levelPairLaw] using (sum_map (levelPairLaw p) Prod.snd w).symm

lemma levelPair_entropy (p : Law (α×β)) :
    entropy (levelPairLaw p) ≤ entropy (levelLaw (first p))+entropy (levelLaw (second p)) := by
  simpa only [first_levelPairLaw,second_levelPairLaw] using entropy_subadditive (levelPairLaw p)

lemma positive_marginals (p : Law (α×β)) {z : α×β} (hz : 0 < p z) :
    0 < first p z.1 ∧ 0 < second p z.2 := by
  constructor
  · exact lt_of_lt_of_le hz (Finset.single_le_sum (fun b _=>p.nonneg (z.1,b)) (Finset.mem_univ z.2))
  · exact lt_of_lt_of_le hz (Finset.single_le_sum (fun a _=>p.nonneg (a,z.2)) (Finset.mem_univ z.1))

lemma level_pair_support_subset (p : Law (α×β)) (R : α→β→Prop)
    (hR : ∀z,0 < p z→R z.1 z.2) (n : Level (first p)×Level (second p)) :
    (support p).filter (fun z=>endpointLevels p z=n) ⊆
      ((levelCell (first p) n.1)×ˢ(levelCell (second p) n.2)).filter (fun z=>R z.1 z.2) := by
  intro z hz
  obtain ⟨hs,he⟩ := Finset.mem_filter.mp hz
  have hp := (mem_support p z).mp hs
  have hm := positive_marginals p hp
  have h₁ : atomLevel (first p) z.1=n.1.val := congrArg (fun x=>x.1.val) he
  have h₂ : atomLevel (second p) z.2=n.2.val := congrArg (fun x=>x.2.val) he
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨(mem_levelCell _ _ _).mpr ⟨hm.1,h₁⟩,(mem_levelCell _ _ _).mpr ⟨hm.2,h₂⟩⟩,hR z hp⟩

lemma positive_level_pair_support (p : Law (α×β)) (n : Level (first p)×Level (second p))
    (hn : 0 < levelPairLaw p n) :
    ((support p).filter (fun z=>endpointLevels p z=n)).Nonempty := by
  by_contra he
  have hz : levelPairLaw p n=0 := by
    unfold levelPairLaw map
    apply Finset.sum_eq_zero
    intro z _
    by_cases hh : endpointLevels p z=n
    · rw [ite_eq_left hh]
      have hnot : z∉support p := by
        intro hm
        exact he ⟨z,Finset.mem_filter.mpr ⟨hm,hh⟩⟩
      exact outside_support p hnot
    · simp [hh]
  linarith

theorem expected_total_level_loss (p : Law (α×β)) (NA NB D : ℝ)
    (hrect : ∀n : Level (first p)×Level (second p),0 < levelPairLaw p n→
      Real.log (((support p).filter (fun z=>endpointLevels p z=n)).card:ℝ) ≤
        D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) :
    (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(D-entropy p+entropy (levelLaw (first p))+entropy (levelLaw (second p))) := by
  have he := entropy_partition_bound p (endpointLevels p)
    (fun n=>D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) (by
      intro n hn
      convert hrect n hn using 1
      congr 3
      ext point
      simp)
  change entropy p ≤ entropy (levelPairLaw p)+
    ∑n,levelPairLaw p n*(D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) at he
  have hs : (∑n,levelPairLaw p n*(D-(levelLoss (first p) NA n.1+
      levelLoss (second p) NB n.2)/2)) = D-
      ((∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n))/2 := by
    simp only [mul_sub,←mul_div_assoc,mul_add,Finset.sum_sub_distrib,←Finset.sum_div,
      Finset.sum_add_distrib,←Finset.sum_mul,(levelPairLaw p).sum_one,one_mul,
      sum_levelPair_fst,sum_levelPair_snd]
  rw [hs] at he
  have hh := levelPair_entropy p
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
