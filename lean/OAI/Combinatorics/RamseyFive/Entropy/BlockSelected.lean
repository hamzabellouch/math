import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RevealDomains

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

theorem fresh_selected_fraction (S : B → Finset A) (r : ℕ) (hr : 0<r)
    (hS : ∀ b, r ≤ (S b).card) (f : (B → A) → B → A → ℝ)
    (hf : ∀ s b a, 0 ≤ f s b a)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) :
    r * mean (freshBlockLaw S) (fun s => ∑ b, f s b (s b)) ≤
      mean (freshBlockLaw S) (fun s => ∑ b, ∑ a ∈ S b, f s b a) := by
  have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (hr.trans_le (hS b))
  rw [freshBlockLaw_eq S hn]
  simp only [mean_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hc : (r : ℝ) ≤ (S b).card := by exact_mod_cast hS b
  have hnp : 0 ≤ mean (piLaw (fun b => uniformOn (S b) (hn b))) (fun s => f s b (s b)) :=
    mean_nonneg _ _ fun s => hf s b (s b)
  exact (mul_le_mul_of_nonneg_right hc hnp).trans_eq (unused_selected_identity S hn f hown b)

lemma blockRoundMean_smul
    (J : Law (((B × A) ⊕ T) → β) → (B → Finset A) → (B → A) → ℝ)
    (c : ℝ) (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A) (n : ℕ) (i : Fin n) :
    blockRoundMean (fun p S s => c * J p S s) p S n i = c * blockRoundMean J p S n i := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact mean_smul _ _ _
    | succ i =>
      simp only [blockRoundMean, Fin.cases_succ, ih, mean_smul]

lemma blockRoundMean_compare
    (J₁ J₂ : Law (((B × A) ⊕ T) → β) → (B → Finset A) → (B → A) → ℝ)
    (P : Law (((B × A) ⊕ T) → β) → Prop)
    (hP : ∀ p, P p → ∀ E a, P (fiber (reveal p E) a))
    (r : ℕ)
    (hJ : ∀ p, P p → ∀ S, (∀ b, r ≤ (S b).card) →
      mean (freshBlockLaw S) (J₁ p S) ≤ mean (freshBlockLaw S) (J₂ p S))
    (p : Law (((B × A) ⊕ T) → β)) (hp : P p) (S : B → Finset A)
    (n : ℕ) (hS : ∀ b, r+n ≤ (S b).card) (i : Fin n) :
    blockRoundMean J₁ p S n i ≤ blockRoundMean J₂ p S n i := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact hJ p hp S (fun b => by have := hS b; omega)
    | succ i =>
      apply mean_mono
      intro s
      apply mean_mono
      intro a
      apply ih _ (hP p hp _ a) _
      exact eraseBlock_card S s (r+n) (fun b => by have := hS b; omega)

def blockSelectedInformation (p : Law (((B × A) ⊕ T) → β)) (_S : B → Finset A)
    (s : B → A) : ℝ := ∑ b, (blockInformation p s b (s b) : ℝ)

def blockSelectedDeficit (J : ℝ) (p : Law (((B × A) ⊕ T) → β)) (_S : B → Finset A)
    (s : B → A) : ℝ := ∑ b, (J - entropy (map p (fun x => x (Sum.inl (b,s b)))))

lemma blockSelectedInformation_mean (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (r : ℕ) (hr : 0<r) (hS : ∀ b, r ≤ (S b).card) :
    r * mean (freshBlockLaw S) (blockSelectedInformation p S) ≤
      mean (freshBlockLaw S) (blockAllInformation p S) := by
  apply (fresh_selected_fraction S r hr hS
    (fun s b a => (blockInformation p s b a : ℝ)) (fun _ _ _ => NNReal.coe_nonneg _)
    (fun s b a i => congrArg NNReal.toReal (blockInformation_own_independent p s b a i))).trans
  apply mean_mono
  intro s
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)

omit [Nonempty A] in
lemma blockAllDeficit_eq (J : ℝ) (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (s : B → A) : blockAllDeficit J p S s =
      (∑ b, ∑ a ∈ S b, (J - entropy (map p (fun x => x (Sum.inl (b,a)))))) +
      ∑ t, (J - entropy (map p (fun x => x (Sum.inr t)))) := by
  unfold blockAllDeficit marginalDeficit
  have he : (∑ i, if i ∈ blockActive S then
        (J - entropy (map p (fun x => x i))) else 0) =
      (∑ b, ∑ a ∈ S b, (J - entropy (map p (fun x => x (Sum.inl (b,a)))))) +
      ∑ t, (J - entropy (map p (fun x => x (Sum.inr t)))) := by
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro b _
      simp only [mem_blockActive_left,Finset.sum_ite_mem,Finset.univ_inter]
    · apply Finset.sum_congr rfl
      intro t _
      rw [ite_eq_left (mem_blockActive_right S t)]
  simpa only [Finset.sum_ite_mem,Finset.univ_inter] using he

lemma blockSelectedDeficit_mean (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J)
    (p : Law (((B × A) ⊕ T) → β)) (hp : InDomains p D)
    (S : B → Finset A) (r : ℕ) (hr : 0<r) (hS : ∀ b, r ≤ (S b).card) :
    r * mean (freshBlockLaw S) (blockSelectedDeficit J p S) ≤
      mean (freshBlockLaw S) (blockAllDeficit J p S) := by
  apply (fresh_selected_fraction S r hr hS
    (fun _s b a => J - entropy (map p (fun x => x (Sum.inl (b,a)))))
    (fun _ b a => sub_nonneg.mpr (hp.entropy_cap J hJ _)) (fun _ _ _ _ => rfl)).trans
  apply mean_mono
  intro s
  rw [blockAllDeficit_eq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => sub_nonneg.mpr (hp.entropy_cap J hJ _))

theorem block_round_selected_information (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (r n : ℕ) (hr : 0<r) (hS : ∀ b, r+n ≤ (S b).card) (i : Fin n) :
    r * blockRoundMean blockSelectedInformation p S n i ≤
      blockRoundMean blockAllInformation p S n i := by
  rw [←blockRoundMean_smul]
  apply blockRoundMean_compare _ _ (fun _ => True) (fun _ _ _ _ => trivial) r _ p trivial S n hS i
  intro p _ S hS
  rw [mean_smul]
  exact blockSelectedInformation_mean p S r hr hS

theorem block_round_selected_deficit (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J) (p : Law (((B × A) ⊕ T) → β))
    (hp : InDomains p D) (S : B → Finset A) (r n : ℕ) (hr : 0<r)
    (hS : ∀ b, r+n ≤ (S b).card) (i : Fin n) :
    r * blockRoundMean (blockSelectedDeficit J) p S n i ≤
      blockRoundMean (blockAllDeficit J) p S n i := by
  rw [←blockRoundMean_smul]
  apply blockRoundMean_compare _ _ (fun p => InDomains p D) (fun _ hp E a => hp.fiber E a)
    r _ p hp S n hS i
  intro p hp S hS
  rw [mean_smul]
  exact blockSelectedDeficit_mean J D hJ p hp S r hr hS
end

open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma conditionOn_le (p : Law α) (E : Finset α) (hE : 0<eventMass p E) (a : α) :
    conditionOn p E hE a≤p a/eventMass p E := by
  rw [conditionOn_apply]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (p.nonneg a) hE.le

lemma conditionOn_positive (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (a : α) (ha : 0<conditionOn p E hE a) : a∈E ∧ 0<p a := by
  rw [conditionOn_apply] at ha
  split_ifs at ha with he
  · exact ⟨he,(div_pos_iff.mp ha).resolve_right (fun hn=>hE.not_gt hn.2) |>.1⟩
  · exact (lt_irrefl 0 ha).elim

lemma map_conditionOn_le (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (f : α→β) (b : β) :
    map (conditionOn p E hE) f b ≤ map p f b / eventMass p E := by
  change (∑ a,if f a=b then conditionOn p E hE a else 0)≤
    (∑ a,if f a=b then p a else 0)/eventMass p E
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact conditionOn_le p E hE a
  · simp only [zero_div,le_refl]

theorem conditioned_density (p : Law α) (prior : Law β) (stream : α→β)
    (E : Finset α) (hE : 0<eventMass p E) (D c : ℝ)
    (hc : 0<c) (hprob : c≤eventMass p E)
    (hdens : ∀ b,map p stream b≤D*prior b) :
    ∀ b,map (conditionOn p E hE) stream b≤(D/c)*prior b := by
  intro b
  calc
    _ ≤ map p stream b/eventMass p E := map_conditionOn_le p E hE stream b
    _ ≤ map p stream b/c := div_le_div_of_nonneg_left ((map p stream).nonneg b) hc hprob
    _ ≤ (D*prior b)/c := div_le_div_of_nonneg_right (hdens b) hc.le
    _ = _ := by ring

lemma conditionOn_mean_le (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (f : α→ℝ) (hf : ∀ a,0≤f a) :
    mean (conditionOn p E hE) f≤ mean p f/eventMass p E := by
  simp only [mean,Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  have hh:=mul_le_mul_of_nonneg_right (conditionOn_le p E hE a) (hf a)
  simpa only [div_mul_eq_mul_div] using hh

lemma mean_exists_ge (p : Law α) (f : α→ℝ) :
    ∃ a,0<p a ∧ mean p f≤f a := by
  by_contra! h
  have hex : ∃ a,0<p a := by
    have := p.sum_one
    by_contra! hn
    have hz : ∀ a,p a=0 := fun a=>le_antisymm (hn a) (p.nonneg a)
    simp [hz] at this
  obtain ⟨a,ha⟩:=hex
  have hh : mean p f< mean p (fun _=>mean p f) := by
    apply Finset.sum_lt_sum
    · intro b _
      by_cases hb : 0<p b
      · exact mul_le_mul_of_nonneg_left (h b hb).le (p.nonneg b)
      · have hz : p b=0 := le_antisymm (le_of_not_gt hb) (p.nonneg b)
        simp [hz]
    · exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left (h a ha) ha⟩
  rw [mean_const] at hh
  exact (lt_irrefl _ hh)

theorem fix_independent_table (p : Law α) (tables : Law β) (E : β→Finset α)
    (c : ℝ) (havg : c≤ mean tables (fun t=>eventMass p (E t))) :
    ∃ t,0<tables t ∧ c≤eventMass p (E t) := by
  obtain ⟨t,ht,he⟩:=mean_exists_ge tables (fun t=>eventMass p (E t))
  exact ⟨t,ht,havg.trans he⟩
end SharpRamseyFive.FiniteEntropy

end

end OAI
