import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockReveal

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]
local instance : DecidableEq ι := Classical.decEq _
local instance (E : Finset ι) : DecidableEq E := Classical.decEq _

lemma mean_mono_pos {α : Type*} [Fintype α] (p : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < p a → f a ≤ g a) : mean p f ≤ mean p g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hz : p a = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a)

lemma reveal_positive (p : Law (ι → β)) (E : Finset ι) (a : E → β) (x : ι → β)
    (h : 0 < reveal p E (a,x)) : 0 < p x ∧ (fun i : E => x i.val) = a := by
  obtain ⟨y,hy,he⟩ := map_positive p (fun y => ((fun i : E => y i.val),y)) (a,x) h
  have hxy : y = x := congrArg Prod.snd he
  subst y
  exact ⟨hy,congrArg Prod.fst he⟩

lemma fiber_reveal_support (p : Law (ι → β)) (E : Finset ι) (a : E → β)
    (x : ι → β) (hx : 0 < fiber (reveal p E) a x) : 0 < p x := by
  by_cases ha : 0 < first (reveal p E) a
  · apply (reveal_positive p E a x _).1
    rw [mass_eq_first_mul_fiber]
    exact mul_pos ha hx
  · simpa only [fiber, dite_eq_right ha, second_reveal] using hx

lemma fiber_reveal_agrees (p : Law (ι → β)) (E : Finset ι) (a : E → β)
    (ha : 0 < first (reveal p E) a) (x : ι → β)
    (hx : 0 < fiber (reveal p E) a x) : (fun i : E => x i.val) = a := by
  apply (reveal_positive p E a x _).2
  rw [mass_eq_first_mul_fiber]
  exact mul_pos ha hx

def InDomains (p : Law (ι → β)) (D : ι → Finset β) : Prop :=
  ∀ x, 0 < p x → ∀ i, x i ∈ D i

lemma InDomains.fiber {p : Law (ι → β)} {D : ι → Finset β} (h : InDomains p D)
    (E : Finset ι) (a : E → β) : InDomains (fiber (reveal p E) a) D := by
  intro x hx i
  exact h x (fiber_reveal_support p E a x hx) i

lemma InDomains.entropy_cap {p : Law (ι → β)} {D : ι → Finset β}
    (h : InDomains p D) (J : ℝ) (hJ : ∀ i, Real.log (D i).card ≤ J) (i : ι) :
    entropy (map p (fun x => x i)) ≤ J := by
  apply le_trans (entropy_support_cap _ (D i).card _) (hJ i)
  exact_mod_cast Finset.card_le_card (show support (map p (fun x => x i)) ⊆ D i from by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := map_positive p (fun x => x i) b ((mem_support _ _).mp hb)
    exact h x hx i)

def FixedOutside (p : Law (ι → β)) (U : Finset ι) : Prop :=
  ∀ i, i ∉ U → ∃ b, ∀ x, 0 < p x → x i = b

lemma constant_coordinate_entropy (p : Law (ι → β)) (i : ι) (b : β)
    (h : ∀ x, 0 < p x → x i = b) : entropy (map p (fun x => x i)) = 0 := by
  apply le_antisymm _ (entropy_nonneg _)
  calc
    _ ≤ Real.log (1 : ℝ) := entropy_support_cap _ 1 (by
      have hs : support (map p (fun x => x i)) ⊆ {b} := by
        intro c hc
        obtain ⟨x,hx,rfl⟩ := map_positive p (fun x => x i) c ((mem_support _ _).mp hc)
        simp only [Finset.mem_singleton]
        exact h x hx
      have := Finset.card_le_card hs
      simpa using (Nat.cast_le (α := ℝ)).mpr this)
    _ = 0 := Real.log_one

lemma FixedOutside.entropy_zero {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) (i : ι) (hi : i ∉ U) : entropy (map p (fun x => x i)) = 0 := by
  obtain ⟨b,hb⟩ := h i hi
  exact constant_coordinate_entropy p i b hb

lemma FixedOutside.fiber {p : Law (ι → β)} {U : Finset ι} (h : FixedOutside p U)
    (E : Finset ι) (a : E → β) (ha : 0 < first (reveal p E) a) :
    FixedOutside (fiber (reveal p E) a) (U \ E) := by
  intro i hi
  by_cases he : i ∈ E
  · refine ⟨a ⟨i,he⟩,fun x hx => ?_⟩
    exact congrFun (fiber_reveal_agrees p E a ha x hx) ⟨i,he⟩
  · have hu : i ∉ U := fun hu => hi (Finset.mem_sdiff.mpr ⟨hu,he⟩)
    obtain ⟨b,hb⟩ := h i hu
    exact ⟨b,fun x hx => hb x (fiber_reveal_support p E a x hx)⟩

lemma FixedOutside.entropy_le_sum {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) : entropy p ≤ ∑ i ∈ U, entropy (map p (fun x => x i)) := by
  have ht := totalCorrelation_nonneg p
  have he : (∑ i, entropy (map p (fun x => x i))) =
      ∑ i ∈ U, entropy (map p (fun x => x i)) := by
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => h.entropy_zero i hi)).symm
  change 0 ≤ (∑ i, entropy (map p (fun x => x i))) - entropy p at ht
  rw [he] at ht
  exact sub_nonneg.mp ht

def activeDeficit (p : Law (ι → β)) (U : Finset ι) (J : ℝ) : ℝ :=
  U.card * J - entropy p

def marginalDeficit (p : Law (ι → β)) (U : Finset ι) (J : ℝ) : ℝ :=
  ∑ i ∈ U, (J - entropy (map p (fun x => x i)))

lemma marginalDeficit_le_active {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) (J : ℝ) : marginalDeficit p U J ≤ activeDeficit p U J := by
  have hh := h.entropy_le_sum
  simp only [marginalDeficit, activeDeficit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

lemma activeDeficit_reveal (p : Law (ι → β)) (U E : Finset ι) (hEU : E ⊆ U)
    (J : ℝ) (hc : ∀ i ∈ E, entropy (map p (fun x => x i)) ≤ J) :
    mean (first (reveal p E)) (fun a => activeDeficit (fiber (reveal p E) a) (U \ E) J) ≤
      activeDeficit p U J := by
  have hcap : entropy (first (reveal p E)) ≤ (E.card : ℝ) * J := by
    apply (entropy_reveal_le_coordinate_sum p E).trans
    calc
      _ ≤ ∑ _i ∈ E,J := Finset.sum_le_sum hc
      _ = _ := by simp
  have hh := conditional_deficit_le (reveal p E) ((E.card : ℝ)*J) (((U \ E).card : ℝ)*J) hcap
  rw [entropy_reveal] at hh
  have hcard : ((E.card : ℝ) + (U \ E).card) = U.card := by
    simpa only [add_comm] using (show ((U \ E).card : ℝ) + E.card = U.card by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hEU)
  simpa only [activeDeficit, mean, ←add_mul, hcard] using hh
end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

def blockActive (S : B → Finset A) : Finset ((B × A) ⊕ T) :=
  Finset.univ.filter fun i => Sum.elim (fun z : B × A => z.2 ∈ S z.1) (fun _ => True) i

omit [Nonempty A] in
lemma mem_blockActive_left (S : B → Finset A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ blockActive (T := T) S ↔ a ∈ S b := by simp [blockActive]
omit [Nonempty A] in
lemma mem_blockActive_right (S : B → Finset A) (t : T) :
    Sum.inr t ∈ blockActive S := by simp [blockActive]

lemma freshBlockLaw_supported (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) (hs : 0 < freshBlockLaw S s) : ∀ b, s b ∈ S b := by
  intro b
  by_contra h
  rw [freshBlockLaw_eq S hS,piLaw_uniformOn_zero S hS s h] at hs
  exact lt_irrefl _ hs

omit [Nonempty A] in
lemma representativeSet_subset_active (S : B → Finset A) (s : B → A)
    (hs : ∀ b, s b ∈ S b) : representativeSet (T := T) s ⊆ blockActive S := by
  intro i hi
  simp only [representativeSet, Finset.mem_image, Finset.mem_univ, true_and] at hi
  obtain ⟨b,rfl⟩ := hi
  exact (mem_blockActive_left S b (s b)).mpr (hs b)

omit [Nonempty A] in
lemma blockActive_erase (S : B → Finset A) (s : B → A) :
    blockActive (T := T) (eraseBlock S s) = blockActive S \ representativeSet s := by
  ext i
  cases i with
  | inl x => rcases x with ⟨b,a⟩; simp [blockActive,eraseBlock,representativeSet, and_comm, eq_comm]
  | inr t => simp [blockActive,representativeSet]

def blockAllDeficit (J : ℝ) (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (_s : B → A) : ℝ := marginalDeficit p (blockActive S) J

theorem block_round_deficit (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hp : InDomains p D) (hfix : FixedOutside p (blockActive S))
    (n : ℕ) (hS : ∀ b, n ≤ (S b).card) (i : Fin n) :
    blockRoundMean (blockAllDeficit J) p S n i ≤ activeDeficit p (blockActive S) J := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
    cases i using Fin.cases with
    | zero =>
      change mean (freshBlockLaw S) (fun _ => marginalDeficit p (blockActive S) J) ≤ _
      rw [mean_const]
      exact marginalDeficit_le_active hfix J
    | succ i =>
      change mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => blockRoundMean (blockAllDeficit J) (fiber (reveal p (representativeSet s)) a)
          (eraseBlock S s) n i)) ≤ _
      apply le_trans (mean_mono_pos (freshBlockLaw S) (fun s hs => ?_))
        (mean_const (freshBlockLaw S) (activeDeficit p (blockActive S) J)).le
      have he : representativeSet (T := T) s ⊆ blockActive S :=
        representativeSet_subset_active S s (freshBlockLaw_supported S hn s hs)
      calc
        _ ≤ mean (first (reveal p (representativeSet s)))
          (fun a => activeDeficit (fiber (reveal p (representativeSet s)) a)
            (blockActive (eraseBlock S s)) J) := by
            apply mean_mono_pos
            intro a ha
            apply ih _ _ (hp.fiber _ _)
            · rw [blockActive_erase]
              exact hfix.fiber _ _ ha
            · exact eraseBlock_card S s n hS
        _ ≤ activeDeficit p (blockActive S) J := by
          rw [blockActive_erase]
          exact activeDeficit_reveal p (blockActive S) (representativeSet s) he J
            (fun j _ => hp.entropy_cap J hJ j)

theorem exists_actual_pre_round_with_deficit (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hp : InDomains p D) (hfix : FixedOutside p (blockActive S))
    (n : ℕ) (hn : 0<n) (hS : ∀ b, n+1 ≤ (S b).card) :
    ∃ i : Fin n,
      blockRoundMean blockAllInformation p S n i ≤ 2 * totalCorrelation p / n ∧
      blockRoundMean (blockAllDeficit J) p S n i ≤ activeDeficit p (blockActive S) J := by
  obtain ⟨i,hi⟩ := exists_actual_pre_round p S n hn hS
  exact ⟨i,hi,block_round_deficit J D hJ p S hp hfix n (fun b => by have := hS b; omega) i⟩
end SharpRamseyFive.FiniteEntropy

end

end OAI
