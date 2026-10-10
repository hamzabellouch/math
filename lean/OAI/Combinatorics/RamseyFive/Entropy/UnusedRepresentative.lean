import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RepresentativeSet
import OAI.Combinatorics.RamseyFive.Entropy.ProductHistory

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
local instance : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

lemma uniformOn_expectation (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (∑ a, uniformOn S hS a * f a) = (S.card : ℝ)⁻¹ * ∑ a ∈ S, f a := by
  simp only [uniformOn]
  calc
    _ = ∑ a, if a ∈ S then (S.card : ℝ)⁻¹ * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by rw [←Finset.sum_filter, Finset.filter_univ_mem, Finset.mul_sum]

lemma piLaw_uniformOn_zero (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) {b : B} (h : s b ∉ S b) :
    piLaw (fun b => uniformOn (S b) (hS b)) s = 0 := by
  classical
  change (∏ b, uniformOn (S b) (hS b) (s b)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [uniformOn,h])

theorem unused_selected_identity (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (S b).card * (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * f s b (s b)) =
      ∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a) := by
  classical
  rw [independent_selected_identity _ f hown]
  simp_rw [uniformOn_expectation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hc : ((S b).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hS b))
  field_simp

theorem unused_all_le_twice_unselected (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card)
    (f : (B → A) → B → A → ℝ) (hf : ∀ s b a, 0 ≤ f s b a)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a)) ≤
      2*(∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s *
        (∑ a ∈ (S b).erase (s b), f s b a)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hi := unused_selected_identity S hS f hown b
  have hs : (∑ s, w s * (∑ a ∈ S b, f s b a)) =
      (∑ s, w s * f s b (s b)) +
      (∑ s, w s * (∑ a ∈ (S b).erase (s b), f s b a)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s b ∈ S b
    · rw [←mul_add, Finset.add_sum_erase _ _ h]
    · have hz : w s = 0 := piLaw_uniformOn_zero S hS s h
      simp [hz]
  have hn : 0 ≤ ∑ s, w s * f s b (s b) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s) (hf s b (s b))
  have hc : (2 : ℝ) ≤ (S b).card := by exact_mod_cast hsize b
  change (S b).card * (∑ s, w s * f s b (s b)) = _ at hi
  change (∑ s, w s * (∑ a ∈ S b, f s b a)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hc hn]

theorem unused_information_le_twice_cost
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card) :
    (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
      ((∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ)) +
        ∑ t : T, (middleInformation p s t : ℝ))) ≤
      2 * (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
        revealCost p (representativeSet s)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hb := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) =>
    unused_all_le_twice_unselected S hS hsize
      (fun s b a => (blockInformation p s b a : ℝ))
      (fun _ _ _ => NNReal.coe_nonneg _) (fun s b a i =>
        congrArg NNReal.toReal (blockInformation_own_independent p s b a i)) b)
  have hc (s : B → A) :
      (∑ b : B, ∑ a ∈ (S b).erase (s b), (blockInformation p s b a : ℝ)) +
      (∑ t : T, (middleInformation p s t : ℝ)) ≤ revealCost p (representativeSet s) := by
    apply le_trans _ (representative_unselected_le_cost p s)
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.erase_subset_erase (s b) (Finset.subset_univ _)
    · intro a _ _
      exact NNReal.coe_nonneg _
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (B → A))) =>
    mul_le_mul_of_nonneg_left (hc s) (w.nonneg s))
  have hm : 0 ≤ ∑ s : B → A, w s * ∑ t : T, (middleInformation p s t : ℝ) := by
    exact Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s)
      (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
  have hb' :
      (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ))) ≤
      2 * (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := by
    calc
      _ = ∑ b : B, ∑ s : B → A, w s * (∑ a ∈ S b, (blockInformation p s b a : ℝ)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ b : B, 2 * (∑ s : B → A, w s * (∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := hb
      _ = _ := by
        rw [←Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
  change (∑ s : B → A, w s * _) ≤ 2 * (∑ s : B → A, w s * _)
  simp only [mul_add, Finset.sum_add_distrib] at hh ⊢
  linarith only [hb',hh,hm]

end

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

def mean (p : Law α) (f : α → ℝ) : ℝ := ∑ a, p a * f a
lemma mean_nonneg (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ mean p f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf a)
lemma mean_mono (p : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : mean p f ≤ mean p g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)
lemma mean_const (p : Law α) (c : ℝ) : mean p (fun _ => c) = c := by
  rw [mean, ←Finset.sum_mul, p.sum_one, one_mul]
lemma mean_add (p : Law α) (f g : α → ℝ) : mean p (fun a => f a + g a) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]
lemma mean_sub (p : Law α) (f g : α → ℝ) : mean p (fun a => f a - g a) = mean p f - mean p g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]
lemma mean_smul (p : Law α) (c : ℝ) (f : α → ℝ) : mean p (fun a => c * f a) = c * mean p f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]
lemma mean_congr (p : Law α) {f g : α → ℝ} (h : ∀ a, f a = g a) : mean p f = mean p g := by
  exact Finset.sum_congr rfl fun a _ => congrArg (fun x => p a*x) (h a)
lemma mean_finset_sum {ι : Type*} (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm
lemma mean_sum {ι : Type*} [Fintype ι] (p : Law α) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i, f i a) = ∑ i, mean p (f i) := mean_finset_sum p Finset.univ f
lemma mean_map (p : Law α) (g : α → β) (f : β → ℝ) : mean (map p g) f = mean p (fun a => f (g a)) := by
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp
lemma mean_adaptive (p : Law α) (q : α → Law β) (f : α × β → ℝ) :
    mean (adaptiveLaw p q) f = mean p (fun a => mean (q a) (fun b => f (a,b))) := by
  simp only [mean, adaptiveLaw, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
end SharpRamseyFive.FiniteEntropy

end

end OAI
