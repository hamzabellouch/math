import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UnusedRepresentative

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

def freshBlockLaw (S : B → Finset A) : Law (B → A) :=
  piLaw fun b => if h : (S b).Nonempty then uniformOn (S b) h else uniformType A
lemma freshBlockLaw_eq (S : B → Finset A) (hS : ∀ b, (S b).Nonempty) :
    freshBlockLaw S = piLaw (fun b => uniformOn (S b) (hS b)) := by
  simp only [freshBlockLaw, dite_eq_left (hS _)]

def eraseBlock (S : B → Finset A) (s : B → A) : B → Finset A := fun b => (S b).erase (s b)

omit [Fintype B] [Fintype A] [Nonempty A] in
lemma eraseBlock_card (S : B → Finset A) (s : B → A) (n : ℕ)
    (hS : ∀ b, n+1 ≤ (S b).card) : ∀ b, n ≤ (eraseBlock S s b).card := by
  intro b
  have := hS b
  simp only [eraseBlock, Finset.card_erase_eq_ite]
  split_ifs <;> omega

def blockAllInformation (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (s : B → A) : ℝ :=
  (∑ b, ∑ a ∈ S b, (blockInformation p s b a : ℝ)) +
    ∑ t, (middleInformation p s t : ℝ)

omit [Nonempty A] in
lemma blockAllInformation_nonneg (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (s : B → A) : 0 ≤ blockAllInformation p S s := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
    (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)

lemma blockAllInformation_mean_le (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (hS : ∀ b, 2 ≤ (S b).card) :
    mean (freshBlockLaw S) (blockAllInformation p S) ≤
      2 * mean (freshBlockLaw S) (fun s => revealCost p (representativeSet s)) := by
  have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
  rw [freshBlockLaw_eq S hn]
  exact unused_information_le_twice_cost p S hn hS

def blockRoundMean
    (J : Law (((B × A) ⊕ T) → β) → (B → Finset A) → (B → A) → ℝ)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A) : (n : ℕ) → Fin n → ℝ
  | 0 => Fin.elim0
  | n+1 => Fin.cases (mean (freshBlockLaw S) (J p S)) (fun i =>
      mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => blockRoundMean J (fiber (reveal p (representativeSet s)) a)
          (eraseBlock S s) n i)))

lemma blockRoundMean_nonneg
    (J : Law (((B × A) ⊕ T) → β) → (B → Finset A) → (B → A) → ℝ)
    (hJ : ∀ p S s, 0 ≤ J p S s) (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (n : ℕ) (i : Fin n) : 0 ≤ blockRoundMean J p S n i := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact mean_nonneg _ _ (hJ p S)
    | succ i =>
      exact mean_nonneg _ _ fun s => mean_nonneg _ _ fun a => ih _ _ i

omit [Nonempty A] in
lemma mean_reveal_budget (p : Law (((B × A) ⊕ T) → β)) (μ : Law (B → A)) :
    mean μ (fun s => revealCost p (representativeSet s)) +
      mean μ (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) ≤
          totalCorrelation p := by
  rw [←mean_add]
  apply le_trans (mean_mono μ (fun s => reveal_information_budget p (representativeSet s)))
  exact (mean_const μ (totalCorrelation p)).le

theorem block_information_telescope
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (n : ℕ) (hS : ∀ b, n+1 ≤ (S b).card) :
    (∑ i : Fin n, blockRoundMean blockAllInformation p S n i) ≤ 2 * totalCorrelation p := by
  induction n generalizing p S with
  | zero => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (totalCorrelation_nonneg p)
  | succ n ih =>
    have hsize : ∀ b, 2 ≤ (S b).card := fun b => by have := hS b; omega
    have hn (s : B → A) : ∀ b, n+1 ≤ (eraseBlock S s b).card :=
      eraseBlock_card S s (n+1) hS
    have hcost := blockAllInformation_mean_le p S hsize
    have hbudget := mean_reveal_budget p (freshBlockLaw S)
    simp only [blockRoundMean, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    have htail :
        (∑ i : Fin n, mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => blockRoundMean blockAllInformation (fiber (reveal p (representativeSet s)) a)
            (eraseBlock S s) n i))) ≤
        2 * mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
      rw [←mean_sum]
      simp_rw [←mean_sum]
      calc
        _ ≤ mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => 2 * totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
            apply mean_mono
            intro s
            apply mean_mono
            intro a
            exact ih _ _ (hn s)
        _ = _ := by simp_rw [mean_smul]
    linarith only [htail,hcost,hbudget]

theorem exists_actual_pre_round (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (n : ℕ) (hn : 0<n) (hS : ∀ b, n+1 ≤ (S b).card) :
    ∃ i : Fin n, blockRoundMean blockAllInformation p S n i ≤ 2 * totalCorrelation p / n := by
  by_contra h
  push Not at h
  have hh : (∑ _i : Fin n, 2 * totalCorrelation p / n) <
      ∑ i : Fin n, blockRoundMean blockAllInformation p S n i := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩)
    intro i _
    exact h i
  have hc : (∑ _i : Fin n, 2 * totalCorrelation p / n) = 2 * totalCorrelation p := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
  rw [hc] at hh
  exact (not_lt_of_ge (block_information_telescope p S n hS)) hh
end
end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def support (p : Law α) : Finset α := Finset.univ.filter fun a => 0 < p a

lemma mem_support (p : Law α) (a : α) : a ∈ support p ↔ 0 < p a := by simp [support]

lemma outside_support (p : Law α) {a : α} (ha : a ∉ support p) : p a=0 := by
  exact le_antisymm (le_of_not_gt (fun h => ha ((mem_support p a).mpr h))) (p.nonneg a)

noncomputable def supportLaw (p : Law α) : Law (support p) where
  mass a := p a.val
  nonneg a := p.nonneg _
  sum_one := by
    rw [Finset.sum_coe_sort (support p)]
    calc
      _ = ∑ a,p a := Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => outside_support p ha)
      _ = 1 := p.sum_one

lemma map_supportLaw (p : Law α) : map (supportLaw p) Subtype.val = p := by
  apply Law.ext
  funext a
  change (∑ b : support p,if b.val=a then p b.val else 0)=p a
  rw [Finset.sum_coe_sort (support p) (fun b : α => if b=a then p b else 0)]
  by_cases h : a ∈ support p
  · simp [h]
  · have hz := outside_support p h
    simp [h,hz]

theorem entropy_le_log_support (p : Law α) : entropy p ≤ Real.log (support p).card := by
  have hh := entropy_le_log_card (supportLaw p)
  have he := entropy_map_injective (supportLaw p) Subtype.val Subtype.val_injective
  rw [map_supportLaw] at he
  rw [←he] at hh
  simpa only [Fintype.card_coe] using hh

lemma entropy_support_cap (p : Law α) (N : ℝ) (hN : (support p).card ≤ N) :
    entropy p ≤ Real.log N := by
  have hc : (0:ℝ) < (support p).card := by
    have he : Nonempty (support p) := by
      by_contra h
      have : IsEmpty (support p) := not_nonempty_iff.mp h
      simpa using (supportLaw p).sum_one
    have hh : 0<(support p).card := by simpa only [Fintype.card_coe] using Fintype.card_pos_iff.mpr he
    exact_mod_cast hh
  exact (entropy_le_log_support p).trans (Real.log_le_log hc hN)

theorem entropy_first_lower_of_partners (p : Law (α × β)) (N : ℝ)
    (hcap : ∀ a,0 < first p a → ((support (fiber p a)).card:ℝ) ≤ N) :
    entropy p-Real.log N ≤ entropy (first p) := by
  have hc : (∑ a,first p a*entropy (fiber p a)) ≤ Real.log N := by
    calc
      _ ≤ ∑ a,first p a*Real.log N := Finset.sum_le_sum fun a _ => by
        by_cases h : first p a=0
        · simp only [h,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (entropy_support_cap (fiber p a) N
            (hcap a (lt_of_le_of_ne ((first p).nonneg _) (Ne.symm h)))) ((first p).nonneg _)
      _ = _ := by rw [←Finset.sum_mul,(first p).sum_one,one_mul]
  rw [entropy_chain]
  linarith

noncomputable def eventProbability (p : Law α) (S : Finset α) : ℝ := ∑ a ∈ S,p a

theorem heavy_atom_mass (p : Law α) (N K : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hcap : ((support p).card:ℝ) ≤ N) :
    eventProbability p (Finset.univ.filter fun a => N*p a > Real.exp K) ≤
      (Real.log N-entropy p+1)/K := by
  let E := Finset.univ.filter fun a => N*p a > Real.exp K
  have hpoint (a : α) :
      (if a ∈ E then K*p a else 0)-(if a ∈ support p then 1/N else 0) ≤
        p a*Real.log (N*p a) := by
    by_cases hp : p a=0
    · have hE : a ∉ E := by simp only [E,Finset.mem_filter,Finset.mem_univ,true_and,hp,mul_zero]; exact (Real.exp_pos K).not_gt
      have hs : a ∉ support p := by simp [mem_support,hp]
      simp only [hp,hE,hs,ite_false,sub_zero,zero_mul,le_refl]
    · have hp' := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hs := (mem_support p a).mpr hp'
      by_cases he : a ∈ E
      · have hh : Real.exp K < N*p a := (Finset.mem_filter.mp he).2
        have hl : K ≤ Real.log (N*p a) := (Real.le_log_iff_exp_le (by positivity)).mpr hh.le
        simp only [he,hs,ite_true]
        nlinarith [mul_le_mul_of_nonneg_right hl (p.nonneg a),div_pos zero_lt_one hN]
      · have hh := point_log_ratio (p a) (1/N) (p.nonneg a) (by positivity) (fun _ => by positivity)
        have heq : p a/(1/N)=N*p a := by field_simp
        rw [heq] at hh
        simp only [he,hs,ite_false,ite_true,zero_sub]
        nlinarith [p.nonneg a]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hlog : (∑ a,p a*Real.log (N*p a))=Real.log N-entropy p := by
    calc
      _ = ∑ a,(p a*Real.log N+p a*Real.log (p a)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hp : p a=0
        · simp [hp]
        · rw [Real.log_mul (ne_of_gt hN) hp]
          ring
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one,one_mul]; simp only [entropy,sub_neg_eq_add]
  rw [Finset.sum_sub_distrib,hlog] at h
  have he : (∑ a,if a ∈ E then K*p a else 0)=K*eventProbability p E := by
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    simp only [eventProbability,Finset.mul_sum]
  have hs : (∑ a,if a ∈ support p then 1/N else 0)=((support p).card:ℝ)/N := by
    rw [Finset.sum_ite_mem]
    simp [div_eq_mul_inv]
  rw [he,hs] at h
  have hfrac : ((support p).card:ℝ)/N ≤ 1 := (div_le_one hN).mpr hcap
  apply (le_div_iff₀ hK).mpr
  dsimp [E] at h
  nlinarith

end SharpRamseyFive.FiniteEntropy

end OAI
