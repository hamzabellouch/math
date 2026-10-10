import OAI.Combinatorics.FiniteCircle.DyadicShifts

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem few_large_prime_divisors {h : ℕ} (hh : 2 ≤ h)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) {β : ℤ} (hβ : β ≠ 0)
    (hsmall : β.natAbs < h ^ h) :
    3 * ((Finset.univ.filter fun i => (p i : ℤ) ∣ β).card) < h := by
  let s := Finset.univ.filter fun i => (p i : ℤ) ∣ β
  have hdvd : (∏ i ∈ s, p i) ∣ β.natAbs := by
    have heq : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      Finset.prod_image (fun _ _ _ _ hij => hinj hij)
    rw [← heq]
    apply Finset.prod_primes_dvd
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (hp i).prime
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact Int.natCast_dvd.mp (Finset.mem_filter.mp hi).2
  have hprod : h ^ (3 * s.card) ≤ β.natAbs := by
    calc
      h ^ (3 * s.card) = ∏ i ∈ s, h ^ 3 := by simp [pow_mul]
      _ ≤ ∏ i ∈ s, p i := Finset.prod_le_prod (fun i _ => hlarge i)
      _ ≤ β.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hβ) hdvd
  by_contra hn
  have hge : h ≤ 3 * s.card := Nat.le_of_not_gt hn
  have : h ^ h ≤ h ^ (3 * s.card) := Nat.pow_le_pow_right (by omega) hge
  omega

theorem many_mask_children {h : ℕ} (hh : 2 ≤ h) (p : Fin h → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) (f : (Σ k : Fin h, Fin (p k)) → ℤ)
    {β : ℤ} (hβ : β ≠ 0) (hsmall : β.natAbs < h ^ h)
    (hc : ∀ k, (p k : ℤ) ∣ β + ∑ b : Fin (p k), (b.val : ℤ) * f ⟨k, b⟩) :
    h ≤ 2 * (Finset.univ.filter fun j => f j ≠ 0).card := by
  classical
  let s := Finset.univ.filter fun j => f j ≠ 0
  let t := Finset.univ.filter fun k => ¬ (p k : ℤ) ∣ β
  let q := Finset.univ.filter fun k => (p k : ℤ) ∣ β
  have hq : 3 * q.card < h := few_large_prime_divisors hh p hp hinj hlarge hβ hsmall
  have ht : t ⊆ s.image Sigma.fst := by
    intro k hk
    have hk' : ¬ (p k : ℤ) ∣ β := (Finset.mem_filter.mp hk).2
    have hex : ∃ b : Fin (p k), f ⟨k, b⟩ ≠ 0 := by
      by_contra hn
      push Not at hn
      have hc' := hc k
      simp only [hn, mul_zero, Finset.sum_const_zero, add_zero] at hc'
      exact hk' hc'
    obtain ⟨b, hb⟩ := hex
    exact Finset.mem_image.mpr ⟨⟨k, b⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
  have hcard : t.card ≤ s.card :=
    (Finset.card_le_card ht).trans (Finset.card_image_le)
  have hcount : q.card + t.card = h := by
    simpa [q, t] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin h))) (fun k => (p k : ℤ) ∣ β))
  change h ≤ 2 * s.card
  omega

def FrequencyTree (J : ℕ → Type) : ℕ → Type _
  | 0 => ℤ
  | l + 1 => J (l + 1) → FrequencyTree J l

noncomputable def frequencySum (J : ℕ → Type) [∀ l, Fintype (J l)] :
    (l : ℕ) → FrequencyTree J l → ℤ
  | 0, t => t
  | l + 1, t => ∑ j, frequencySum J l (t j)

noncomputable def frequencyMass (J : ℕ → Type) [∀ l, Fintype (J l)] :
    (l : ℕ) → FrequencyTree J l → ℕ
  | 0, t => (show ℤ from t).natAbs
  | l + 1, t => ∑ j, frequencyMass J l (t j)

theorem frequencySum_natAbs_le_mass (J : ℕ → Type) [∀ l, Fintype (J l)]
    (l : ℕ) (t : FrequencyTree J l) :
    (frequencySum J l t).natAbs ≤ frequencyMass J l t := by
  induction l with
  | zero => exact le_rfl
  | succ l ih =>
    exact (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ih (t j))

def MaskChildren (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := Σ k : Fin h, Fin (p l k)

instance maskChildrenFintype (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype (MaskChildren h p l) := inferInstanceAs (Fintype (Σ k : Fin h, Fin (p l k)))

noncomputable def MaskCongruences (h : ℕ) (p : ℕ → ℕ → ℕ) :
    (l : ℕ) → FrequencyTree (MaskChildren h p) l → Prop
  | 0, _ => True
  | l + 1, t =>
    (∀ k : Fin h, (p (l + 1) k : ℤ) ∣ frequencySum (MaskChildren h p) (l + 1) t +
      ∑ b : Fin (p (l + 1) k), (b.val : ℤ) * frequencySum (MaskChildren h p) l (t ⟨k, b⟩)) ∧
    ∀ j, MaskCongruences h p l (t j)

theorem mask_branching_induction {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (l : ℕ) (hl : l ≤ h) (t : FrequencyTree (MaskChildren h p) l)
    (hc : MaskCongruences h p l t)
    (hroot : frequencySum (MaskChildren h p) l t ≠ 0)
    (hsmall : frequencyMass (MaskChildren h p) l t < h ^ h) :
    ((h : ℝ) / 2) ^ l ≤ (frequencyMass (MaskChildren h p) l t : ℝ) := by
  classical
  induction l with
  | zero =>
    have : 1 ≤ frequencyMass (MaskChildren h p) 0 t :=
      (Int.natAbs_pos.mpr hroot).trans_le (frequencySum_natAbs_le_mass _ _ _)
    simpa using (show (1 : ℝ) ≤ frequencyMass (MaskChildren h p) 0 t by exact_mod_cast this)
  | succ l ih =>
    let f : MaskChildren h p (l + 1) → ℤ := fun j => frequencySum (MaskChildren h p) l (t j)
    let s := Finset.univ.filter fun j => f j ≠ 0
    have hsumSmall : (frequencySum (MaskChildren h p) (l + 1) t).natAbs < h ^ h :=
      (frequencySum_natAbs_le_mass _ _ _).trans_lt hsmall
    have hcard : h ≤ 2 * s.card :=
      many_mask_children hh (fun k => p (l + 1) k)
        (fun k => hp _ k (by omega) hl) (hinj _ (by omega) hl)
        (fun k => hlarge _ k (by omega) hl) f hroot hsumSmall hc.1
    have hchild : ∀ j, frequencyMass (MaskChildren h p) l (t j) < h ^ h := by
      intro j
      apply lt_of_le_of_lt _ hsmall
      change frequencyMass (MaskChildren h p) l (t j) ≤ ∑ j, frequencyMass (MaskChildren h p) l (t j)
      exact Finset.single_le_sum (f := fun j => frequencyMass (MaskChildren h p) l (t j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hm : ∀ j ∈ s, ((h : ℝ) / 2) ^ l ≤ frequencyMass (MaskChildren h p) l (t j) := by
      intro j hj
      exact ih (by omega) (t j) (hc.2 j) (Finset.mem_filter.mp hj).2 (hchild j)
    have hcardR : (h : ℝ) / 2 ≤ s.card := by
      have : (h : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hcard
      linarith
    calc
      ((h : ℝ) / 2) ^ (l + 1) = ((h : ℝ) / 2) * ((h : ℝ) / 2) ^ l := by ring
      _ ≤ s.card * ((h : ℝ) / 2) ^ l := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = ∑ j ∈ s, ((h : ℝ) / 2) ^ l := by simp
      _ ≤ ∑ j ∈ s, (frequencyMass (MaskChildren h p) l (t j) : ℝ) := Finset.sum_le_sum hm
      _ ≤ ∑ j, (frequencyMass (MaskChildren h p) l (t j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = (frequencyMass (MaskChildren h p) (l + 1) t : ℝ) := by
        simp only [frequencyMass, Nat.cast_sum]

theorem mask_frequency_branching {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (t : FrequencyTree (MaskChildren h p) h) (hc : MaskCongruences h p h t)
    (hroot : frequencySum (MaskChildren h p) h t ≠ 0) :
    ((h : ℝ) / 2) ^ h ≤ (frequencyMass (MaskChildren h p) h t : ℝ) := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hcap : ((h : ℝ) / 2) ^ h ≤ (h : ℝ) ^ h := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith
  have hsmall : frequencyMass (MaskChildren h p) h t < h ^ h := by
    exact_mod_cast hlt.trans_le hcap
  exact (not_lt_of_ge (mask_branching_induction hh p hp hinj hlarge h le_rfl t hc hroot hsmall)) hlt

attribute [reducible] MaskChildren

end FiniteCircle

end OAI
