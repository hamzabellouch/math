import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductSmallTail
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeResidueChannel

namespace OAI

/-! # Exact equivalence of prime-site and prime-subset probabilities -/

namespace JointDickman

open Finset

noncomputable def selectedPrimeSubset (Q : Finset ℕ) (x : Q → Bool) : Finset ℕ :=
  Q.filter (fun p => if hp : p ∈ Q then x ⟨p, hp⟩ = true else False)

@[simp] theorem selectedPrimeSubset_mem (Q : Finset ℕ) (x : Q → Bool) (p : Q) :
    p.val ∈ selectedPrimeSubset Q x ↔ x p = true := by
  simp [selectedPrimeSubset, p.property]

theorem selectedPrimeSubset_subset (Q : Finset ℕ) (x : Q → Bool) :
    selectedPrimeSubset Q x ⊆ Q := filter_subset _ _

theorem selectedPrimeSubset_injective (Q : Finset ℕ) : Function.Injective (selectedPrimeSubset Q) := by
  intro x y hxy
  funext p
  have h : x p = true ↔ y p = true := by
    rw [← selectedPrimeSubset_mem Q x p, ← selectedPrimeSubset_mem Q y p, hxy]
  cases hx : x p <;> cases hy : y p <;> simp_all

open Classical in
theorem selectedPrimeSubset_surjective (Q S : Finset ℕ) (hS : S ⊆ Q) :
    ∃ x : Q → Bool, selectedPrimeSubset Q x = S := by
  refine ⟨fun p => decide (p.val ∈ S), ?_⟩
  ext p
  by_cases hp : p ∈ Q
  · simp [selectedPrimeSubset, hp]
  · have hpS : p ∉ S := fun h => hp (hS h)
    simp [selectedPrimeSubset, hp, hpS]

theorem retainedPrimeProduct_selected (Q : Finset ℕ) (x : Q → Bool) :
    retainedPrimeProduct Q x = ∏ p ∈ selectedPrimeSubset Q x, p := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then p.val else 1 := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then p else 1 :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then p else 1)
    _ = _ := by rw [prod_ite, hfilter]; simp

theorem bernoulliSiteMass_selected (Q : Finset ℕ) (q : ℕ → ℝ) (x : Q → Bool) :
    bernoulliSiteMass (fun p : Q => q p.val) x = bernoulliSubsetMass Q q (selectedPrimeSubset Q x) := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  have hfilter' : Q.filter (fun p => p ∉ selectedPrimeSubset Q x) = Q \ selectedPrimeSubset Q x := by
    ext p
    simp
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then q p.val else 1 - q p.val := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
      cases x p <;> rfl
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then q p else 1 - q p :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then q p else 1 - q p)
    _ = _ := by rw [prod_ite, hfilter, hfilter']; rfl

open Classical in
/-- This equality transfers every event, not just an interval or a residue class. -/
theorem bernoulliPrimeSite_event (Q : Finset ℕ) (q : ℕ → ℝ) (A : ℕ → Prop) :
    (∑ x : Q → Bool, if A (retainedPrimeProduct Q x) then
      bernoulliSiteMass (fun p : Q => q p.val) x else 0) =
      ∑ S ∈ Q.powerset, if A (∏ p ∈ S, p) then bernoulliSubsetMass Q q S else 0 := by
  apply sum_bij (fun x _ => selectedPrimeSubset Q x)
  · intro x _
    exact mem_powerset.mpr (selectedPrimeSubset_subset Q x)
  · intro x _ y _ h
    exact selectedPrimeSubset_injective Q h
  · intro S hS
    obtain ⟨x, hx⟩ := selectedPrimeSubset_surjective Q S (mem_powerset.mp hS)
    exact ⟨x, mem_univ _, hx⟩
  · intro x _
    rw [retainedPrimeProduct_selected, bernoulliSiteMass_selected]

open Classical in
theorem quarterPrimeMass_small_log_tail
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ x : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ≤ δ then
          quarterPrimeMass (auxiliaryPrimes B) x else 0) ≤
        C * (δ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := primeProduct_small_log_tail hM
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hB
  intro δ hδ hδ1
  have heq (x : auxiliaryPrimes B → Bool) :
      quarterPrimeMass (auxiliaryPrimes B) x =
        bernoulliSiteMass (fun p : auxiliaryPrimes B => (1 / 4 : ℝ) / p.val) x := by
    unfold quarterPrimeMass
    congr 1
    funext p
    ring
  simp_rw [heq]
  rw [bernoulliPrimeSite_event (auxiliaryPrimes B) (fun p : ℕ => (1 / 4 : ℝ) / p)
    (fun n : ℕ => Real.log n / B ≤ δ)]
  exact hB δ hδ hδ1


open Classical in
theorem primeSiteMass_event (Q : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ x : Q → Bool, if retainedPrimeProduct Q x ∈ K then
      bernoulliSiteMass (fun p : Q => z / p.val) x else 0) =
      ∑ n ∈ K, primeProductMass Q z n := by
  rw [primeProductMass_sum_event]
  have h := bernoulliPrimeSite_event Q (fun p : ℕ => z / p) (fun n => n ∈ K)
  convert h using 1 <;> apply sum_congr rfl <;> intro n _ <;> split_ifs <;> rfl

theorem quarterPrimeMass_eq (Q : Finset ℕ) (x : Q → Bool) :
    quarterPrimeMass Q x = bernoulliSiteMass (fun p : Q => (1 / 4 : ℝ) / p.val) x := by
  unfold quarterPrimeMass
  congr 1
  funext p
  ring

theorem retainedPrimeProduct_pos (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 < retainedPrimeProduct Q x := by
  rw [retainedPrimeProduct_selected]
  exact prod_pos (fun p hp => (hQ p (selectedPrimeSubset_subset Q x hp)).pos)

theorem retainedPrimeProduct_coprime (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {q : ℕ} (hq : q ≠ 0) (hcut : ∀ p ∈ Q, q < p) (x : Q → Bool) :
    (retainedPrimeProduct Q x).Coprime q := by
  rw [retainedPrimeProduct_selected, Nat.coprime_prod_left_iff]
  intro p hp
  have hpQ := selectedPrimeSubset_subset Q x hp
  apply (hQ p hpQ).coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt (hcut p hpQ)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdiv)

end JointDickman

end OAI
