import OAI.NumberTheory.Ostmann.Supply.CenteredBudget
import OAI.NumberTheory.Ostmann.Supply.TensorModeEnergy

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped BigOperators

theorem indexPrimeProduct_injOn (p : ℕ → ℕ) (n : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ)) :
    Set.InjOn (fun s : Finset ℕ => ∏ i ∈ s, p i) ((range n).powerset : Set (Finset ℕ)) := by
  have hpf (s : Finset ℕ) (hs : s ⊆ range n) :
      (∏ i ∈ s, p i).primeFactors = s.image p := by
    have hprod : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      prod_image (f := fun q : ℕ => q) (fun i hi j hj hij => hinj (hs hi) (hs hj) hij)
    rw [← hprod]
    apply Nat.primeFactors_prod
    intro q hq
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
    exact hp i (mem_range.mp (hs hi))
  intro s hs t ht hprod
  change (∏ i ∈ s, p i) = (∏ i ∈ t, p i) at hprod
  have hss := mem_powerset.mp hs
  have htt := mem_powerset.mp ht
  have himage : s.image p = t.image p := by rw [← hpf s hss, ← hpf t htt, hprod]
  apply Finset.Subset.antisymm
  · intro i hi
    have hip : p i ∈ t.image p := by rw [← himage]; exact mem_image_of_mem p hi
    obtain ⟨j, hj, hji⟩ := mem_image.mp hip
    have he : j = i := hinj (htt hj) (hss hi) hji
    simpa only [he] using hj
  · intro i hi
    have hip : p i ∈ s.image p := by rw [himage]; exact mem_image_of_mem p hi
    obtain ⟨j, hj, hji⟩ := mem_image.mp hip
    have he : j = i := hinj (hss hj) (htt hi) hji
    simpa only [he] using hj

def retainedProducts (p : ℕ → ℕ) (n K : ℕ) : Finset ℕ :=
  (retainedModes n K).image (fun s => ∏ i ∈ s, p i)

theorem norm_residue_lowModes_sq_eq_product_sum (A : Finset ℕ) (p : ℕ → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ p : ℕ, Finset (ZMod p)) (n K : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ)) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (residueCenteredVector p S) n)‖^2 =
      ∑ t ∈ retainedProducts p n K, centeredEnergy A S t := by
  rw [norm_residue_lowModes_sq A p S n K hp hinj]
  symm
  exact sum_image (fun s hs t ht h => indexPrimeProduct_injOn p n hp hinj
    (mem_filter.mp hs).1 (mem_filter.mp ht).1 h)

theorem norm_residue_lowModes_sq_le_sum (A : Finset ℕ) (p : ℕ → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ p : ℕ, Finset (ZMod p)) (n K : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ))
    (T : Finset ℕ) (hT : retainedProducts p n K ⊆ T) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (residueCenteredVector p S) n)‖^2 ≤
      ∑ t ∈ T, centeredEnergy A S t := by
  rw [norm_residue_lowModes_sq_eq_product_sum A p S n K hp hinj]
  exact sum_le_sum_of_subset_of_nonneg hT (fun t ht hnot => centeredEnergy_nonneg A S t)

theorem norm_residue_lowModes_sq_le_budget (A : Finset ℕ) (hAn : A.Nonempty)
    (p : ℕ → ℕ) [∀ i, NeZero (p i)] (S : ∀ p : ℕ, Finset (ZMod p)) (n K R : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ))
    (hR : 0 < R) (hA : ∀ a ∈ A, a ≤ R^2)
    (hS : ∀ a ∈ A, ∀ p, p.Prime → p ≤ R → (a : ZMod p) ∈ S p)
    (hpos : ∀ p, p.Prime → p ≤ R → 0 < supportRatio S p)
    (T : Finset ℕ) (hcontain : retainedProducts p n K ⊆ T)
    (hT : ∀ t ∈ T, Squarefree t ∧ t ≤ R) {B : ℝ} (hB : 0 < B)
    (hcop : ∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ)/p ≤ 1/16)
    (hmean : ∑ p ∈ CompletionCounting.primesUpTo R, |Real.log (supportRatio S p)|/p ≤ B/16) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (residueCenteredVector p S) n)‖^2 ≤
      1536 * (R : ℝ)/(A.card : ℝ)*Real.exp B :=
  (norm_residue_lowModes_sq_le_sum A p S n K hp hinj T hcontain).trans
    (centered_energy_sum_le A hAn S R hR hA hS hpos T hT hB hcop hmean)

end Ostmann.Supply.TensorModes

end

end OAI
