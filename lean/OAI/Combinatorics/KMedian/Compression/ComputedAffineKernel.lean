import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineKernel
import OAI.Combinatorics.KMedian.Compression.ComputedIntegerKernel
import OAI.Combinatorics.KMedian.Compression.FinsetVectorExtension

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def activeMatrix {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ) :
    Fin (d+1) → Fin μ.support.card → ℤ :=
  fun j i => Fin.cases 1 (fun j => v ((μ.support.orderIsoOfFin rfl) i).val j) j

def computedAffineKernel {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) : Fin n → ℤ :=
  let zi := Gaussian.computedIntegerKernel (d+1) μ.support.card (activeMatrix μ v)
  let z := Vector.ofFn (Compression.extendVector μ.support zi)
  fun i => z[i.val]

theorem computedAffineKernel_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    let z := computedAffineKernel μ v
    (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) ∧
      (∀ j, ∑ i, (z i:ℚ)*(v i j:ℚ)=0) ∧
      (∀ i, μ.numerator i=0 → z i=0) ∧
      ∀ i, |z i| ≤ (2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) := by
  dsimp only
  let V := activeMatrix μ v
  let zi := Gaussian.computedIntegerKernel (d+1) μ.support.card V
  have hVb : ∀ j i, |V j i| ≤ (2:ℤ)^L := by
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [V,activeMatrix,Fin.cases_zero,abs_one] using
        (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2) : (1:ℤ) ≤ 2^L)
    · simpa only [V,activeMatrix,Fin.cases_succ] using hv ((μ.support.orderIsoOfFin rfl) i).val j
  have hzi := Gaussian.computedIntegerKernel_spec (d+1) μ.support.card L V hsize hVb
  have he : computedAffineKernel μ v=Compression.extendVector μ.support zi := by
    funext i
    simp only [computedAffineKernel,Vector.getElem_ofFn]
    rfl
  rw [he]
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨i,hi⟩ := hzi.1
    exact ⟨((μ.support.orderIsoOfFin rfl) i).val,by rwa [Compression.extendVector_at]⟩
  · have hh := hzi.2.1 0
    simp only [V,activeMatrix,Fin.cases_zero,mul_one] at hh
    simpa only [mul_one] using
      (Compression.extendVector_sum μ.support zi (fun _ => 1)).trans (by simpa only [mul_one] using hh)
  · intro j
    have hh := hzi.2.1 j.succ
    simp only [V,activeMatrix,Fin.cases_succ] at hh
    have ht := (Compression.extendVector_sum μ.support zi (fun i => v i j)).trans hh
    exact_mod_cast ht
  · intro i hi
    apply Compression.extendVector_zero
    simpa only [mem_support,not_not] using hi
  · intro i
    have heN : μ.support.card ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    apply Compression.extendVector_bound _ _ _ (by positivity) _ i
    intro j
    exact (hzi.2.2 j).trans (pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right heN 1)))

end MetricKMedian.IntegerLaw

end OAI
