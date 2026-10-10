import OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialMean
import Mathlib.Data.Finset.SymmDiff

namespace OAI

/-! Algebra of the low-degree functions used in the circuit approximation.
Multiplication adds degrees, including after Boolean multilinearization. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical symmDiff

variable {n : ℕ}

lemma walsh_mul (S T : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh T x = walsh (S ∆ T) x := by
  have hd : Disjoint (S ∆ T) (S ∩ T) := by
    rw [disjoint_left]
    intro i hi hi'
    simp only [mem_symmDiff, mem_inter] at hi hi'
    tauto
  have hu : (S ∆ T) ∪ (S ∩ T) = S ∪ T := by
    ext i
    simp only [mem_union, mem_symmDiff, mem_inter]
    tauto
  have he : walsh (S ∪ T) x * walsh (S ∩ T) x = walsh S x * walsh T x :=
    prod_union_inter
  have hh : walsh (S ∪ T) x = walsh (S ∆ T) x * walsh (S ∩ T) x := by
    simpa only [walsh, hu] using
      (prod_union hd : (∏ i ∈ (S ∆ T) ∪ (S ∩ T), booleanSign (x i)) = _)
  rw [hh, mul_assoc, walsh_mul_self, mul_one] at he
  exact he.symm

lemma WalshDegreeLE.of_walsh (S : Finset (Fin n)) {t : ℕ} (hS : S.card ≤ t) :
    WalshDegreeLE (walsh S) t := by
  refine ⟨fun T => if T = S then 1 else 0, ?_⟩
  intro x
  simp [hS]

lemma WalshDegreeLE.const (c : ℝ) (t : ℕ) :
    WalshDegreeLE (fun _ : BooleanCube n => c) t := by
  refine ⟨fun S => if S = ∅ then c else 0, ?_⟩
  intro x
  simp

lemma WalshDegreeLE.smul {F : BooleanCube n → ℝ} {t : ℕ}
    (hF : WalshDegreeLE F t) (c : ℝ) : WalshDegreeLE (fun x => c * F x) t := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun S => c * a S, ?_⟩
  intro x
  dsimp only
  rw [ha, mul_sum]
  apply sum_congr rfl
  intro S _
  ring

lemma WalshDegreeLE.sub {F G : BooleanCube n → ℝ} {t : ℕ}
    (hF : WalshDegreeLE F t) (hG : WalshDegreeLE G t) :
    WalshDegreeLE (fun x => F x - G x) t := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  refine ⟨fun S => a S - b S, ?_⟩
  intro x
  dsimp only
  rw [ha, hb, ← sum_sub_distrib]
  apply sum_congr rfl
  intro S _
  ring

lemma WalshDegreeLE.sum {ι : Type*} (I : Finset ι) (F : ι → BooleanCube n → ℝ)
    {t : ℕ} (hF : ∀ i ∈ I, WalshDegreeLE (F i) t) :
    WalshDegreeLE (fun x => ∑ i ∈ I, F i x) t := by
  choose a ha using fun i : I => hF i i.property
  refine ⟨fun S => ∑ i : I, a i S, ?_⟩
  intro x
  dsimp only
  rw [← sum_coe_sort I]
  simp_rw [ha]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  exact (sum_mul _ _ _).symm

lemma WalshDegreeLE.mul {F G : BooleanCube n → ℝ} {p q : ℕ}
    (hF : WalshDegreeLE F p) (hG : WalshDegreeLE G q) :
    WalshDegreeLE (fun x => F x * G x) (p + q) := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  let A := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ p)
  let B := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ q)
  have heq : (fun x => F x * G x) = fun x =>
      ∑ S ∈ A, ∑ T ∈ B, (a S * b T) * walsh (S ∆ T) x := by
    funext x
    rw [ha, hb, sum_mul]
    apply sum_congr rfl
    intro S _
    rw [mul_sum]
    apply sum_congr rfl
    intro T _
    rw [← walsh_mul]
    ring
  rw [heq]
  apply WalshDegreeLE.sum A
  intro S hS
  apply WalshDegreeLE.sum B
  intro T hT
  apply WalshDegreeLE.smul
  apply WalshDegreeLE.of_walsh
  calc
    (S ∆ T).card ≤ (S ∪ T).card := card_le_card symmDiff_subset_union
    _ ≤ S.card + T.card := card_union_le S T
    _ ≤ p + q := add_le_add (mem_filter.mp hS).2 (mem_filter.mp hT).2

end TwoPointCorrelations

end OAI
