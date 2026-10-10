import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetSieve

namespace OAI

/-! # A missing-residue lower bound for the actual reduced prime energy -/

namespace Ostmann

open scoped Classical BigOperators

 theorem unitFrequencyEnergy_int_congr {q r : ℕ} [NeZero q] [NeZero r]
    (h : q = r) {ι : Type*} (A : Finset ι) (a : ι → ℤ) :
    unitFrequencyEnergy A (fun x => (a x : ZMod q)) =
      unitFrequencyEnergy A (fun x => (a x : ZMod r)) := by
  subst r
  rfl

 theorem prime_support_energy_lower {ι : Type*} (p : ℕ) [Fact p.Prime]
    (A : Finset ι) (hA : A.Nonempty) (a : ι → ℤ)
    (S : Finset (ZMod p)) (hS : S.Nonempty)
    (ha : ∀ x ∈ A, (a x : ZMod p) ∈ S) :
    (p : ℝ) / S.card - 1 ≤ unitFrequencyEnergy A (fun x => (a x : ZMod p)) := by
  let ps : Fin 1 → ℕ := fun _ => p
  let ss : ∀ i, Finset (ZMod (ps i)) := fun _ => S
  let R : Finset (Fin 1) := {0}
  have hc : Pairwise (fun i j => (ps i).Coprime (ps j)) := by
    intro i j hij
    have he : i = j := Subsingleton.elim i j
    exact (hij he).elim
  have hprod : ∏ i ∈ R, ps i = p := by simp [R, ps]
  let : NeZero (∏ i ∈ R, ps i) := ⟨by rw [hprod]; exact (Fact.out : p.Prime).ne_zero⟩
  have hpa : ∀ x ∈ A, ∀ i ∈ R, (a x : ZMod (ps i)) ∈ ss i := by
    intro x hx i _
    exact ha x hx
  have he := subset_reduced_energy_expansion ps ss R hc A a hpa
  have hnonneg (T : Finset (Fin 1)) (hT : T ∈ R.powerset) :
      0 ≤ subsetSieveCoefficient ps ss R T *
        centeredSubsetEnergy ps ss T A (fun x i => (a x : ZMod (ps i))) := by
    apply mul_nonneg
    · exact subsetSieveCoefficient_nonneg ps ss R T (fun _ _ => hS)
    · exact centeredSubsetEnergy_nonneg ps ss T A _
  have hle := Finset.single_le_sum hnonneg (show ∅ ∈ R.powerset by simp)
  rw [centeredSubsetEnergy_empty ps ss A hA, mul_one] at hle
  have hcoeff : subsetSieveCoefficient ps ss R ∅ = (p : ℝ) / S.card - 1 := by
    simp [subsetSieveCoefficient, R, ps, ss]
  rw [hcoeff, ← he] at hle
  rw [unitFrequencyEnergy_int_congr hprod A a] at hle
  exact hle

end Ostmann

end OAI
