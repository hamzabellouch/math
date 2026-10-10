import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellsBounded
import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def boundedPrimeSet (Q : ℕ) (S : Finset ℕ) : Finset (PrimeUpTo Q) :=
  Finset.univ.filter (fun p=>p.val∈S)

@[simp] lemma mem_boundedPrimeSet {Q : ℕ} {S : Finset ℕ} {p : PrimeUpTo Q} :
    p∈boundedPrimeSet Q S ↔ p.val∈S := by simp [boundedPrimeSet]

lemma naturalPrimeSet_boundedPrimeSet (Q : ℕ) (S : Finset ℕ) (hS : S⊆Q.primesLE) :
    naturalPrimeSet (boundedPrimeSet Q S)=S := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact mem_boundedPrimeSet.mp hq
  · intro hp
    exact Finset.mem_image.mpr ⟨⟨p,hS hp⟩,mem_boundedPrimeSet.mpr hp,rfl⟩

lemma boundedPrimeSet_naturalPrimeSet {Q : ℕ} (E : Finset (PrimeUpTo Q)) :
    boundedPrimeSet Q (naturalPrimeSet E)=E := by
  ext p
  rw [mem_boundedPrimeSet]
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hp
    have hh : q=p := Subtype.ext he
    simpa only [hh] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩

lemma boundedPrimeSet_mass (Q : ℕ) (S : Finset ℕ) (hS : S⊆Q.primesLE) :
    primeShellMass (boundedPrimeSet Q S)=harmonicPrimeMass S := by
  rw [← naturalPrimeSet_mass,naturalPrimeSet_boundedPrimeSet Q S hS]

lemma sum_boundedPrimeSet (Q : ℕ) (S : Finset ℕ) (hS : S⊆Q.primesLE)
    {A : Type*} [AddCommMonoid A] (f : ℕ→A) :
    (∑p∈boundedPrimeSet Q S,f p.val)=∑p∈S,f p := by
  rw [← sum_naturalPrimeSet,naturalPrimeSet_boundedPrimeSet Q S hS]

def boundedInterval {Q : ℕ} (E : Finset (PrimeUpTo Q)) (a b : ℝ) : Finset (PrimeUpTo Q) :=
  E.filter (fun p=>a < Real.log (Real.log p.val) ∧ Real.log (Real.log p.val)≤b)

lemma boundedInterval_subset {Q : ℕ} (E : Finset (PrimeUpTo Q)) (a b : ℝ) :
    boundedInterval E a b⊆E := Finset.filter_subset _ _

lemma naturalPrimeSet_boundedInterval {Q : ℕ} (E : Finset (PrimeUpTo Q)) (a b : ℝ) :
    naturalPrimeSet (boundedInterval E a b)=
      (naturalPrimeSet E).filter (fun p : ℕ=>a < Real.log (Real.log p) ∧ Real.log (Real.log p)≤b) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq,hl,hu⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,hl,hu⟩
  · intro hp
    obtain ⟨hp,hl,hu⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hl,hu⟩,rfl⟩

lemma boundedInterval_mass {Q : ℕ} (E : Finset (PrimeUpTo Q)) (a b : ℝ) :
    primeShellMass (boundedInterval E a b)=harmonicIntervalMass (naturalPrimeSet E) a b := by
  rw [← naturalPrimeSet_mass,naturalPrimeSet_boundedInterval]
  rfl

lemma boundedInterval_log_bounds {Q : ℕ} (E : Finset (PrimeUpTo Q)) (a b : ℝ)
    (p : PrimeUpTo Q) (hp : p∈boundedInterval E a b) :
    Real.exp a < Real.log p.val ∧ Real.log p.val≤Real.exp b := by
  obtain ⟨_,hl,hu⟩ := Finset.mem_filter.mp hp
  have hlog : 0 < Real.log p.val := Real.log_pos (by exact_mod_cast (primeUpTo_prime p).one_lt)
  have hle := Real.exp_le_exp.mpr hu
  have hlt := Real.exp_lt_exp.mpr hl
  rw [Real.exp_log hlog] at hle hlt
  exact ⟨hlt,hle⟩

lemma boundedPrimeSet_subset {Q : ℕ} {S T : Finset ℕ} (h : S⊆T) :
    boundedPrimeSet Q S⊆boundedPrimeSet Q T := fun _ hp=>mem_boundedPrimeSet.mpr (h (mem_boundedPrimeSet.mp hp))

lemma naturalPrimeSet_boundedInterval_of_cutoff (Q : ℕ) (E : Finset ℕ) (a b : ℝ)
    (hprime : ∀p∈E,p.Prime)
    (hcut : ∀p∈E,a < Real.log (Real.log p) → Real.log (Real.log p)≤b → p≤Q) :
    naturalPrimeSet (boundedInterval (boundedPrimeSet Q E) a b)=
      E.filter (fun p : ℕ=>a < Real.log (Real.log p) ∧ Real.log (Real.log p)≤b) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq,hl,hu⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨mem_boundedPrimeSet.mp hq,hl,hu⟩
  · intro hp
    obtain ⟨hp,hl,hu⟩ := Finset.mem_filter.mp hp
    let q : PrimeUpTo Q := ⟨p,Nat.mem_primesLE.mpr ⟨hcut p hp hl hu,hprime p hp⟩⟩
    exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr
      ⟨mem_boundedPrimeSet.mpr hp,hl,hu⟩,rfl⟩

lemma boundedInterval_mass_of_cutoff (Q : ℕ) (E : Finset ℕ) (a b : ℝ)
    (hprime : ∀p∈E,p.Prime)
    (hcut : ∀p∈E,a < Real.log (Real.log p) → Real.log (Real.log p)≤b → p≤Q) :
    primeShellMass (boundedInterval (boundedPrimeSet Q E) a b)=harmonicIntervalMass E a b := by
  rw [← naturalPrimeSet_mass,naturalPrimeSet_boundedInterval_of_cutoff Q E a b hprime hcut]
  rfl

end Ostmann.Characters.HigherBiasSource

end

end OAI
