import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourcePrimeSets

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Preliminaries Construction
attribute [local instance] Classical.propDecidable

def testShellEligible {Q : ℕ} (E : Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (j : ℕ) : Prop :=
  c0 ≤ primeShellMass (boundedInterval E (U+j) (U+j+1)) ∧
    Real.exp (U+j+1) ≤ logX/4

def testedShellFamily {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ)
    (i : Fin (5*k+3)) : Finset (PrimeUpTo Q) :=
  if hi : i.val < 3 then base ⟨i.val,hi⟩
  else if testShellEligible E c0 U logX (i.val-3) then
    boundedInterval E (U+(i.val-3:ℕ)) (U+(i.val-3:ℕ)+1)
  else base 2

def firstTestIndex (k : ℕ) (i : Fin 3) : Fin (5*k+3) := ⟨i.val,by omega⟩
def gridTestIndex (k : ℕ) (j : Fin (5*k)) : Fin (5*k+3) := ⟨j.val+3,by omega⟩

@[simp] theorem testedShellFamily_first {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ) (i : Fin 3) :
    testedShellFamily E base c0 U logX k (firstTestIndex k i)=base i := by
  have hi : (firstTestIndex k i).val<3 := i.isLt
  rw [testedShellFamily,dite_eq_left hi]
  rfl

theorem testedShellFamily_grid {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ) (j : Fin (5*k))
    (hj : testShellEligible E c0 U logX j.val) :
    testedShellFamily E base c0 U logX k (gridTestIndex k j)=
      boundedInterval E (U+j.val) (U+j.val+1) := by
  have hi : ¬(gridTestIndex k j).val<3 := by
    change ¬j.val+3<3
    omega
  rw [testedShellFamily,dite_eq_right hi]
  have he : (gridTestIndex k j).val-3=j.val := Nat.add_sub_cancel j.val 3
  simp only [he,ite_eq_left hj]

theorem testedShellFamily_subset {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ)
    (hbase : ∀ i,base i⊆E) (i : Fin (5*k+3)) :
    testedShellFamily E base c0 U logX k i⊆E := by
  unfold testedShellFamily
  split_ifs
  · exact hbase _
  · exact boundedInterval_subset _ _ _
  · exact hbase _

theorem testedShellFamily_mass {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ)
    (hbase : ∀ i,c0≤primeShellMass (base i)) (i : Fin (5*k+3)) :
    c0≤primeShellMass (testedShellFamily E base c0 U logX k i) := by
  unfold testedShellFamily
  split_ifs with hi he
  · exact hbase _
  · exact he.1
  · exact hbase _

theorem testedShellFamily_log_cutoff {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ)
    (hbase : ∀ i,∀ p∈base i,Real.log p.val≤logX/4)
    (i : Fin (5*k+3)) (p : PrimeUpTo Q)
    (hp : p∈testedShellFamily E base c0 U logX k i) : Real.log p.val≤logX/4 := by
  unfold testedShellFamily at hp
  split_ifs at hp with hi he
  · exact hbase _ p hp
  · exact (boundedInterval_log_bounds _ _ _ p hp).2.trans he.2
  · exact hbase _ p hp

theorem testedShellFamily_grid_of_harmonicMass {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (base : Fin 3 → Finset (PrimeUpTo Q)) (c0 U logX : ℝ) (k : ℕ) (j : Fin (5*k))
    (hm : c0≤harmonicIntervalMass (naturalPrimeSet E) (U+j.val) (U+j.val+1))
    (hcut : Real.exp (U+j.val+1)≤logX/4) :
    testedShellFamily E base c0 U logX k (gridTestIndex k j)=
      boundedInterval E (U+j.val) (U+j.val+1) := by
  apply testedShellFamily_grid
  constructor
  · simpa only [boundedInterval_mass] using hm
  · exact hcut

end Ostmann.Characters.HigherBiasSource

end

end OAI
