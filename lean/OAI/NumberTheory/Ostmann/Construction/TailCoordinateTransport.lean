import OAI.NumberTheory.Ostmann.Supply.TailSieveEnergy

namespace OAI

/-! # Equality transport for dependent prime-coordinate energies -/
namespace Ostmann
open scoped Classical

theorem tail_low_energy_congr {n : ℕ} (p q : Fin n → ℕ)
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)] (hpq : p = q)
    (A : Set ℕ) (N K : ℕ) (E : Finset ℤ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates p (fun i => tailDensityMask A N (p i))
        (fun i => (x : ZMod (p i)))))) ^ 2 =
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates q (fun i => tailDensityMask A N (q i))
        (fun i => (x : ZMod (q i)))))) ^ 2 := by
  cases hpq
  rfl

theorem tail_complement_low_energy_congr {n : ℕ} (p q : Fin n → ℕ)
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)] (hpq : p = q)
    (A : Set ℕ) (N K : ℕ) (E : Finset ℤ) :
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates p (fun i => Finset.univ \ tailDensityMask A N (p i))
        (fun i => (x : ZMod (p i)))))) ^ 2 =
    countingVectorNorm (lowModeVector K (averagedCoordinates E
      (fun x => tensorPointCoordinates q (fun i => Finset.univ \ tailDensityMask A N (q i))
        (fun i => (x : ZMod (q i)))))) ^ 2 := by
  cases hpq
  rfl

end Ostmann

end OAI
