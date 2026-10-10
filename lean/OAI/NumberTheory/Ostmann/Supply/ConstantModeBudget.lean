import OAI.NumberTheory.Ostmann.Supply.RestrictedSubsetEnergy

namespace OAI

/-! # The constant mode bounds the size of a sieved interval subset -/
namespace Ostmann
open scoped Classical BigOperators

 theorem lowMode_tensor_energy_one_le {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*} (A : Finset ι) (hA : A.Nonempty)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    1 ≤ countingVectorNorm (lowModeVector K
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 := by
  rw [lowMode_tensor_energy]
  have he : (if (∅ : Finset (Fin n)).card ≤ K then centeredSubsetEnergy p S ∅ A a else 0) = 1 := by
    simp [centeredSubsetEnergy_empty p S A hA a]
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun T : Finset (Fin n) => if T.card ≤ K then centeredSubsetEnergy p S T A a else 0)
    (by intro T _; split_ifs; exact centeredSubsetEnergy_nonneg p S T A a; exact le_rfl)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  simpa only [he] using hh

 theorem constant_mode_card_bound (α E m v : ℝ) (hα : 0 ≤ α) (hm : 0 < m)
    (hv : 1 ≤ v) (hbudget : α * v ≤ E / m) : α * m ≤ E := by
  have h := (mul_le_mul_of_nonneg_left hv hα).trans hbudget
  rw [mul_one] at h
  exact (le_div_iff₀ hm).mp h

end Ostmann

end OAI
