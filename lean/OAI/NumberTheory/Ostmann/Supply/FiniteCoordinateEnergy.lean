import OAI.NumberTheory.Ostmann.Supply.AveragedKernelPairing
import OAI.NumberTheory.Ostmann.Supply.CenteredRamanujanKernel

namespace OAI

/-! # The energy of averaged finite tensor coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_identity {α : Type*} [Fintype α] (f g : α → ℂ) :
    kernelPairingLinearMap f g (fun x y => if y = x then 1 else 0) =
      ∑ x, conj (f x) * g x := by
  change (∑ x, conj (f x) * ∑ y, (if y = x then 1 else 0) * g y) = _
  simp

theorem averagedCoordinates_inner {ι κ α : Type*} [Fintype α]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → α → ℂ) :
    (∑ x, conj (averagedCoordinates A V x) * averagedCoordinates B W x) =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, ∑ x, conj (V a x) * W b x := by
  have hh := kernelPairing_averages A B V W (fun x y => if y = x then 1 else 0)
  simpa only [kernelPairing_identity] using hh

theorem countingVectorNorm_sq_complex {α : Type*} [Fintype α] (f : α → ℂ) :
    ((countingVectorNorm f ^ 2 : ℝ) : ℂ) = ∑ x, conj (f x) * f x := by
  rw [countingVectorNorm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Complex.ofReal_pow, mul_comm] using (Complex.mul_conj' (f x)).symm

theorem productVector_inner {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f g : ∀ i, α i → ℂ) :
    (∑ x : (∀ i, α i), conj (∏ i, f i (x i)) * ∏ i, g i (x i)) =
      ∏ i, ∑ x, conj (f i x) * g i x := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => conj (f i x) * g i x)).symm

noncomputable def centeredSubsetVector {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n))
    (a : ∀ i, ZMod (p i)) (x : ∀ i : T, ZMod (p i)) : ℂ :=
  ∏ i : T, centeredSupportProjection (S i) (residuePointVector (a i)) (x i)

noncomputable def centeredSubsetEnergy {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) : ℝ :=
  countingVectorNorm (averagedCoordinates A (fun x => centeredSubsetVector p S T (a x))) ^ 2

theorem centeredSubsetEnergy_formula {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    (centeredSubsetEnergy p S T A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∏ i ∈ T, ∑ z, conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
          centeredSupportProjection (S i) (residuePointVector (a y i)) z := by
  rw [centeredSubsetEnergy, countingVectorNorm_sq_complex, averagedCoordinates_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hh := productVector_inner (ι := T) (α := fun i : T => ZMod (p i))
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a x i)) z)
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  unfold centeredSubsetVector
  have hp := Finset.prod_coe_sort T (fun i : Fin n => ∑ z : ZMod (p i),
    conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
      centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  convert hh.trans hp using 1
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    rfl

theorem centeredSubsetEnergy_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    0 ≤ centeredSubsetEnergy p S T A a := sq_nonneg _

theorem centeredSubsetEnergy_empty {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*}
    (A : Finset ι) (hA : A.Nonempty) (a : ι → ∀ i, ZMod (p i)) :
    centeredSubsetEnergy p S ∅ A a = 1 := by
  have hAc : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  rw [centeredSubsetEnergy, countingVectorNorm_sq]
  simp [averagedCoordinates, centeredSubsetVector, hAc]

end Ostmann

end OAI
