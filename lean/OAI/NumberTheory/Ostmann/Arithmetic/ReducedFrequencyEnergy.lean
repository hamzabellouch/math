import OAI.NumberTheory.Ostmann.Characters.UnitRamanujanProduct
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProbability

namespace OAI

/-! # Reduced-frequency energy of a uniform set and its Ramanujan kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def unitFrequencyEnergy {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) : ℝ :=
  ∑ u : (ZMod q)ˣ, ‖(A.card : ℂ)⁻¹ * ∑ x ∈ A,
    ZMod.stdAddChar ((u : ZMod q) * a x)‖ ^ 2

theorem unitFrequencyEnergy_nonneg {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) : 0 ≤ unitFrequencyEnergy A a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem unitFrequencyEnergy_kernel {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) :
    (unitFrequencyEnergy A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ *
        ∑ x ∈ A, ∑ y ∈ A, unitRamanujanKernel q (a x - a y) := by
  have hp (u : (ZMod q)ˣ) :
      ((‖(A.card : ℂ)⁻¹ * ∑ x ∈ A, ZMod.stdAddChar ((u : ZMod q) * a x)‖ ^ 2 : ℝ) : ℂ) =
        (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
          ZMod.stdAddChar ((u : ZMod q) * (a x - a y)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [show (u : ZMod q) * (a x - a y) =
      (u : ZMod q) * a x + -((u : ZMod q) * a y) by ring,
      AddChar.map_add_eq_mul]
    ring
  rw [unitFrequencyEnergy, Complex.ofReal_sum]
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  rfl

theorem sum_reducedNumerators_eq_units {q : ℕ} [NeZero q]
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ h ∈ reducedNumerators q, f h) = ∑ u : (ZMod q)ˣ, f (u : ZMod q).val := by
  change (∑ h ∈ reducedResidues q, f h) = _
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

theorem intervalSetReducedEnergy_eq_unitFrequencyEnergy {M q : ℕ} [NeZero q]
    (A : Finset (Fin M)) (J : ℤ) :
    intervalSetReducedEnergy A J q =
      unitFrequencyEnergy A (fun n => ((J + (n.val : ℤ) : ℤ) : ZMod q)) := by
  unfold intervalSetReducedEnergy unitFrequencyEnergy
  rw [sum_reducedNumerators_eq_units]
  apply Finset.sum_congr rfl
  intro u _
  simp only [intervalSetExponentialSum, sieveAdditivePhase_eq_stdAddChar,
    ZMod.natCast_zmod_val]

end Ostmann

end OAI
