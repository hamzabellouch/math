import Mathlib
import OAI.Analysis.LaughlinGap.FourHighest
import OAI.Analysis.LaughlinGap.ThreeBounds

namespace OAI

/-! Four Allowance. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

abbrev FourCoordinates (Q : ℕ) := Fin (2*Q-2+1) × Occupation.PairLabel (Q+1)

noncomputable instance (D : ℕ) : DecidableEq (OrbitalTriple D) := Classical.decEq _

def orbitalTripleFinite {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q)
    (b : OrbitalTriple D) : FourCoordinates Q :=
  (⟨b.val.1,by have := b.property; omega⟩,
    ⟨(⟨b.val.2.1,by have := b.property; omega⟩,
      ⟨b.val.2.2,by have := b.property; omega⟩),b.property.2⟩)

lemma orbitalTripleFinite_injective {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    Function.Injective (orbitalTripleFinite hQ hD) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : FourCoordinates Q => x.1.val) he
  · apply Prod.ext
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.1.val) he
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.2.val) he

lemma sum_orbitalTriple {Q D : ℕ} {M : Type*} [AddCommMonoid M]
    (hQ : 2 ≤ Q) (hD : D ≤ Q) (f : FourCoordinates Q → M)
    (hf : ∀ a, a.1.val+a.2.val.1.val+a.2.val.2.val ≠ D → f a = 0) :
    ∑ b : OrbitalTriple D, f (orbitalTripleFinite hQ hD b) = ∑ a, f a := by
  classical
  apply Finset.sum_bij_ne_zero (fun b _ _ => orbitalTripleFinite hQ hD b)
  · simp
  · intros a _ _ b _ _ he
    exact orbitalTripleFinite_injective hQ hD he
  · intro a ha hfa
    have hw : a.1.val+a.2.val.1.val+a.2.val.2.val=D := by
      by_contra hn; exact hfa (hf a hn)
    let b : OrbitalTriple D := ⟨(a.1.val,a.2.val.1.val,a.2.val.2.val), hw,a.2.property⟩
    have hb : orbitalTripleFinite hQ hD b = a := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; rfl
    exact ⟨b,Finset.mem_univ _,by rwa [hb],hb⟩
  · simp

noncomputable def fourHighestRows (Q D : ℕ) : Matrix (FourCopy D) (OrbitalTriple D) ℝ :=
  fun r b => fourBodyCoefficient Q D D r.val.val b.val.1 b.val.2.1 b.val.2.2

lemma fourHighestRows_orthonormal {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    fourHighestRows Q D * (fourHighestRows Q D).transpose = 1 := by
  classical
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  let f := fun a : FourCoordinates Q => fourBodyCoupled Q D D r.val.val a *
    fourBodyCoupled Q D D s.val.val a
  have he (b : OrbitalTriple D) : f (orbitalTripleFinite hQ hD b) =
      fourHighestRows Q D r b * fourHighestRows Q D s b := by
    simp only [f, fourBodyCoupled_coefficient (Nat.le_of_lt_succ r.val.isLt) le_rfl hD,
      fourBodyCoupled_coefficient (Nat.le_of_lt_succ s.val.isLt) le_rfl hD]
    rfl
  rw [← show (∑ b, f (orbitalTripleFinite hQ hD b)) =
    ∑ b, fourHighestRows Q D r b * fourHighestRows Q D s b by simp only [he],
    sum_orbitalTriple hQ hD f]
  · have ho := (orthonormal_iff_ite.mp (fourBodyHighestFamily_orthonormal hQ hD)) s r
    simpa only [fourBodyHighestFamily, EuclideanSpace.inner_toLp_toLp, star_trivial,
      dotProduct, eq_comm] using ho
  · intro a ha
    dsimp [f]
    rw [fourBodyCoupled_coefficient (Nat.le_of_lt_succ r.val.isLt) le_rfl hD]
    simp [fourBodyCoefficient,ha]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

noncomputable def localFourCoordinates {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q)
    (b : OrbitalTriple D) : FockMatrix (Q+1) :=
  let a := orbitalTripleFinite hQ hD b
  annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val

lemma fourAnnihilator_high_local {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) (r : FourCopy D) :
    fourAnnihilator Q D D r.val.val =
      combination (localFourCoordinates hQ hD) (fourHighestRows Q D r) := by
  classical
  rw [fourAnnihilator_exterior hQ hD le_rfl (Nat.le_of_lt_succ r.val.isLt) r.property]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
  let f := fun a : FourCoordinates Q =>
    fourBodyCoefficient Q D D r.val.val a.1.val a.2.val.1.val a.2.val.2.val •
      (annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val)
  change _ = ∑ b, f (orbitalTripleFinite hQ hD b)
  rw [sum_orbitalTriple hQ hD f]
  · exact (Fintype.sum_prod_type f).symm
  · intro a ha
    simp [f, fourBodyCoefficient, ha]

lemma fourHighest_bessel {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    (∑ r : FourCopy D, (fourAnnihilator Q D D r.val.val).transpose *
      fourAnnihilator Q D D r.val.val) ≤
        ∑ b : OrbitalTriple D, (physicalPair Q b.val.1).transpose * physicalPair Q b.val.1 := by
  simp only [fourAnnihilator_high_local hQ hD]
  apply (sub_nonneg.mp (combination_bessel (fourHighestRows Q D)
    (fourHighestRows_orthonormal hQ hD) (localFourCoordinates hQ hD)).nonneg).trans
  apply Finset.sum_le_sum
  intro b hb
  simpa only [localFourCoordinates, orbitalTripleFinite, Matrix.mul_assoc] using
    sub_nonneg.mp (double_annihilation_square_le
      (orbitalTripleFinite hQ hD b).2.val.1 (orbitalTripleFinite hQ hD b).2.val.2
        (physicalPair Q b.val.1)).nonneg

theorem fourHighest_average_bessel {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    ((2*Q-1 : ℕ):ℝ) •
      (∑ r : FourCopy D, average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q D D r.val.val).transpose * fourAnnihilator Q D D r.val.val)) ≤
    (Fintype.card (OrbitalTriple D):ℝ) • physicalHamiltonian Q := by
  have h := average_mono (rotationCommutant (fockLowering Q)) (fourHighest_bessel hQ hD)
  simp only [map_sum] at h
  have he (b : OrbitalTriple D) := physicalPair_single_val hQ
    (show b.val.1 < 2*Q-1 by have := b.property; omega)
  simp only [he, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have h' := smul_le_smul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) (2*Q-1))
  have hn : ((2*Q-1 : ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  convert h' using 1
  rw [smul_smul]
  congr 1
  field_simp

end LaughlinGap.RealOccupation

end

end OAI
