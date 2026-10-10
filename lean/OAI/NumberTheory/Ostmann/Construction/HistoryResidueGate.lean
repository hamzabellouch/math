import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPrecision
import OAI.NumberTheory.Ostmann.Construction.HistoryPolynomialSpecialization

namespace OAI

/-! # Constructing the residue gate for cleared integer history tests -/

namespace Ostmann

open scoped Classical

def smallDivisionTest (N d : ℤ) (s : ℕ) : Prop :=
  d ∣ N ∧ IsUnit ((N / d : ℤ) : ZMod s)

theorem smallDivisionTest_modEq (N N' d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (h : N ≡ N' [ZMOD d * s]) : smallDivisionTest N d s ↔ smallDivisionTest N' d s := by
  have hint : d ∣ N ↔ d ∣ N' := (h.of_dvd (dvd_mul_right d (s : ℤ))).dvd_iff
  have hquot (hN : d ∣ N) (hN' : d ∣ N') :
      (N / d : ℤ) ≡ N' / d [ZMOD s] := by
    apply Int.modEq_iff_dvd.mpr
    apply Int.dvd_of_mul_dvd_mul_left hd
    have he : d * (N' / d - N / d) = N' - N := by
      nlinarith only [Int.ediv_mul_cancel hN, Int.ediv_mul_cancel hN']
    rw [he]
    exact h.dvd
  constructor
  · rintro ⟨hN, hu⟩
    refine ⟨hint.mp hN, ?_⟩
    rwa [← (ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot hN (hint.mp hN))]
  · rintro ⟨hN', hu⟩
    refine ⟨hint.mpr hN', ?_⟩
    rwa [(ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot (hint.mpr hN') hN')]

theorem integerPolynomial_eval_modEq {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℤ) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    MvPolynomial.eval₂ (RingHom.id ℤ) a P ≡ MvPolynomial.eval₂ (RingHom.id ℤ) b P [ZMOD M] := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval₂_C, RingHom.id_apply]; exact .refl _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (h i)

theorem cleared_history_test_residue_invariant {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℕ) (d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (hdiv : d * s ∣ (M : ℤ)) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) a P) d s ↔
      smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) b P) d s :=
  smallDivisionTest_modEq _ _ d s hd ((integerPolynomial_eval_modEq P a b M h).of_dvd hdiv)

noncomputable def clearedHistoryResidueGate {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M] (z : ZMod M) : ℂ :=
  if ∀ j, smallDivisionTest
    (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i (z.val : ℤ)) (P j)) (d j) (s j)
    then 1 else 0

theorem clearedHistoryResidueGate_norm {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M] (z : ZMod M) :
    ‖clearedHistoryResidueGate P d s a i M z‖ ≤ 1 := by
  unfold clearedHistoryResidueGate
  split_ifs <;> norm_num

/-- The original conjunction of integer divisibility and frequency-unit
checks is exactly a bounded function of the surviving prime residue. -/
theorem clearedHistoryResidueGate_exact {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M]
    (hd : ∀ j, d j ≠ 0) (hdiv : ∀ j, d j * s j ∣ (M : ℤ)) (x : ℤ) :
    clearedHistoryResidueGate P d s a i M (x : ZMod M) =
      if ∀ j, smallDivisionTest
        (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (P j)) (d j) (s j)
        then 1 else 0 := by
  have hx : x ≡ ((x : ZMod M).val : ℤ) [ZMOD M] := by
    apply (ZMod.intCast_eq_intCast_iff x (((x : ZMod M).val : ℕ) : ℤ) M).mp
    rw [Int.cast_natCast]
    exact (ZMod.natCast_zmod_val (x : ZMod M)).symm
  have hcoord (k : σ) : Function.update a i x k ≡
      Function.update a i (((x : ZMod M).val : ℤ)) k [ZMOD M] := by
    by_cases hki : k = i
    · subst k; simpa [Function.update] using hx
    · simp [Function.update, hki]
  have ht : (∀ j, smallDivisionTest
      (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (P j)) (d j) (s j)) ↔
      (∀ j, smallDivisionTest
      (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i ((x : ZMod M).val : ℤ)) (P j)) (d j) (s j)) := by
    apply forall_congr'
    intro j
    exact cleared_history_test_residue_invariant (P j) _ _ M (d j) (s j) (hd j) (hdiv j) hcoord
  simp only [clearedHistoryResidueGate, ht]

end Ostmann

end OAI
