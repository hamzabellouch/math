import Mathlib.Tactic
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A]

noncomputable def cutEuler (I : Ideal A) (x : A) : ℤ :=
  ((Module.length A (A ⧸ (I ⊔ Ideal.span {x}))).toNat : ℤ) -
    (Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x}))).toNat

private theorem finite_cross_add_to_integer
    (a b c d e f : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (he : e ≠ ⊤) (hf : f ≠ ⊤)
    (h : a + b + c = d + e + f) :
    (a.toNat : ℤ) - d.toNat =
      ((e.toNat : ℤ) - b.toNat) + ((f.toNat : ℤ) - c.toNat) := by
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  lift d to ℕ using hd
  lift e to ℕ using he
  lift f to ℕ using hf
  have hn : a + b + c = d + e + f := by exact_mod_cast h
  simp only [ENat.toNat_natCast]
  omega

theorem cutEuler_cyclic_step (I : Ideal A) (f x : A)
    (hcut : ∀ J : Ideal A, Module.length A (A ⧸ (J ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ J : Ideal A,
      Module.length A ((J.colon {x}) ⧸ J.submoduleOf (J.colon {x})) ≠ ⊤) :
    cutEuler I x = cutEuler (I.colon {f}) x + cutEuler (I ⊔ Ideal.span {f}) x := by
  exact finite_cross_add_to_integer _ _ _ _ _ _
    (hcut I) (hker (I.colon {f})) (hker (I ⊔ Ideal.span {f}))
    (hker I) (hcut (I.colon {f})) (hcut (I ⊔ Ideal.span {f}))
    (cyclic_ideal_step_cross_add I f x)

@[simp] theorem cutEuler_top (x : A) : cutEuler (⊤ : Ideal A) x = 0 := by
  simp [cutEuler, Module.length_eq_zero]

theorem cutEuler_filtration (J : ℕ → Ideal A) (f : ℕ → A) (x : A) (n : ℕ)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    cutEuler (J 0) x = (∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x) +
      cutEuler (J n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)),
      cutEuler_cyclic_step (J n) (f n) x hcut hker,
      ← hstep n (Nat.lt_succ_self n), Finset.sum_range_succ, add_assoc]

theorem exists_prime_factor_euler_sum [IsNoetherianRing A] (x : A)
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      cutEuler (⊥ : Ideal A) x = ∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x := by
  obtain ⟨n, J, f, hm, h0, hn, hs⟩ := exists_cyclic_prime_filtration_nat (A := A)
  refine ⟨n, J, f, hm, h0, hn, hs, ?_⟩
  simpa only [h0, hn, cutEuler_top, add_zero] using
    cutEuler_filtration J f x n (fun i hi => (hs i hi).2) hcut hker

end PiExponentJets.W28.LocalIntersection

end OAI
