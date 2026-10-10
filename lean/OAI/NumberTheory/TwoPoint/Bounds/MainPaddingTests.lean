import OAI.NumberTheory.TwoPoint.Bounds.PaddingWitnessProbability

namespace OAI

/-! The actual main-word padding tests imply all tests retained after tuple centering. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def MainPaddingTests {ι : Type*} (p : ι → ℕ) (h B : ℕ)
    (main : List SignedStep) (x : ι → Fin B) : Prop :=
  ∀ (k : Fin main.length) (i : ι), p i ∈ (main.get k).padding.primeFactors →
    ((x i).val : ZMod (p i)) = -((wordDisplacement h (main.take k.val) : ℤ) : ZMod (p i))

theorem mainPaddingTests_retained {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep) (x : ι → Fin B)
    (hpad : ∀ t ∈ main, t.padding ≠ 0) (htuple : ∀ t ∈ main, t.tuple ≠ 0)
    (hcover : ∀ (k : Fin main.length) i, p i ∈ (main.get k).tuple.primeFactors → i ∈ S)
    (hx : MainPaddingTests p h B main x) : RetainedMainTests p S h B main x := by
  intro i hi k hk
  rw [Nat.primeFactors_mul (hpad _ (List.get_mem main k))
    (htuple _ (List.get_mem main k)), mem_union] at hk
  rcases hk with hk | hk
  · exact hx k i hk
  · exact (hi (hcover k i hk)).elim

theorem mainPaddingTests_congr {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (hsep : ∀ (k : Fin main.length) i, p i ∈ (main.get k).padding.primeFactors → i ∉ S)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    MainPaddingTests p h B main x ↔ MainPaddingTests p h B main y := by
  constructor
  · intro hx k i hi
    rw [← hxy i (hsep k i hi)]
    exact hx k i hi
  · intro hy k i hi
    rw [hxy i (hsep k i hi)]
    exact hy k i hi

noncomputable def paddingWeightedFunction {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ) (x : ι → Fin B) : ℝ :=
  if MainPaddingTests p h B main x then R x else 0

lemma paddingWeightedFunction_nonneg {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ)
    (hR : ∀ x, 0 ≤ R x) (x : ι → Fin B) :
    0 ≤ paddingWeightedFunction p h B main R x := by
  unfold paddingWeightedFunction
  split_ifs
  · exact hR x
  · exact le_rfl

lemma paddingWeightedFunction_le {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hR : ∀ x, R x ≤ C) (x : ι → Fin B) :
    paddingWeightedFunction p h B main R x ≤ C := by
  unfold paddingWeightedFunction
  split_ifs
  · exact hR x
  · exact hC

theorem paddingWeightedFunction_retained {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (R : (ι → Fin B) → ℝ) (x : ι → Fin B)
    (hpad : ∀ t ∈ main, t.padding ≠ 0) (htuple : ∀ t ∈ main, t.tuple ≠ 0)
    (hcover : ∀ (k : Fin main.length) i, p i ∈ (main.get k).tuple.primeFactors → i ∈ S)
    (hx : paddingWeightedFunction p h B main R x ≠ 0) :
    RetainedMainTests p S h B main x := by
  apply mainPaddingTests_retained p S h B main x hpad htuple hcover
  by_contra hn
  exact hx (ite_eq_right hn)

theorem paddingWeightedFunction_invariant {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (R : (ι → Fin B) → ℝ)
    (hsep : ∀ (k : Fin main.length) i, p i ∈ (main.get k).padding.primeFactors → i ∉ S)
    (hR : ∀ x y, (∀ i, i ∉ S → x i = y i) → R x = R y)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    paddingWeightedFunction p h B main R x = paddingWeightedFunction p h B main R y := by
  unfold paddingWeightedFunction
  rw [mainPaddingTests_congr p S h B main hsep x y hxy, hR x y hxy]

end TwoPointCorrelations

end OAI
