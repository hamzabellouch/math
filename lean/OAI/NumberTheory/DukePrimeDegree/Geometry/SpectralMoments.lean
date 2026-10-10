import Mathlib.LinearAlgebra.Vandermonde
import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteOrderSpectrum

namespace OAI

/-!
# Power traces determine finite Euler products

Finite spectra are determined by all their power sums. This is the
linear-algebra step that turns the cyclic character identities into
identities of local Artin Euler factors.
-/

noncomputable section
open Module
open scoped BigOperators Classical

namespace DukePrimeDegree

theorem finite_weights_eq_zero_of_moments
    {I : Type*} [Fintype I] (lam a : I → ℂ) (hlam : Function.Injective lam)
    (h : ∀ k : ℕ, (∑ i, a i * lam i ^ k) = 0) : a = 0 := by
  let e := Fintype.equivFin I
  have he : Function.Injective (fun i => lam (e.symm i)) := hlam.comp e.symm.injective
  have hm : ∀ k : Fin (Fintype.card I),
      (∑ i : Fin (Fintype.card I), a (e.symm i) * lam (e.symm i) ^ (k : ℕ)) = 0 := by
    intro k
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans (h k)
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero he hm
  funext i
  simpa using congrFun hz (e i)

theorem weighted_euler_products_eq_of_moments
    {I : Type*} [Fintype I] (lam : I → ℂ) (p q : I → ℕ)
    (h : ∀ k : ℕ, (∑ i, (p i : ℂ) * lam i ^ k) =
      ∑ i, (q i : ℂ) * lam i ^ k) (z : ℂ) :
    (∏ i, (1 - z * lam i) ^ p i) = ∏ i, (1 - z * lam i) ^ q i := by
  let J := Set.range lam
  let : Fintype J := (Set.finite_range lam).fintype
  let r : I → J := fun i => ⟨lam i, ⟨i, rfl⟩⟩
  let weight (t : I → ℕ) (j : J) := ∑ i ∈ Finset.univ.filter (fun i => r i = j), t i
  have regroup (t : I → ℕ) (k : ℕ) :
      (∑ j : J, (weight t j : ℂ) * j.val ^ k) = ∑ i, (t i : ℂ) * lam i ^ k := by
    calc
      _ = ∑ j : J, ∑ i ∈ Finset.univ.filter (fun i => r i = j),
          (t i : ℂ) * lam i ^ k := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [weight, Nat.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have hij : lam i = j.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
        rw [hij]
      _ = _ := Finset.sum_fiberwise Finset.univ r _
  have hw : (fun j : J => (weight p j : ℂ) - (weight q j : ℂ)) = 0 := by
    apply finite_weights_eq_zero_of_moments Subtype.val _ Subtype.val_injective
    intro k
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [regroup, regroup, h, sub_self]
  have hweight (j : J) : weight p j = weight q j := by
    have he := congrFun hw j
    simp only [Pi.zero_apply, sub_eq_zero] at he
    exact_mod_cast he
  have prod_regroup (t : I → ℕ) :
      (∏ i, (1 - z * lam i) ^ t i) =
        ∏ j : J, (1 - z * j.val) ^ weight t j := by
    calc
      _ = ∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => r i = j),
          (1 - z * lam i) ^ t i :=
        (Finset.prod_fiberwise Finset.univ r _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        dsimp only [weight]
        rw [← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro i hi
        have hij : lam i = j.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
        rw [hij]
  rw [prod_regroup, prod_regroup]
  simp only [hweight]

/-- Equality of finite-group characters gives the corresponding local
Euler-factor identity. The natural exponents permit denominator-cleared
integer character relations. -/
theorem euler_det_products_eq_of_characters
    {I G : Type*} [Fintype I] [Group G] [Finite G]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (p q : I → ℕ)
    (h : ∀ g, (∑ i, (p i : ℂ) * (ρ i).character g) =
      ∑ i, (q i : ℂ) * (ρ i).character g)
    (g : G) (z : ℂ) :
    (∏ i, (LinearMap.id - z • ρ i g).det ^ p i) =
      ∏ i, (LinearMap.id - z • ρ i g).det ^ q i := by
  have hb (i : I) : ∃ (n : ℕ) (b : Basis (Fin n) ℂ (V i)) (lam : Fin n → ℂ),
      ∀ j, ρ i g (b j) = lam j • b j := by
    apply exists_eigenbasis_of_finite_order (ρ i g) (Nat.card_pos (α := G))
    rw [← map_pow, pow_card_eq_one', map_one]
  choose n b lam hb using hb
  let μ : (i : I) × Fin (n i) → ℂ := fun j => lam j.1 j.2
  have hm : ∀ k : ℕ,
      (∑ j : (i : I) × Fin (n i), (p j.1 : ℂ) * μ j ^ k) =
        ∑ j : (i : I) × Fin (n i), (q j.1 : ℂ) * μ j ^ k := by
    intro k
    have he (i : I) : (ρ i).character (g ^ k) = ∑ j, lam i j ^ k := by
      rw [Representation.character, map_pow]
      exact trace_pow_eq_sum_of_eigenbasis (b i) (ρ i g) (lam i) (hb i) k
    simpa only [Fintype.sum_sigma, μ, ← Finset.mul_sum, he] using h (g ^ k)
  have H := weighted_euler_products_eq_of_moments μ
    (fun j => p j.1) (fun j => q j.1) hm z
  simp only [Fintype.prod_sigma, μ, Finset.prod_pow] at H
  simpa only [← euler_det_eq_prod_of_eigenbasis (b _) (ρ _ g) (lam _) (hb _) z] using H

end DukePrimeDegree

end

end OAI
