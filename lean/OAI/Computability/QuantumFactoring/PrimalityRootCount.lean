import Mathlib
import OAI.Computability.QuantumFactoring.Primality

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The nonnegative exponent orbit. In a finite group this is the manuscript's H;
using its submonoid presentation makes the m^u p^v representatives explicit. -/
def residueOrbit (s m p : ℕ) : Submonoid (ZMod s) :=
  Submonoid.closure {(m : ZMod s), (p : ZMod s)}

lemma residueOrbit_rep {s m p : ℕ} (x : residueOrbit s m p) :
    ∃ u v : ℕ, ((m^u*p^v : ℕ) : ZMod s) = x.val := by
  simpa using (Submonoid.mem_closure_pair (m : ZMod s) (p : ZMod s) x.val).mp x.property

noncomputable def residueRoot {F : Type*} [Field F] {s m p : ℕ}
    (w : F) (x : residueOrbit s m p) : F := w^x.val.val

lemma residueRoot_injective {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) :
    Function.Injective (residueRoot (s := s) (m := m) (p := p) w) := by
  intro x y hxy
  apply Subtype.ext
  apply ZMod.val_injective
  exact hw.pow_inj (ZMod.val_lt x.val) (ZMod.val_lt y.val) hxy

lemma eval_eq_on_orbit {F : Type*} [Field F] {s m p : ℕ} {w : F}
    (hw : w^s = 1) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w) (x : residueOrbit s m p) :
    f.eval (residueRoot w x) = g.eval (residueRoot w x) := by
  obtain ⟨u,v,hrep⟩ := residueOrbit_rep x
  have hf := ((hfm.pow_exp u).mul_exp (hfp.pow_exp v)) w hw
  have hg := ((hgm.pow_exp u).mul_exp (hgp.pow_exp v)) w hw
  have hk : residueRoot w x = w^(m^u*p^v) := by
    unfold residueRoot
    rw [← hrep, ZMod.val_natCast, ← pow_eq_pow_mod _ hw]
  rw [hk, ← hf, ← hg, hfg]

/-- The lower-bound injection is proved by h distinct roots of f-g, not by
assuming any tested product has a nonzero value. -/
lemma eval_injective_low_degree {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) {f g : F[X]}
    (hfm : Introspective s m f) (hfp : Introspective s p f)
    (hgm : Introspective s m g) (hgp : Introspective s p g)
    (hfg : f.eval w = g.eval w)
    (hf : f.natDegree < Nat.card (residueOrbit s m p))
    (hg : g.natDegree < Nat.card (residueOrbit s m p)) : f = g := by
  classical
  let : Fintype (residueOrbit s m p) := Fintype.ofFinite (residueOrbit s m p)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq f g (residueRoot_injective (m := m) (p := p) hw)
  · exact eval_eq_on_orbit hw.pow_eq_one hfm hfp hgm hgp hfg
  · simpa [Nat.card_eq_fintype_card] using max_lt hf hg

noncomputable def subsetPolynomial {F : Type*} [Field F] (S : Finset F) : F[X] :=
  ∏ a ∈ S, (X-C a)

lemma subsetPolynomial_injective {F : Type*} [Field F] :
    Function.Injective (subsetPolynomial (F := F)) := by
  intro S T h
  have hr := congrArg Polynomial.roots h
  simpa [subsetPolynomial, Polynomial.roots_prod_X_sub_C, Finset.val_inj] using hr

lemma subsetPolynomial_degree {F : Type*} [Field F] (S : Finset F) :
    (subsetPolynomial S).natDegree = S.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card S id

lemma subsetPolynomial_introspective {F : Type*} [Field F] {s k : ℕ}
    (S : Finset F) (hf : ∀ a ∈ S, Introspective s k (X-C a)) :
    Introspective s k (subsetPolynomial S) := Introspective.prod S _ hf

/-- The entire lower/upper root count, prior to arithmetic estimates: a collision
of two distinct integer exponents bounds the number of subset products. -/
lemma subset_count_le_collision {F : Type*} [Field F] {s m p : ℕ} [NeZero s]
    {w : F} (hw : IsPrimitiveRoot w s) (S : Finset F) {t k₁ k₂ : ℕ}
    (ht : t < Nat.card (residueOrbit s m p))
    (hm : ∀ a ∈ S, Introspective s m (X-C a))
    (hp : ∀ a ∈ S, Introspective s p (X-C a))
    (hk₁ : ∀ a ∈ S, Introspective s k₁ (X-C a))
    (hk₂ : ∀ a ∈ S, Introspective s k₂ (X-C a))
    (hk : w^k₁ = w^k₂) (hne : k₁ ≠ k₂) :
    S.card.choose t ≤ max k₁ k₂ := by
  classical
  let T := S.powersetCard t
  let values := T.image (fun A => (subsetPolynomial A).eval w)
  have he : Set.InjOn (fun A => (subsetPolynomial A).eval w) T := by
    intro A hA B hB hAB
    obtain ⟨hAS,hAt⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨hBS,hBt⟩ := Finset.mem_powersetCard.mp hB
    apply subsetPolynomial_injective
    exact eval_injective_low_degree hw
      (subsetPolynomial_introspective A (fun a ha => hm a (hAS ha)))
      (subsetPolynomial_introspective A (fun a ha => hp a (hAS ha)))
      (subsetPolynomial_introspective B (fun a ha => hm a (hBS ha)))
      (subsetPolynomial_introspective B (fun a ha => hp a (hBS ha))) hAB
      (by simpa [subsetPolynomial_degree, hAt] using ht)
      (by simpa [subsetPolynomial_degree, hBt] using ht)
  have hv : values.card = S.card.choose t := by
    rw [Finset.card_image_of_injOn he, Finset.card_powersetCard]
  have hpoly : (X^k₁-X^k₂ : F[X]) ≠ 0 := by
    intro hz
    have heq := congrArg Polynomial.natDegree (sub_eq_zero.mp hz)
    exact hne (by simpa using heq)
  have hroots : values.val ⊆ (X^k₁-X^k₂ : F[X]).roots := by
    intro z hz
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hAS,_⟩ := Finset.mem_powersetCard.mp hA
    rw [Polynomial.mem_roots hpoly]
    have h₁ := subsetPolynomial_introspective A (fun a ha => hk₁ a (hAS ha)) w hw.pow_eq_one
    have h₂ := subsetPolynomial_introspective A (fun a ha => hk₂ a (hAS ha)) w hw.pow_eq_one
    simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X]
    rw [h₁,h₂,hk,sub_self]
  calc
    S.card.choose t = values.card := hv.symm
    _ ≤ (X^k₁-X^k₂ : F[X]).natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ max k₁ k₂ := by simpa using Polynomial.natDegree_sub_le (X^k₁ : F[X]) (X^k₂)

end ExactQuantumFactoring.Primality


end

end OAI
