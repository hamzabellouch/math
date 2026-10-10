import OAI.Algebra.OddKaplansky.ModularGeneric

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6

section
namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [sectionInstance28 : Fintype E] [DecidableEq E]
variable (p : ℕ) [sectionInstance30 : Fact p.Prime] [sectionInstance29 : CharP K p]
abbrev C := Multiplicative (E → ZMod p)
abbrev R := MonoidAlgebra K (C (E := E) p)

def coordinate (i : E) : C (E := E) p := Multiplicative.ofAdd (Pi.single i 1)
def delta (x : E → ZMod p) : R (K := K) (E := E) p := MonoidAlgebra.single (Multiplicative.ofAdd x) 1
def X (i : E) : R (K := K) (E := E) p := delta p (Pi.single i 1) - 1

lemma coordinate_pow
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (i : E) : coordinate p i ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  ext j
  simp [coordinate, Pi.single_apply, apply_ite]

instance : CharP (R (K := K) (E := E) p) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero

lemma X_pow (i : E) : X (K := K) p i ^ p = 0 := by
  rw [X, sub_pow_char, one_pow]
  have he : delta (K := K) p (Pi.single i (1 : ZMod p)) ^ p = 1 := by
    change (MonoidAlgebra.of K (C (E := E) p) (coordinate p i)) ^ p = 1
    rw [← map_pow, coordinate_pow, map_one]
  rw [he, sub_self]

lemma delta_product
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) :
    delta (K := K) p x = ∏ i, (1 + X p i) ^ (x i).val := by
  have he : Multiplicative.ofAdd x = ∏ i, coordinate p i ^ (x i).val := by
    apply Multiplicative.toAdd.injective
    ext j
    simp only [toAdd_prod, toAdd_pow, coordinate, toAdd_ofAdd,
      Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ZMod.natCast_zmod_val]
  calc
    delta p x = MonoidAlgebra.of K _ (∏ i, coordinate p i ^ (x i).val) := congrArg _ he
    _ = ∏ i, (MonoidAlgebra.of K _ (coordinate p i)) ^ (x i).val := by simp only [map_prod, map_pow]
    _ = _ := by apply Finset.prod_congr rfl; intro i _; congr 1; simp [X, delta, coordinate]

open MvPolynomial in
def shiftPolynomial (x : E → ZMod p) : MvPolynomial E K := ∏ i : E, (1 + MvPolynomial.X i) ^ (x i).val

def eval : MvPolynomial E K →ₐ[K] R (K := K) (E := E) p := MvPolynomial.aeval (X p)

lemma eval_shiftPolynomial (x : E → ZMod p) : eval p (shiftPolynomial (K := K) p x) = delta p x := by
  rw [shiftPolynomial, map_prod]
  simp only [map_pow, map_add, map_one, eval, MvPolynomial.aeval_X]
  exact (delta_product p x).symm

lemma degreeOf_shiftPolynomial
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) (i : E) :
    (shiftPolynomial (K := K) p x).degreeOf i ≤ (x i).val := by
  unfold shiftPolynomial
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ j : E, (if i = j then 1 else 0) * (x j).val := by
      apply Finset.sum_le_sum
      intro j _
      apply (MvPolynomial.degreeOf_pow_le _ _ _).trans
      rw [Nat.mul_comm (x j).val]
      apply Nat.mul_le_mul_right
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      by_cases hij : i = j <;> simp [hij, MvPolynomial.degreeOf_X_of_ne]
    _ = (x i).val := by simp

def monomial (n : E → Fin p) : R (K := K) (E := E) p := ∏ i, X p i ^ (n i).val

def monomialSpan : Submodule K (R (K := K) (E := E) p) := Submodule.span K (Set.range (monomial p))

lemma eval_mem_span
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (f : MvPolynomial E K) (hf : ∀ i, f.degreeOf i < p) :
    eval p f ∈ monomialSpan (K := K) p := by
  rw [f.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hb (i : E) : d i < p := (MvPolynomial.monomial_le_degreeOf i hd).trans_lt (hf i)
  let n : E → Fin p := fun i => ⟨d i, hb i⟩
  have he : eval p (MvPolynomial.monomial d (f.coeff d)) = f.coeff d • monomial p n := by
    simp only [eval, MvPolynomial.aeval_monomial, monomial, n, Algebra.smul_def]
    congr 1
    exact Finsupp.prod_fintype _ _ (by simp)
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)

lemma span_eq_top : monomialSpan (K := K) (E := E) p = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using MonoidAlgebra.induction_on with
  | of g =>
    change delta p g.toAdd ∈ _
    rw [← eval_shiftPolynomial]
    apply eval_mem_span
    intro i
    exact (degreeOf_shiftPolynomial p g.toAdd i).trans_lt (ZMod.val_lt _)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul c x hx => exact Submodule.smul_mem _ c hx

end
end OddKaplansky.Augmentation

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {E : Type portUniverse4} [Field K] [Fintype E] [DecidableEq E]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

lemma monomial_independent : LinearIndependent K (monomial (K := K) (E := E) p) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact (span_eq_top p).ge
  · rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (C (E := E) p) K)]
    simp [C]

def gridBasis : Module.Basis (E → Fin p) K (R (K := K) (E := E) p) :=
  Module.Basis.mk (monomial_independent p) (span_eq_top p).ge
@[simp] lemma gridBasis_apply (n : E → Fin p) : gridBasis (K := K) p n = monomial p n :=
  Module.Basis.mk_apply _ _ _

lemma eval_zero_of_high_degree (f : MvPolynomial E K)
    (hf : ∀ d ∈ f.support, Fintype.card E * (p-1) < Finsupp.degree d) :
    eval p f = 0 := by
  rw [f.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hi : ∃ i : E, p ≤ d i := by
    by_contra! hn
    have hle : Finsupp.degree d ≤ Fintype.card E * (p-1) := by
      change d.sum (fun _ n => n) ≤ _
      rw [Finsupp.sum_fintype _ _ (by simp)]
      calc
        _ ≤ ∑ _i : E, (p-1) := Finset.sum_le_sum (fun i _ => by have := hn i; omega)
        _ = _ := by simp []
    exact (hf d hd).not_ge hle
  obtain ⟨i,hi⟩ := hi
  rw [eval, MvPolynomial.aeval_monomial]
  have hz : d.prod (fun i k => X (K := K) p i ^ k) = 0 := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact pow_eq_zero_of_le hi (X_pow p i)
  rw [hz, mul_zero]

lemma eval_ideal_power (n : ℕ) (hn : Fintype.card E * (p-1) < n)
    (f : MvPolynomial E K) (hf : f ∈ MvPolynomial.idealOfVars E K ^ n) : eval p f = 0 := by
  apply eval_zero_of_high_degree
  intro d hd
  exact hn.trans_le ((MvPolynomial.mem_pow_idealOfVars_iff n f).mp hf d hd)

end
end OddKaplansky.Augmentation

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse5} {E : Type portUniverse6} [Field K] [Fintype E] [sectionInstance31 : DecidableEq E]
variable (p : ℕ) [sectionInstance32 : Fact p.Prime] [sectionInstance33 : CharP K p]

def exponents (n : E → Fin p) : E →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (n i).val)
@[simp] lemma exponents_apply
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (n : E → Fin p) (i : E) : exponents p n i = (n i).val := rfl
lemma degree_exponents
    {E : Type contextUniverse1}
    [Fintype.{contextUniverse1} E]
    [DecidableEq.{contextUniverse1 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)] (n : E → Fin p) : Finsupp.degree (exponents p n) = ∑ i, (n i).val := by
  change (exponents p n).sum (fun _ a => a) = _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rfl
lemma eval_monomial
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (n : E → Fin p) :
    eval (K := K) p (MvPolynomial.monomial (exponents p n) 1) = monomial p n := by
  rw [eval, MvPolynomial.aeval_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (by simp)

lemma shiftPolynomial_sub_one_mem
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (x : E → ZMod p) :
    shiftPolynomial (K := K) p x - 1 ∈ MvPolynomial.idealOfVars E K := by
  let I := MvPolynomial.idealOfVars E K
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change Ideal.Quotient.mk I (_ - 1) = 0
  rw [map_sub, map_one, shiftPolynomial, map_prod]
  have hx (i : E) : Ideal.Quotient.mk I (MvPolynomial.X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  simp [map_pow, map_add, hx]

lemma annihilates_monomial (x : E → ZMod p) (n : E → Fin p) (ell : ℕ)
    (hn : Fintype.card E * (p-1) < ell + ∑ i, (n i).val) :
    (delta (K := K) p x - 1)^ell * monomial p n = 0 := by
  have hpow := Ideal.pow_mem_pow (shiftPolynomial_sub_one_mem (K := K) p x) ell
  have hmon : MvPolynomial.monomial (exponents p n) (1 : K) ∈
      MvPolynomial.idealOfVars E K ^ (∑ i, (n i).val) := by
    apply (MvPolynomial.monomial_mem_pow_idealOfVars_iff _ _ one_ne_zero).mpr
    rw [degree_exponents]
  have hmul : (shiftPolynomial (K := K) p x - 1)^ell * MvPolynomial.monomial (exponents p n) 1 ∈
      MvPolynomial.idealOfVars E K ^ (ell + ∑ i, (n i).val) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hpow hmon
  have he := eval_ideal_power p _ hn _ hmul
  simpa only [map_mul, map_pow, map_sub, map_one, eval_shiftPolynomial, eval_monomial] using he

end
end OddKaplansky.Augmentation

end

end OAI
