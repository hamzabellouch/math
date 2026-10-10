import OAI.Algebra.OddKaplansky.SectorGroup

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.NilpotentBasis
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {R : Type portUniverse2} [Field K] [Ring R] [Algebra K R]
variable (p : ℕ) (X : R) (b : Module.Basis (Fin p) K R)
variable (hb : ∀ i : Fin p, b i = X^i.val) (hX : X^p=0)
include hb hX in
lemma coeff_power (n : ℕ) (j : Fin p) : b.repr (X^n) j = if n=j.val then 1 else 0 := by
  by_cases hn : n<p
  · rw [← hb ⟨n,hn⟩]
    simp only [Module.Basis.repr_self,Finsupp.single_apply]
    congr 1
    exact propext Fin.ext_iff
  · rw [pow_eq_zero_of_le (by omega : p≤n) hX,map_zero,Finsupp.zero_apply,ite_eq_right (by omega)]
include hb hX in
lemma low_coefficient (ell : ℕ) (a : R) (ha : a*X^ell=0) (i : Fin p) (hi : i.val+ell<p) :
    b.repr a i=0 := by
  have hh := congrArg (fun v : R => b.repr v ⟨i.val+ell,hi⟩) ha
  rw [← b.sum_repr a,Finset.sum_mul] at hh
  have hstep (j : Fin p) : b.repr ((b.repr a j • b j) * X^ell) ⟨i.val+ell,hi⟩ =
      if j=i then b.repr a j else 0 := by
    rw [hb,smul_mul_assoc,← pow_add,map_smul,Finsupp.smul_apply,coeff_power p X b hb hX]
    simp only [Nat.add_right_cancel_iff,Fin.val_inj,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp only [map_sum,Finset.sum_apply',hstep,map_zero,Finsupp.zero_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  exact hh
include hb hX in
lemma right_divisible (ell : ℕ) (hell : ell≤p) (a : R) (ha : a*X^ell=0) :
    ∃ q : R, a=q*X^(p-ell) := by
  refine ⟨∑ i : Fin p, b.repr a i • X^(i.val-(p-ell)),?_⟩
  rw [Finset.sum_mul]
  conv_lhs => rw [← b.sum_repr a]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p - ell ≤ i.val
  · rw [smul_mul_assoc,← pow_add,Nat.sub_add_cancel hi,← hb]
  · have hz := low_coefficient p X b hb hX ell a ha i (by omega)
    rw [hz,zero_smul,zero_smul,zero_mul]
end
end OddKaplansky.NilpotentBasis

namespace OddKaplansky.CyclicAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} [Field K]
variable (p : ℕ) [Fact p.Prime] [sectionInstance69 : CharP K p]
abbrev C := Multiplicative (ZMod p)
abbrev R := MonoidAlgebra K (C p)
def gen : C p := Multiplicative.ofAdd 1
def X : R (K := K) p := MonoidAlgebra.single (gen p) 1-1
instance : CharP (R (K := K) p) p := CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero
lemma gen_pow : gen p ^ p =1 := by apply Multiplicative.toAdd.injective; simp [gen]
lemma nilpotent : X (K := K) p ^ p=0 := by
  rw [X,sub_pow_char,MonoidAlgebra.single_pow,gen_pow,one_pow,one_pow,← MonoidAlgebra.one_def,sub_self]
lemma gen_val (g : C p) : gen p ^ g.toAdd.val = g := by
  apply Multiplicative.toAdd.injective
  simp [gen]
lemma delta_binomial
    {K : Type contextUniverse1}
    [contextInstance1 : Field.{contextUniverse1} K]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance1))))
  p] (g : C p) : MonoidAlgebra.single g (1 : K) = (X p+1)^g.toAdd.val := by
  rw [X,sub_add_cancel,MonoidAlgebra.single_pow,one_pow,gen_val]
lemma spanning : ⊤ ≤ Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val)) := by
  intro a
  have hi : a ∈ Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val)) := by
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.of_apply,delta_binomial,add_pow]
      apply Submodule.sum_mem
      intro k hk
      simp only [one_pow,mul_one]
      rw [mul_comm,← nsmul_eq_mul]
      apply (Submodule.span K (Set.range (fun i : Fin p => X (K := K) p ^ i.val))).toAddSubmonoid.nsmul_mem
      apply Submodule.subset_span
      exact ⟨⟨k,lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) (ZMod.val_lt g.toAdd)⟩,rfl⟩
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | smul c a ha => exact Submodule.smul_mem _ c ha
  exact fun _ => hi
lemma independent : LinearIndependent K (fun i : Fin p => X (K := K) p ^ i.val) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (spanning p)
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (C p) K)]
  simp [C]
def basis : Module.Basis (Fin p) K (R (K := K) p) := Module.Basis.mk (independent p) (spanning p)
lemma basis_apply (i : Fin p) : basis (K := K) p i = X p^i.val := Module.Basis.mk_apply _ _ _
lemma right_divisible (ell : ℕ) (hell : ell≤p) (a : R (K := K) p) (ha : a*X p^ell=0) :
    ∃ q, a=q*X p^(p-ell) := NilpotentBasis.right_divisible p (X p) (basis p) (basis_apply p) (nilpotent p) ell hell a ha
end
end OddKaplansky.CyclicAlgebra

end

end OAI
