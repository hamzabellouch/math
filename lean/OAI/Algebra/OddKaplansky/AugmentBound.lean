import OAI.Algebra.OddKaplansky.LocalAlgebra

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8

section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {T : Type portUniverse2} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [sectionInstance47 : CharP K p] (hT : ∀ t : T, t^p=1)
def X (t : T) : (MonoidAlgebra K T) := MonoidAlgebra.single t 1-1
include hT in
lemma X_nil (t : T) : X (K := K) t^p=0 := by
  rw [power_scalar p hT]
  simp [X,augment_single,(Fact.out : p.Prime).ne_zero]
@[instance_reducible]
def exponentModule : Module (ZMod p) (Additive T) :=
  AddCommGroup.zmodModule (fun t : Additive T => congrArg Additive.ofMul (hT t.toMul))
variable [Module (ZMod p) (Additive T)]

def differenceSubgroup (I : Ideal ((MonoidAlgebra K T))) : Subgroup T where
  carrier := {t | X t∈I}
  one_mem' := by simp [X,← MonoidAlgebra.one_def]
  mul_mem' {a b} ha hb := by
    have hh : X (K := K) (a*b)=X a*MonoidAlgebra.single b 1+X b := by
      simp only [X,sub_mul,MonoidAlgebra.single_mul_single,one_mul]
      abel
    change X (a*b)∈I
    rw [hh]
    exact I.add_mem (I.mul_mem_right _ ha) hb
  inv_mem' {a} ha := by
    have hh : X (K := K) a⁻¹=(-MonoidAlgebra.single a⁻¹ 1)*X a := by
      simp only [X,mul_sub,neg_mul,MonoidAlgebra.single_mul_single,inv_mul_cancel,mul_one,← MonoidAlgebra.one_def]
      abel
    change X a⁻¹∈I
    rw [hh]
    exact I.mul_mem_left _ ha

variable {ι : Type portUniverse3} [Fintype ι]
def generatorIdeal (b : Module.Basis ι (ZMod p) (Additive T)) : Ideal ((MonoidAlgebra K T)) :=
  ∑ i, Ideal.span {X (K := K) (b i).toMul}
lemma generator_mem
    {K : Type contextUniverse1}
    {T : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [contextInstance3 : CommGroup.{contextUniverse2} T]
    (p : Nat)
    [contextInstance5 : Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p]
    [@Module.{0, contextUniverse2} (ZMod p) (Additive.{contextUniverse2} T)
  (@CommSemiring.toSemiring.{0} (ZMod p)
    (@Semifield.toCommSemiring.{0} (ZMod p) (@Field.toSemifield.{0} (ZMod p) (@ZMod.instField p contextInstance5))))
  (@Additive.addCommMonoid.{contextUniverse2} T (@CommGroup.toCommMonoid.{contextUniverse2} T contextInstance3))]
    {ι : Type contextUniverse3}
    [Fintype.{contextUniverse3} ι] (b : Module.Basis ι (ZMod p) (Additive T)) (i : ι) :
    X (K := K) (b i).toMul ∈ generatorIdeal p b := by
  have hh : Ideal.span {X (K := K) (b i).toMul} ≤ generatorIdeal p b :=
by
    change Ideal.span {X (K := K) (b i).toMul} ≤ ∑ j, Ideal.span {X (K := K) (b j).toMul}
    exact Finset.single_le_sum (f := fun j => Ideal.span {X (K := K) (b j).toMul}) (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hh (Ideal.subset_span (by simp))
lemma difference_mem (b : Module.Basis ι (ZMod p) (Additive T)) (t : T) :
    X (K := K) t ∈ generatorIdeal p b := by
  let S := differenceSubgroup (generatorIdeal (K := K) p b)
  let V := AddSubgroup.toZModSubmodule p S.toAddSubgroup
  have hv : V=⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact generator_mem p b i
  have ht : Additive.ofMul t∈V := by rw [hv]; exact Submodule.mem_top
  exact ht
lemma scalar_difference_mem (I : Ideal ((MonoidAlgebra K T))) (hI : ∀ t, X t∈I) (a : (MonoidAlgebra K T)) :
    a-algebraMap K (MonoidAlgebra K T) (augment a)∈I := by
  induction a using MonoidAlgebra.induction_on with
  | of t => simpa only [X,MonoidAlgebra.of_apply,augment_single,map_one] using hI t
  | add a b ha hb =>
    rw [map_add,map_add]
    have hh : a+b-(algebraMap K (MonoidAlgebra K T) (augment a)+algebraMap K (MonoidAlgebra K T) (augment b)) =
        (a-algebraMap K (MonoidAlgebra K T) (augment a))+(b-algebraMap K (MonoidAlgebra K T) (augment b)) := by abel
    rw [hh]
    exact I.add_mem ha hb
  | smul c a ha =>
    have hh := I.mul_mem_left (algebraMap K (MonoidAlgebra K T) c) ha
    simpa only [map_smul,Algebra.smul_def,map_mul,AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply,mul_sub] using hh
lemma ker_le_generator (b : Module.Basis ι (ZMod p) (Additive T)) :
    RingHom.ker (augment (K := K) (T := T)).toRingHom ≤ generatorIdeal p b := by
  intro a ha
  have hh := scalar_difference_mem (generatorIdeal (K := K) p b) (difference_mem p b) a
  change augment a=0 at ha
  simpa only [ha,map_zero,sub_zero] using hh
end
end OddKaplansky.LocalAlgebra

namespace OddKaplansky.NilpotentSum
noncomputable section
open scoped Classical BigOperators
variable {R : Type portUniverse4} {ι : Type portUniverse5} [CommSemiring R]
lemma bounded (p : ℕ) (hp : 0<p) (s : Finset ι) (f : ι → R) (hf : ∀ i∈s, f i^p=0) :
    (∑ i∈s, f i)^(s.card*(p-1)+1)=0 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
    apply (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (hf a (by simp)) (ih fun i hi => hf i (by simp [hi]))
    rw [Nat.add_mul]
    omega
end
end OddKaplansky.NilpotentSum

namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse6} {T : Type portUniverse7} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable [Module (ZMod p) (Additive T)]
variable {ι : Type portUniverse8} [Fintype ι]
include hT in
lemma generator_nil (b : Module.Basis ι (ZMod p) (Additive T)) :
    generatorIdeal (K := K) p b ^(Fintype.card ι*(p-1)+1)=0 := by
  apply NilpotentSum.bounded p (Fact.out : p.Prime).pos Finset.univ
  intro i _
  rw [Ideal.span_singleton_pow,X_nil p hT]
  simp
include hT in
lemma kernel_nil_of_basis (b : Module.Basis ι (ZMod p) (Additive T)) :
    RingHom.ker (augment (K := K) (T := T)).toRingHom ^(Fintype.card ι*(p-1)+1)=0 := by
  apply le_antisymm
  · apply le_trans (pow_le_pow_left' (ker_le_generator p b) _)
    rw [generator_nil p hT b]
  · exact bot_le
variable [sectionInstance48 : Fintype T]
lemma dimension_le_three
    {T : Type contextUniverse1}
    [contextInstance1 : CommGroup.{contextUniverse1} T]
    (p : Nat)
    [contextInstance3 : Fact (Nat.Prime p)]
    [@Module.{0, contextUniverse1} (ZMod p) (Additive.{contextUniverse1} T)
  (@CommSemiring.toSemiring.{0} (ZMod p)
    (@Semifield.toCommSemiring.{0} (ZMod p) (@Field.toSemifield.{0} (ZMod p) (@ZMod.instField p contextInstance3))))
  (@Additive.addCommMonoid.{contextUniverse1} T (@CommGroup.toCommMonoid.{contextUniverse1} T contextInstance1))]
    [Fintype.{contextUniverse1} T] (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j) :
    Module.finrank (ZMod p) (Additive T)≤3 := by
  let L : Additive T →ₗ[ZMod p] (Fin 3 → ZMod p) := j.toAdditiveLeft.toZModLinearMap p
  have hl : Function.Injective L := by
    intro x y h
    exact hj h
  simpa using LinearMap.finrank_le_finrank_of_injective hl
omit [Module (ZMod p) (Additive T)] in
include hT in
lemma kernel_nil_three (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j) :
    RingHom.ker (augment (K := K) (T := T)).toRingHom ^(3*(p-1)+1)=0 := by
  let : Module (ZMod p) (Additive T) := exponentModule p hT
  let b := Module.finBasis (ZMod p) (Additive T)
  have hh := kernel_nil_of_basis (K := K) p hT b
  simp only [Fintype.card_fin] at hh
  exact pow_eq_zero_of_le (Nat.add_le_add_right (Nat.mul_le_mul_right (p-1) (dimension_le_three p j hj)) 1) hh
end
end OddKaplansky.LocalAlgebra

end

end OAI
