import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentSetElements

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
local instance orderedIndependentProductRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance orderedIndependentProductAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance orderedIndependentProductAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance orderedIndependentProductNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance orderedIndependentProductNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
local instance orderedIndependentProductAddCommGroup : AddCommGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommGroup
local instance orderedIndependentProductAddMonoid : AddMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddMonoid
local instance orderedIndependentProductSemiring : Semiring (Torus v Ω) :=
  (Torus.instRing v Ω).toSemiring
local instance orderedIndependentProductNonAssocSemiring : NonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonAssocSemiring
local instance orderedIndependentProductDistrib : Distrib (Torus v Ω) :=
  (Torus.instRing v Ω).toDistrib
local instance orderedIndependentProductMonoid : Monoid (Torus v Ω) :=
  (Torus.instRing v Ω).toMonoid
variable (u:V → M)

def wordExponent {r:ℕ} (a:Fin r → M) : M:=∑i,a i

def wordEnergy : {r:ℕ} → (Fin r → M) → ℤ
  | 0,_=>0
  | _+1,a=>Ω (a 0) (wordExponent (fun i=>a i.succ))+wordEnergy (fun i=>a i.succ)

lemma wordEnergy_eq_pairs {r:ℕ} (a:Fin r → M) :
    wordEnergy Ω a=∑i:Fin r,∑j:Fin r,if i < j then Ω (a i) (a j) else 0 := by
  induction r with
  | zero=>simp [wordEnergy]
  | succ r ih=>
    rw [wordEnergy,ih,Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ,Fin.not_lt_zero,ite_false,zero_add,Fin.succ_lt_succ_iff,
      Fin.succ_pos,ite_true]
    rw [wordExponent,map_sum]

lemma ordered_monomial_product {r:ℕ} (a:Fin r → M) :
    (List.ofFn (fun i=>Torus.X v Ω (a i))).prod=
      Torus.monomial v Ω (wordExponent a) (↑(v^(wordEnergy Ω a))) := by
  induction r with
  | zero=>simp [wordEnergy,wordExponent,Torus.X,Torus.monomial]; rfl
  | succ r ih=>
    rw [List.ofFn_succ,List.prod_cons,ih]
    change Torus.monomial v Ω (a 0) 1 * _=_
    rw [Torus.monomial_mul_monomial,wordEnergy]
    simp only [wordExponent,Fin.sum_univ_succ,zpow_add,Units.val_mul]
    congr 1
    rw [one_mul,mul_comm]

def BlockValid {r:ℕ} (a:Fin r → ℕ) (s:Fin r → Finset V) : Prop :=
  ∀i,IsIndependent Ω u (s i) ∧ (s i).card=a i

def blockLabels {r:ℕ} (s:Fin r → Finset V) : Fin r → M:=fun i=>∑x∈s i,u x

omit [Fintype V] in
lemma independentTerm_product {r:ℕ} (a:Fin r → ℕ) (s:Fin r → Finset V) :
    (List.ofFn (fun i=>independentTerm v Ω u (a i) (s i))).prod=
      if BlockValid Ω u a s then
        Torus.monomial v Ω (wordExponent (blockLabels u s)) (↑(v^(wordEnergy Ω (blockLabels u s)))) else 0 := by
  by_cases h:BlockValid Ω u a s
  · rw [ite_eq_left h]
    have H:(fun i=>independentTerm v Ω u (a i) (s i))=(fun i=>Torus.X v Ω (blockLabels u s i)):=by
      funext i
      exact ite_eq_left (h i)
    rw [H,ordered_monomial_product]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩:=not_forall.mp h
    apply List.prod_eq_zero
    apply List.mem_ofFn.mpr
    exact ⟨i,by simp only [independentTerm,ite_eq_right hi]⟩

lemma independentElement_product {r:ℕ} (a:Fin r → ℕ) :
    (List.ofFn (fun i=>independentElement v Ω u (a i))).prod=
      ∑s:Fin r → Finset V,
        if BlockValid Ω u a s then
          Torus.monomial v Ω (wordExponent (blockLabels u s)) (↑(v^(wordEnergy Ω (blockLabels u s)))) else 0 := by
  have H:∀r:ℕ,∀a:Fin r → ℕ,
      (List.ofFn (fun i=>independentElement v Ω u (a i))).prod=
        ∑s:Fin r → Finset V,(List.ofFn (fun i=>independentTerm v Ω u (a i) (s i))).prod := by
    intro r
    induction r with
    | zero=>intro a; simp
    | succ r ih=>
      intro a
      rw [List.ofFn_succ,List.prod_cons,ih,independentElement]
      erw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [←Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1)=>Finset V)),Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro s hs
      rw [List.ofFn_succ,List.prod_cons]
      rfl
  rw [H]
  apply Finset.sum_congr rfl
  intro s hs
  exact independentTerm_product v Ω u a s
end
end ElementaryPositivity.QuantumTorus

end

end OAI
