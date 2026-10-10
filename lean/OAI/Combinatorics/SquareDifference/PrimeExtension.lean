import OAI.Combinatorics.SquareDifference.ResidueReindex

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Indexed

variable {S J : Type*} [instFintypeS : Fintype S] [instDecidableEqS : DecidableEq S] [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ)

abbrev extendedPrime : S ⊕ J → ℕ := Sum.elim ps p

noncomputable def extendedRoots (B : Finset J) : Finset (S ⊕ J) := univ.disjSum B

@[simp] lemma inl_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (s : S) : Sum.inl s∈extendedRoots (S:=S) B := by simp [extendedRoots]
@[simp] lemma inr_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (j : J) : Sum.inr j∈extendedRoots (S:=S) B ↔ j∈B := by simp [extendedRoots]
noncomputable def outsideSumEquiv (B : Finset J) :
    {i : S ⊕ J // i∉extendedRoots (S:=S) B} ≃ {j : J // j∉B} where
  toFun i := match i with
    | ⟨Sum.inl s,hi⟩ => False.elim (hi (inl_mem_extendedRoots B s))
    | ⟨Sum.inr j,hi⟩ => ⟨j,fun hj => hi ((inr_mem_extendedRoots B j).mpr hj)⟩
  invFun j := ⟨Sum.inr j.val,by simpa using j.property⟩
  left_inv i := by
    rcases i with ⟨s|j,hi⟩
    · exact False.elim (hi (inl_mem_extendedRoots B s))
    · rfl
  right_inv _ := rfl

lemma extendedPrime_injective {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J]
    (ps : S → ℕ)
    (p : J → ℕ) (hs : Function.Injective ps) (hp : Function.Injective p)
    (hdis : ∀s j,ps s≠p j) : Function.Injective (extendedPrime ps p) := by
  intro i j hij
  cases i <;> cases j
  · exact congrArg Sum.inl (hs hij)
  · exact False.elim (hdis _ _ hij)
  · exact False.elim (hdis _ _ hij.symm)
  · exact congrArg Sum.inr (hp hij)

instance extendedPrime_prime [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime] :
    ∀i,Fact (extendedPrime ps p i).Prime := fun i => by cases i <;> dsimp [extendedPrime] <;> infer_instance

lemma extended_roots_modulus {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J]
    (ps : S → ℕ)
    (p : J → ℕ) (B : Finset J) (hp2 : ∀j,p j≠2) :
    rootSquareModulus (extendedPrime ps p) (extendedRoots (S:=S) B)=
      (∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j) := by
  unfold rootSquareModulus extendedRoots
  rw [prod_disjSum]
  simp only [extendedPrime,Sum.elim_inl,Sum.elim_inr,smallQuadraticModulus,hp2,ite_false]
  rfl

lemma extended_outside_modulus (B : Finset J) (hp2 : ∀j,p j≠2) :
    OutsideModulus (fun i => smallQuadraticModulus (extendedPrime ps p i)) (extendedRoots (S:=S) B)=
      fun i => OutsideModulus p B (outsideSumEquiv (S:=S) B i) := by
  funext i
  rcases i with ⟨s|j,hi⟩
  · exact False.elim (hi (inl_mem_extendedRoots B s))
  · simp only [OutsideModulus,outsideSumEquiv,extendedPrime,Sum.elim_inr,smallQuadraticModulus,hp2,ite_false,
      Equiv.coe_fn_mk]

end Indexed

lemma primary_product_cover {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r)
    (q : ℕ) (hq : 0<q) (hqN : q≤N) : q∣∏i,primaryModulus q (p i) := by
  have hS : q.primeFactors⊆univ.image p := by
    intro r hr
    obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hr
    obtain ⟨i,hi⟩ := hcover r hp ((Nat.le_of_dvd hq hd).trans hqN)
    exact mem_image.mpr ⟨i,mem_univ _,hi⟩
  have h := dvd_primaryModulus_product q hq.ne' (univ.image p) hS
  rwa [prod_image (fun _ _ _ _ h => hinj h)] at h

end SquareDifference

end

end OAI
