import OAI.Combinatorics.SquareDifference.Endpoint

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section ResidueCombine

variable {J : Type*} [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [instNeZeroM : NeZero M] (hM : ∀j,M.Coprime (p j))

include hp hM

lemma combined_residue (B : Finset J) (s : ZMod M) (z : ResidueSpace p) :
    ∃a : ℕ,a < M*(∏j∈B,p j) ∧ ∀n : ℕ,
      ((n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j) ↔ n%(M*(∏j∈B,p j))=a := by
  let p' : Option J → ℕ := fun j => j.elim M p
  let : ∀j,NeZero (p' j) := fun j => by cases j <;> dsimp [p'] <;> infer_instance
  have hp' : Pairwise fun i j => (p' i).Coprime (p' j) := by
    intro i j hij
    cases i with
    | none => cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hM j
    | some i => cases j with
      | none => exact (hM i).symm
      | some j => exact hp (fun h => hij (congrArg some h))
  let B' : Finset (Option J) := insert none (B.image some)
  let z' : ResidueSpace p' := fun j => by cases j with
    | none => exact s
    | some j => exact z j
  have hprod : (∏j∈B',p' j)=M*(∏j∈B,p j) := by
    rw [show B'=insert none (B.image some) by rfl,prod_insert (by simp),prod_image]
    · rfl
    · exact fun _ _ _ _ h => Option.some.inj h
  obtain ⟨a,ha,hres⟩ := residue_crt p' hp' B' z'
  refine ⟨a,by rwa [hprod] at ha,fun n => ?_⟩
  rw [←hprod,←hres]
  constructor
  · rintro ⟨hn,hj⟩ j hmem
    rcases mem_insert.mp hmem with rfl | hj'
    · exact hn
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hj'
      exact hj i hi
  · intro h
    refine ⟨h none (mem_insert_self _ _),fun j hj => ?_⟩
    exact h (some j) (mem_insert_of_mem (mem_image.mpr ⟨j,hj,rfl⟩))

omit hp hM in
lemma combined_modulus_coprime {J : Type*}
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (M : ℕ)
    [NeZero M]
    (hM : ∀ (j : J), M.Coprime (p j)) (B : Finset J) (j : J) (hj : j∉B) :
    (M*(∏i∈B,p i)).Coprime (p j) := by
  apply (hM j).mul_left
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  exact hp (fun he => hj (he ▸ hi))

lemma exists_combined_units (B : Finset J) :
    ∃w : ∀j,(ZMod (p j))ˣ,∀j,j∉B → (w j:ZMod (p j))=((M*(∏i∈B,p i):ℕ):ZMod (p j)) := by
  classical
  refine ⟨fun j => if hj : j∈B then 1 else ZMod.unitOfCoprime _ (combined_modulus_coprime p hp M hM B j hj),?_⟩
  intro j hj
  simp only [dite_eq_right hj,ZMod.coe_unitOfCoprime]

end ResidueCombine

noncomputable def smallResidueInput (M : ℕ) (A : Finset ℕ) (s : ZMod M) (n : ℕ) : ℝ :=
  (M:ℝ)*(if (n:ZMod M)=s then natIndicator A n else 0)

lemma smallResidueInput_bound (M : ℕ) (A : Finset ℕ) (s : ZMod M) (n : ℕ) :
    |smallResidueInput M A s n|≤M := by
  unfold smallResidueInput
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  split_ifs
  · exact natIndicator_bound A n
  · norm_num

lemma smallResidueInput_average (M : ℕ) [NeZero M] (A : Finset ℕ) (n : ℕ) :
    (𝔼 s : ZMod M,smallResidueInput M A s n)=natIndicator A n := by
  rw [expect_eq_sum_div_card]
  simp only [smallResidueInput,←mul_sum,sum_ite_eq,mem_univ,ite_true,card_univ,ZMod.card]
  exact mul_div_cancel_left₀ (natIndicator A n) (show (M:ℝ)≠0 from Nat.cast_ne_zero.mpr (NeZero.ne M))

section ActualResidueTransfer

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [NeZero M] (hM : ∀j,M.Coprime (p j))

include hp hM

lemma smallResidue_fiber_identity (B : Finset J) (s : ZMod M) (z : ResidueSpace p)
    (A : Finset ℕ) :
    ∃a : ℕ,a < M*(∏j∈B,p j) ∧ ∀n : ℕ,
      (∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then smallResidueInput M A s n else 0)=
        ((M*(∏j∈B,p j):ℕ):ℝ)*(if n%(M*(∏j∈B,p j))=a then natIndicator A n else 0) := by
  obtain ⟨a,ha,hres⟩ := combined_residue p hp M hM B s z
  refine ⟨a,ha,fun n => ?_⟩
  simp only [←hres]
  unfold smallResidueInput
  push_cast
  split_ifs <;> simp_all ; ring

lemma actual_set_fiber_transfer
    (hcond : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ))
    (N Q H L Qc : ℕ) (B : Finset J) (s : ZMod M) (z : ResidueSpace p)
    (hH : 0<H) (hHQ : H*(∏j∈B,p j)≤Q) (hHQc : H≤Qc)
    (hL : 0<L) (hNL : N≤(M*(∏j∈B,p j))^2*L)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (K M₁ M₂ : ℝ) (hK : 0≤K) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hm₁ : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p N (smallResidueInput M A s) U x)^(2*r))≤M₁^(2*r))
    (hm₂ : ∀C : Finset ℕ,C⊆range L → ∀t,t⊆liftSupportFamily p Qc →
      ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (natIndicator C) U x)^(2*r))≤M₂^(2*r))
    (hchild : ∀C : Finset ℕ,C⊆range L → NatSquareFree C → setFunctional p L Qc C≤K) :
    diagonalIntegral (productTupleLaw p)
      (fun x => actualTruncatedLift p N Q (smallResidueInput M A s) (freezeCoordinates B z x))≤
      (((M*(∏j∈B,p j):ℕ):ℝ)^2*L/N)^(Fintype.card TupleVertex)*
        (K+(Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex))+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M₁^(Fintype.card TupleVertex) := by
  let D := M*(∏j∈B,p j)
  have hD : 0<D := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M))
    (prod_pos (fun j _ => (Fact.out : (p j).Prime).pos))
  obtain ⟨a,ha,hres⟩ := smallResidue_fiber_identity p hp M hM B s z A
  obtain ⟨w,hw⟩ := exists_combined_units p hp M hM B
  apply actual_frozen_diagonal_transfer p hcond href N Q H D L Qc a B z hH hHQ hHQc
    hD hL ha hNL (smallResidueInput M A s) (natIndicator A)
    (natIndicator_vanish N A hA) hres w hw K M₁ M₂ hK hM₁ hM₂ hm₁
  · intro j hj t ht r hr
    have hid : (fun t => natIndicator A (a+D*j+D^2*t))=natIndicator (squareChild A (a+D*j) D L) := by
      funext t
      exact (squareChild_indicator N A hA (a+D*j) D L hNL t).symm
    rw [hid]
    exact hm₂ _ (squareChild_sub _ _ _ _) t ht r hr
  · intro j hj
    have hid : (fun t => natIndicator A (a+D*j+D^2*t))=natIndicator (squareChild A (a+D*j) D L) := by
      funext t
      exact (squareChild_indicator N A hA (a+D*j) D L hNL t).symm
    rw [hid]
    exact hchild _ (squareChild_sub _ _ _ _) (squareChild_free A hfree _ _ _ hD)

end ActualResidueTransfer

end SquareDifference

end

end OAI
