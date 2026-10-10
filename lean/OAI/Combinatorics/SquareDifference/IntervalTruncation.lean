import OAI.Combinatorics.SquareDifference.GateExpansion

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Truncate

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

noncomputable def retainedFamily (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex) : Finset (Finset J) :=
  if v∈keep then liftSupportFamily p Q else (liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)

lemma retainedFamily_sub {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex) :
    retainedFamily p Q T keep v⊆liftSupportFamily p Q := by
  unfold retainedFamily
  split_ifs
  · exact Subset.rfl
  · exact filter_subset _ _

lemma retainedFamily_tail_den {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex)
    (U : Finset J) (hU : U∈liftSupportFamily p Q\retainedFamily p Q T keep v) : T<∏j∈U,p j := by
  have hu := mem_sdiff.mp hU
  unfold retainedFamily at hu
  split_ifs at hu with hv
  · exact False.elim (hu.2 hu.1)
  · exact lt_of_not_ge (fun h => hu.2 (mem_filter.mpr ⟨hu.1,h⟩))

noncomputable def retainedIntervalLift (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (v : TupleVertex) (x : ResidueSpace p) : ℝ :=
  ∑U∈retainedFamily p Q T keep v,intervalPiece p (a v) L (f v) U x

lemma retainedInterval_diff (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (v : TupleVertex) :
    intervalLift p (a v) L Q (f v)-retainedIntervalLift p a L Q T keep f v=
      fun x => ∑U∈liftSupportFamily p Q\retainedFamily p Q T keep v,intervalPiece p (a v) L (f v) U x := by
  funext x
  exact (eq_sub_iff_add_eq.mpr (sum_sdiff (retainedFamily_sub p Q T keep v))).symm

lemma uniform_marginal_moment {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F : V → X → ℝ) (R : ℝ)
    (hm : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r))
    (v w : V) :
    Llaw (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
      1*R^(2*Fintype.card {w : V // w≠v}) := by
  rw [hmar w (fun x => |F w x|^(2*Fintype.card {w : V // w≠v}))]
  simp only [(even_two_mul _).pow_abs,one_mul]
  apply hm
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)

lemma interval_tail_energy (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q T : ℕ) (hT : 0<T) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^2)≤R^2)
    (v : TupleVertex) :
    conditionalEnergy (jointDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (Equiv.funSplitAt v _))
      (intervalLift p (a v) L Q (f v)-retainedIntervalLift p a L Q T keep f v)≤
      (T:ℝ)^(-(1:ℝ)/32)*(1*R^2) := by
  rw [retainedInterval_diff]
  apply (tupleGoodTensor_conductor_energy p hp v _
    (intervalPiece p (a v) L (f v)) (fun U _ => intervalPiece_exactSupport p (a v) L (f v) U)
    T (by exact_mod_cast hT) (fun U hU => by exact_mod_cast (retainedFamily_tail_den p Q T keep v U hU).le)).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_left (hm v _ sdiff_subset)
    (Real.rpow_nonneg (Nat.cast_nonneg T) (-(1:ℝ)/32))

lemma uniform_truncation_error {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X] [DecidableEq X]
    (Llaw : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤Llaw F)
    (hmar : ∀(v : V) (g : X → ℝ),Llaw (fun z => g (z v))=𝔼 x,g x)
    (F G : V → X → ℝ) (T R : ℝ) (hT : 0<T) (hR : 0≤R)
    (henergy : ∀v,conditionalEnergy (jointDensity Llaw (Equiv.funSplitAt v X)) (F v-G v)≤T^(-(1:ℝ)/32)*(1*R^2))
    (hmF : ∀v r,r+1=Fintype.card V → (𝔼 x,F v x^(2*r))≤R^(2*r))
    (hmG : ∀v r,r+1=Fintype.card V → (𝔼 x,G v x^(2*r))≤R^(2*r)) :
    |multilinearIntegral Llaw F-multilinearIntegral Llaw G|≤
      (Fintype.card V:ℝ)*T^(-(1:ℝ)/64)*R^(Fintype.card V) := by
  have hb := multilinear_truncation_error Llaw hpos F G T 1 R hT zero_le_one hR henergy
    (fun v w => ⟨uniform_marginal_moment Llaw hmar F R hmF v w,
      uniform_marginal_moment Llaw hmar G R hmG v w⟩)
  simpa only [mul_one] using hb

lemma tensor_all_marginals {V : Type*} [Fintype V] [DecidableEq V]
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hm : ∀j (v : V) (g : ZMod (p j) → ℝ),Llaw j (fun z => g (z v))=𝔼 x,g x) :
    ∀(v : V) (g : ResidueSpace p → ℝ),tensorLaw Llaw (fun z => g (z v))=𝔼 x,g x := by
  exact fun v g => tensorLaw_marginal Llaw v (fun j => hm j v) g

lemma tensorGood_uniform_marginal (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (v : TupleVertex) (g : ResidueSpace p → ℝ) :
    tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun z => g (z v))=𝔼 x,g x := by
  exact tensor_all_marginals p (fun j => tupleGoodLaw (p:=p j))
    (fun j => tupleGoodLaw_marginal ((le_max_left _ _).trans (hp j))) v g

lemma interval_full_moment (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v r,r+1=Fintype.card TupleVertex → (𝔼 x,intervalLift p (a v) L Q (f v) x^(2*r))≤R^(2*r) := by
  exact fun v r hr => hm v _ Subset.rfl r (Or.inr hr)

lemma interval_retained_moment (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v r,r+1=Fintype.card TupleVertex →
      (𝔼 x,retainedIntervalLift p a L Q T keep f v x^(2*r))≤R^(2*r) := by
  exact fun v r hr => hm v _ (retainedFamily_sub p Q T keep v) r (Or.inr hr)

lemma interval_two_moment (a : TupleVertex → ℕ) (L Q : ℕ) (f : TupleVertex → ℕ → ℝ) (R : ℝ)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    ∀v s,s⊆liftSupportFamily p Q → (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^2)≤R^2 := by
  exact fun v s hs => hm v s hs 1 (Or.inl rfl)

lemma interval_truncation_error (hp : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ))
    (a : TupleVertex → ℕ) (L Q T : ℕ) (hT : 0<T) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (R : ℝ) (hR : 0≤R)
    (hm : ∀v s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p (a v) L (f v) U x)^(2*r))≤R^(2*r)) :
    |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (fun v => intervalLift p (a v) L Q (f v))-
      multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j))) (retainedIntervalLift p a L Q T keep f)|≤
      (Fintype.card TupleVertex:ℝ)*(T:ℝ)^(-(1:ℝ)/64)*R^(Fintype.card TupleVertex) := by
  exact uniform_truncation_error (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
    (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg)) (tensorGood_uniform_marginal p hp)
    _ _ _ _ (by exact_mod_cast hT) hR
    (interval_tail_energy p hp a L Q T hT keep f R (interval_two_moment p a L Q f R hm))
    (interval_full_moment p a L Q f R hm) (interval_retained_moment p a L Q T keep f R hm)

end Truncate

end SquareDifference

end

end OAI
