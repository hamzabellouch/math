import Mathlib
import OAI.Probability.BinarySweep.GridBounds.ProjectionSplitting
import OAI.Probability.BinarySweep.GridBounds.GroupedLogBounds
import OAI.Probability.BinarySweep.GridBounds.GridBoardAverage
import OAI.Probability.BinarySweep.FiniteLaws.SampleMoment

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

local instance : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits

def junctionAverage (p : A → Bool) (z : ℝ) :=
  sampleMatrix p (fun a => (conditionalGroupLaw H z a:ℂ)) (inputToJunction bits H).permCongr

def junctionFrame (p : A → Bool) :=
  actionMatrix p ((inputToJunction bits H).permCongr (framePermutation bits H))

lemma junctionAverage_linear (p : A → Bool) (z : ℝ) :
    (junctionAverage bits H p z).toEuclideanLin=
      groupAverage (junctionTensorRep bits H p) (fun a => (conditionalGroupLaw H z a:ℂ)) := by
  exact sampleMatrix_linear p _ _

lemma junctionAverage_split (p : A → Bool) (z : ℝ) :
    junctionAverage bits H p z=junctionFrame bits H p*columnMatrix bits H p z*rowMatrix bits H p z := by
  apply Matrix.toEuclideanLin.injective
  rw [junctionAverage_linear,groupAverage_split,rowAverage_matrix,columnAverage_matrix]
  simp only [Matrix.toLpLin_mul_same,←Module.End.mul_eq_comp,junctionFrame,actionMatrix_linear]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V)

omit [FiniteDimensional ℂ V] in
lemma projection_commutes_column (p : A → Bool) (z : ℝ) :
    isotypicProjection p ρ*columnMatrix bits H p z=columnMatrix bits H p z*isotypicProjection p ρ := by
  unfold columnMatrix
  rw [groupedAverage_law]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,typeProjection_commutes_action]

omit [FiniteDimensional ℂ V] in
lemma junction_projected_moment (p : A → Bool) (z : ℝ) (q : ℕ) :
    matrixMoment q (isotypicProjection p ρ*junctionAverage bits H p z)=
      matrixMoment q (columnMatrix bits H p z*isotypicProjection p ρ*rowMatrix bits H p z) := by
  rw [junctionAverage_split,←mul_assoc,←mul_assoc]
  have hu : isotypicProjection p ρ*junctionFrame bits H p=
      junctionFrame bits H p*isotypicProjection p ρ := typeProjection_commutes_action p ρ _
  rw [hu,mul_assoc (junctionFrame bits H p),projection_commutes_column,
    mul_assoc (junctionFrame bits H p)]
  rw [matrixMoment_linear,matrixMoment_linear,Matrix.toLpLin_mul_same,
    ←Module.End.mul_eq_comp]
  apply evenMoment_unitary_left
  change (Matrix.toEuclideanLin (junctionFrame bits H p)).adjoint*
    Matrix.toEuclideanLin (junctionFrame bits H p)=1
  unfold junctionFrame
  rw [actionMatrix_linear,unitary_rep_adjoint _ (hilbertTensorRep_unitary p),←map_mul,
    inv_mul_cancel,map_one]

theorem conditional_le_junction [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : A → Bool)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) :
    evenMoment q (groupAverage (ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      matrixMoment q (columnMatrix bits H p z*isotypicProjection p ρ*rowMatrix bits H p z) := by
  rw [←junction_projected_moment bits H ρ p z q]
  exact sampleMoment_le_projected p ρ hρ hocc _ _ hq

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.Signed
open Irrep Representation TraceHolder

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [LinearOrder I] [Nonempty I] [Fintype J] [LinearOrder J]
  {n : I → ℕ} {m : J → ℕ} {N : ℕ}

def typeF {n : ℕ} (α : n.Partition) : ℝ := Real.log (Module.finrank ℂ (Young.PartitionHilbert α):ℝ)

def blockLogSize {I : Type*} [Fintype I] (n : I → ℕ) : ℝ := ∑i, Real.log (n i+1:ℝ)

omit [Nonempty A] [Nonempty I] in
lemma blockActive_card_exp (p : A → Bool) :
    (Fintype.card (∀i, ActiveType p (n i)):ℝ)≤
      Real.exp ((Fintype.card A:ℝ)^2*blockLogSize n) := by
  have hc : (Fintype.card (∀i, ActiveType p (n i)):ℝ)≤∏i,(n i+1:ℝ)^((Fintype.card A)^2) := by
    exact_mod_cast blockActive_card (n:=n) p
  refine hc.trans_eq ?_
  rw [blockLogSize,Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact_mod_cast natShift_pow_exp (n i) ((Fintype.card A)^2)

theorem grouped_dense_bound
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
    (wR : ∀i, Equiv.Perm (Fin (n i)) → ℂ) (wC : ∀j, Equiv.Perm (Fin (m j)) → ℂ)
    {q : ℕ} (hq : 0<q) (c : ℝ) (hc : 0≤c) (hcq : c≤q)
    (ER : I → ℝ) (EC : J → ℝ)
    (hchildR : ∀i (a : ActiveType p (n i)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (wR i))≤Real.exp (-c*typeF a.val+ER i))
    (hchildC : ∀j (a : ActiveType p (m j)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (wC j))≤Real.exp (-c*typeF a.val+EC j)) :
    matrixMoment q (groupedAverage eC gC p wC*isotypicProjection p ρ*groupedAverage eR gR p wR) ≤
      Real.exp (-c*Real.log (Module.finrank ℂ W:ℝ)+(∑i, ER i)+(∑j, EC j)+
        c*(Fintype.card I*Fintype.card J-(N:ℝ))+
        (1+4*c+2*(q:ℝ))*(Fintype.card A:ℝ)^2*(blockLogSize n+blockLogSize m)) := by
  let R := fun a : ∀i, ActiveType p (n i) =>
    groupedProjection eR gR p (fun i => Young.partitionHilbertRep (a i).val)
  let C := fun a : ∀j, ActiveType p (m j) =>
    groupedProjection eC gC p (fun j => Young.partitionHilbertRep (a j).val)
  let FR := fun a : ∀i, ActiveType p (n i) => ∑i, typeF (a i).val
  let FC := fun a : ∀j, ActiveType p (m j) => ∑j, typeF (a j).val
  let L := blockLogSize n+blockLogSize m
  let D : ℝ := (Fintype.card A:ℝ)^2
  let E := (∑i, ER i)+(∑j, EC j)+D*L
  have hchild (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      matrixMoment q (groupedAverage eC gC p wC*C b)*
        matrixMoment q (R a*groupedAverage eR gR p wR)≤Real.exp (-c*(FR a+FC b)+E) := by
    have hr := grouped_projected_exp_bound eR gR p
      (fun i => Young.partitionHilbertRep (a i).val)
      (fun i => Young.partitionHilbertRep_unitary (a i).val) wR hq
      (fun i => -c*typeF (a i).val+ER i) (fun i => hchildR i (a i))
    have ht := grouped_projected_exp_bound eC gC p
      (fun j => Young.partitionHilbertRep (b j).val)
      (fun j => Young.partitionHilbertRep_unitary (b j).val) wC hq
      (fun j => -c*typeF (b j).val+EC j) (fun j => hchildC j (b j))
    rw [groupedProjection_commutes_average] at ht
    refine (mul_le_mul ht hr (matrixMoment_nonneg _ _) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    simp only [FR,FC,E,D,L,blockLogSize,Finset.sum_add_distrib,
      ←Finset.mul_sum,Nat.cast_pow]
    ring
  have ho (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      ‖C b*isotypicProjection p ρ*R a‖^2≤Real.exp
        (FR a+FC b-Real.log (Module.finrank ℂ W:ℝ)+
          (Fintype.card I*Fintype.card J-(N:ℝ))+4*D*L) := by
    exact actual_board_overlap_exp board p eR eC gR gC hR hC ρ
      (fun i => Young.partitionHilbertRep (a i).val) (fun j => Young.partitionHilbertRep (b j).val)
  have hk (a : ∀i, ActiveType p (n i)) (b : ∀j, ActiveType p (m j)) :
      ‖C b*isotypicProjection p ρ*R a‖≤1 :=
    groupedProjection_overlap_contract eR eC gR gC p ρ
      (fun i => Young.partitionHilbertRep (a i).val) (fun j => Young.partitionHilbertRep (b j).val)
  have hb := matrixMoment_dense_exponential hq (groupedAverage eR gR p wR)
    (groupedAverage eC gC p wC) (isotypicProjection p ρ) R C
    (fun a => groupedProjection_idempotent eR gR p _) (fun b => groupedProjection_idempotent eC gC p _)
    (groupedActive_projection_sum eR gR p) (groupedActive_projection_sum eC gC p)
    FR FC c (Real.log (Module.finrank ℂ W:ℝ)) (Fintype.card I*Fintype.card J-(N:ℝ))
    E (4*D*L) hc hcq hchild ho hk
  have hn : ((Fintype.card (∀i, ActiveType p (n i))*Fintype.card (∀j, ActiveType p (m j)):ℕ):ℝ) ≤
      Real.exp (D*L) := by
    rw [Nat.cast_mul]
    refine (mul_le_mul (blockActive_card_exp (n:=n) p) (blockActive_card_exp (n:=m) p)
      (by positivity) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    dsimp [D,L]
    ring
  refine hb.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn (2*q))
    (Real.exp_pos _).le).trans_eq ?_)
  rw [←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  dsimp [E,D,L]
  push_cast
  ring

end BinaryCoordinateSweeps.Signed

end

end OAI
