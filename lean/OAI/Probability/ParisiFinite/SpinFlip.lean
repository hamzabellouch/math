import Mathlib
import OAI.Probability.ParisiFinite.YAdd

namespace OAI

/-! Spin Flip. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SKQAOA.Masks
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

 
def spinFlip (R : Fin n → C) (ε : C → Bool) : Equiv.Perm (Configuration n) where
  toFun σ i := if ε (R i) then !(σ i) else σ i
  invFun σ i := if ε (R i) then !(σ i) else σ i
  left_inv σ := by funext i; cases h : ε (R i) <;> simp [h]
  right_inv σ := by funext i; cases h : ε (R i) <;> simp [h]

def flipGate (R : Fin n → C) (ε : C → Bool) : Operator n := (spinFlip R ε).permMatrix ℂ

omit [Fintype C] [DecidableEq C] in
@[simp] theorem spinFlip_symm (R : Fin n → C) (ε : C → Bool) :
    (spinFlip R ε).symm=spinFlip R ε := rfl

omit [Fintype C] [DecidableEq C] in
@[simp] theorem flipGate_adjoint (R : Fin n → C) (ε : C → Bool) :
    (flipGate R ε)ᴴ=flipGate R ε := by
  simp only [flipGate,Matrix.conjTranspose_permMatrix]
  rfl

omit [Fintype C] [DecidableEq C] in
@[simp] theorem flipGate_square (R : Fin n → C) (ε : C → Bool) :
    flipGate R ε*flipGate R ε=1 := by
  change (spinFlip R ε).permMatrix ℂ*(spinFlip R ε)⁻¹.permMatrix ℂ=1
  rw [←Matrix.permMatrix_mul,inv_mul_cancel,Matrix.permMatrix_one]

omit [Fintype C] [DecidableEq C] in
theorem flipGate_unitary (R : Fin n → C) (ε : C → Bool) :
    flipGate R ε∈unitary (Operator n) := by
  constructor <;> simp only [Matrix.star_eq_conjTranspose,flipGate_adjoint,flipGate_square]

omit [Fintype C] [DecidableEq C] in
@[simp] theorem spin_spinFlip (R : Fin n → C) (ε : C → Bool) (σ : Configuration n) (i : Fin n) :
    (spin (spinFlip R ε σ) i : ℂ)=MaskSign.sign ε (R i)*(spin σ i : ℂ) := by
  cases h : ε (R i) <;> cases hs : σ i <;> simp [spinFlip,spin,MaskSign.sign,h,hs]

 

omit [Fintype C] [DecidableEq C] in
theorem flipGate_conjugate_cost (R : Fin n → C) (ε : C → Bool) (J : Disorder n) :
    flipGate R ε*cost n J*flipGate R ε=
      ((Real.sqrt (n:ℝ))⁻¹ : ℂ) • ∑e : Edge n,
        (MaskSign.sign ε (R e.1.1)*MaskSign.sign ε (R e.1.2)*(J e:ℂ)) •
          (pauliZ e.1.1*pauliZ e.1.2) := by
  have hd (f : Configuration n → ℂ) :
      flipGate R ε*Matrix.diagonal f*flipGate R ε=
        Matrix.diagonal (fun σ => f (spinFlip R ε σ)) := by
    ext σ τ
    simp only [flipGate,Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv,Matrix.submatrix_apply]
    rw [Matrix.diagonal_apply,Matrix.diagonal_apply]
    congr 1
    exact propext (Equiv.apply_eq_iff_eq (spinFlip R ε))
  rw [cost_eq_diagonal,hd]
  ext σ τ
  simp only [Matrix.smul_apply,Matrix.sum_apply,pauliZ,Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply,smul_eq_mul]
  by_cases h : σ=τ
  · subst τ
    simp only [ite_true]
    simp only [hamiltonian,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv,spin_spinFlip]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  · simp [h]

end SKQAOA.Masks

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace MaskSign
variable {C : Type*} [Fintype C] [DecidableEq C]

 
theorem pair_projection {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (u v : ι → C) (A : ι → V) {a b : C} (hab : a≠b) :
    ((2:ℂ)^(Fintype.card C))⁻¹ •
      (∑ε : C → Bool,(sign ε a*sign ε b) •
        ∑i,(sign ε (u i)*sign ε (v i)) • A i)=
      ∑i,if (a=u i ∧ b=v i) ∨ (a=v i ∧ b=u i) then A i else 0 := by
  simp_rw [Finset.smul_sum,smul_smul,←mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_smul]
  have he : (∑ε : C → Bool,((2:ℂ)^(Fintype.card C))⁻¹*sign ε a*sign ε b*
      sign ε (u i)*sign ε (v i))=
      ((2:ℂ)^(Fintype.card C))⁻¹*
        ∑ε : C → Bool,sign ε a*sign ε b*sign ε (u i)*sign ε (v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε hε
    ring
  rw [he,sum_four hab]
  split_ifs <;> simp

end MaskSign

namespace SKQAOA.Masks
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

def pairEdges (R : Fin n → C) (a b : C) : Finset (Edge n) :=
  Finset.univ.filter (fun e => (a=R e.1.1 ∧ b=R e.1.2) ∨ (a=R e.1.2 ∧ b=R e.1.1))

 

theorem pairCost_identity (R : Fin n → C) (J : Disorder n) {a b : C} (hab : a≠b) :
    Locality.maskedCost J (pairEdges R a b)=
      ((2:ℂ)^(Fintype.card C))⁻¹ •
        ∑ε : C → Bool,(MaskSign.sign ε a*MaskSign.sign ε b) •
          (flipGate R ε*cost n J*flipGate R ε) := by
  have hf (ε : C → Bool) : flipGate R ε*cost n J*flipGate R ε=
      ∑e : Edge n,(MaskSign.sign ε (R e.1.1)*MaskSign.sign ε (R e.1.2)) •
        (((Real.sqrt (n:ℝ))⁻¹:ℂ) • ((J e:ℂ) • (pauliZ e.1.1*pauliZ e.1.2))) := by
    rw [flipGate_conjugate_cost,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [smul_smul]
    congr 1
    ring
  simp_rw [hf]
  rw [MaskSign.pair_projection (fun e : Edge n => R e.1.1)
    (fun e : Edge n => R e.1.2) _ hab]
  rw [Locality.maskedCost_sum,pairEdges,Finset.sum_filter,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

 

omit [Fintype C] in
theorem pairEdges_distinct (R : Fin n → C) {a b : C} (hab : a≠b)
    {e : Edge n} (he : e∈pairEdges R a b) : R e.1.1≠R e.1.2 := by
  rcases (Finset.mem_filter.mp he).2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact fun h => hab (ha.trans (h.trans hb.symm))
  · exact fun h => hab (ha.trans (h.symm.trans hb.symm))

end SKQAOA.Masks

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SKQAOA.Masks
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

def signReal (ε : C → Bool) (a : C) : ℝ := if ε a then -1 else 1

omit [Fintype C] [DecidableEq C] in
@[simp] theorem signReal_cast (ε : C → Bool) (a : C) :
    (signReal ε a : ℂ)=MaskSign.sign ε a := by
  cases h : ε a <;> simp [signReal,MaskSign.sign,h]

def signedDisorder (R : Fin n → C) (ε : C → Bool) (J : Disorder n) : Disorder n :=
  fun e => signReal ε (R e.1.1)*signReal ε (R e.1.2)*J e

omit [Fintype C] [DecidableEq C] in
theorem flipGate_cost (R : Fin n → C) (ε : C → Bool) (J : Disorder n) :
    flipGate R ε*cost n J*flipGate R ε=cost n (signedDisorder R ε J) := by
  rw [flipGate_conjugate_cost]
  simp only [cost,signedDisorder,Complex.ofReal_mul,signReal_cast]

def pairWeight (a b : C) (ε : C → Bool) : ℝ :=
  ((2:ℝ)^(Fintype.card C))⁻¹*signReal ε a*signReal ε b

theorem pairCost_weighted (R : Fin n → C) (J : Disorder n) {a b : C} (hab : a≠b) :
    Locality.maskedCost J (pairEdges R a b)=
      ∑ε : C → Bool,(pairWeight a b ε:ℂ) • cost n (signedDisorder R ε J) := by
  rw [pairCost_identity R J hab,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ε hε
  rw [flipGate_cost]
  simp only [smul_smul,pairWeight,Complex.ofReal_mul,Complex.ofReal_inv,
    Complex.ofReal_pow,Complex.ofReal_ofNat,signReal_cast]
  congr 1
  ring

omit [Fintype C] [DecidableEq C] in
theorem flipGate_evolution (R : Fin n → C) (ε : C → Bool) (J : Disorder n) (t : ℝ) :
    evolution t (cost n (signedDisorder R ε J))=
      flipGate R ε*evolution t (cost n J)*flipGate R ε := by
  let U : (Operator n)ˣ := ⟨flipGate R ε,flipGate R ε,flipGate_square R ε,flipGate_square R ε⟩
  have hr : (↑U : Operator n)=flipGate R ε := rfl
  have hi : (↑(U⁻¹) : Operator n)=flipGate R ε := rfl
  rw [←flipGate_cost]
  unfold evolution
  have he : (-(t:ℂ)*Complex.I) • (flipGate R ε*cost n J*flipGate R ε)=
      (↑U : Operator n)*((-(t:ℂ)*Complex.I) • cost n J)*↑(U⁻¹) := by
    rw [hr,hi,Matrix.mul_smul,Matrix.smul_mul]
  rw [he,Matrix.exp_units_conj,hr,hi]

 

theorem evolution_list_sum {ι : Type*} (A : ι → Operator n) (θ : ι → ℝ)
    (hc : ∀i j,Commute (A i) (A j)) (l : List ι) :
    evolution 1 ((l.map (fun i => (θ i:ℂ) • A i)).sum)=
      (l.map (fun i => evolution (θ i) (A i))).prod := by
  induction l with
  | nil => simp [evolution]
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,List.prod_cons]
    have hcomm : Commute ((θ i:ℂ) • A i) ((l.map (fun j => (θ j:ℂ) • A j)).sum) := by
      apply Commute.list_sum_right
      intro B hB
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hB
      exact ((hc i j).smul_left _).smul_right _
    rw [Locality.evolution_add_of_commute 1 hcomm,ih]
    congr 1
    simp only [evolution,smul_smul,Complex.ofReal_one]
    congr 1
    ring_nf

 

theorem pairCost_evolution_word (R : Fin n → C) (J : Disorder n)
    {a b : C} (hab : a≠b) (t : ℝ) :
    evolution t (Locality.maskedCost J (pairEdges R a b))=
      (Finset.univ.toList.map (fun ε : C → Bool =>
        flipGate R ε*evolution (t*pairWeight a b ε) (cost n J)*flipGate R ε)).prod := by
  have hs : (Finset.univ.toList.map (fun ε : C → Bool =>
      ((t*pairWeight a b ε:ℝ):ℂ) • cost n (signedDisorder R ε J))).sum=
      (t:ℂ) • Locality.maskedCost J (pairEdges R a b) := by
    rw [Finset.sum_map_toList,pairCost_weighted R J hab,Finset.smul_sum]
    simp only [Complex.ofReal_mul,smul_smul]
  have he : evolution t (Locality.maskedCost J (pairEdges R a b))=
      evolution 1 ((t:ℂ) • Locality.maskedCost J (pairEdges R a b)) := by
    simp only [evolution,smul_smul,Complex.ofReal_one]
    congr 1
    ring_nf
  rw [he,←hs,evolution_list_sum]
  · congr 1
    apply List.map_congr_left
    intro ε hε
    exact flipGate_evolution R ε J _
  · intro ε δ
    rw [cost_eq_diagonal,cost_eq_diagonal]
    exact Matrix.commute_diagonal _ _

end SKQAOA.Masks

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SKQAOA.Masks
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

 

omit [Fintype C] [DecidableEq C] in
theorem flipGate_tensor (R : Fin n → C) (ε : C → Bool) :
    flipGate R ε=TensorMatrix.lift (fun i => if ε (R i) then TwoState.swap else 1) := by
  ext σ τ
  have he (i : Fin n) :
      (if ε (R i) then TwoState.swap else 1) (σ i) (τ i)=
        if spinFlip R ε σ i=τ i then (1:ℂ) else 0 := by
    cases h : ε (R i) <;> cases hs : σ i <;> cases ht : τ i <;>
      simp [spinFlip,TwoState.swap,h,hs]
  simp only [flipGate,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,TensorMatrix.lift,he,Fintype.prod_ite_zero,Finset.prod_const_one]
  congr 1
  exact propext (show spinFlip R ε σ=τ ↔ ∀i,spinFlip R ε σ i=τ i from funext_iff)

 
theorem tensor_scalar (c : Fin n → ℂ) (A : Fin n → Matrix Bool Bool ℂ) :
    TensorMatrix.lift (fun i => c i • A i)=(∏i,c i) • TensorMatrix.lift A := by
  ext σ τ
  simp [TensorMatrix.lift,Finset.prod_mul_distrib]

 
def maskedMixer (R : Fin n → C) (ε : C → Bool) : Operator n :=
  ∑i : Fin n,if ε (R i) then pauliX i else 0

omit [Fintype C] [DecidableEq C] in
theorem maskedMixer_evolution (R : Fin n → C) (ε : C → Bool) (t : ℝ) :
    evolution t (maskedMixer R ε)=
      TensorMatrix.lift (fun i => if ε (R i) then TwoState.rotation t else 1) := by
  have he : (-(t:ℂ)*Complex.I) • maskedMixer R ε =
      ∑i : Fin n,TensorMatrix.atSite i
        (if ε (R i) then (-(t:ℂ)*Complex.I) • TwoState.swap else 0) := by
    simp only [maskedMixer,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp only [smul_zero,TensorMatrix.local_zero,pauliX_eq_atSite,TensorMatrix.local_smul]
  unfold evolution
  rw [he,TensorMatrix.exp_sum_atSite_univ]
  congr 1
  funext i
  cases h : ε (R i) <;> simp [TwoState.rotation_eq_exp]

 

omit [Fintype C] [DecidableEq C] in
theorem maskedMixer_flip (R : Fin n → C) (ε : C → Bool) :
    evolution (Real.pi/2) (maskedMixer R ε)=
      (∏i : Fin n,if ε (R i) then (-Complex.I) else 1) • flipGate R ε := by
  rw [maskedMixer_evolution,flipGate_tensor]
  have he : (fun i : Fin n => if ε (R i) then TwoState.rotation (Real.pi/2) else 1)=
      fun i => (if ε (R i) then (-Complex.I) else 1) •
        (if ε (R i) then TwoState.swap else 1) := by
    funext i
    cases h : ε (R i) <;> simp [TwoState.rotation]
  rw [he,tensor_scalar]

end SKQAOA.Masks

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator
attribute [local instance] LieRing.ofAssociativeRing

namespace SKQAOA.Helpers
variable {n : ℕ}

theorem twoState_ZY : TwoState.z*TwoState.y-TwoState.y*TwoState.z=
    (-2*Complex.I) • TwoState.swap := by
  ext a b
  cases a <;> cases b <;> norm_num [TwoState.z,TwoState.y,TwoState.swap,
    TwoState.sign,Matrix.mul_apply,Fintype.sum_bool,Complex.I_mul_I] <;> ring

theorem pauli_ZY (i : Fin n) : ⁅pauliZ i,pauliY i⁆=(-2*Complex.I) • pauliX i := by
  have h := congrArg (TensorMatrix.localAlgHom i) twoState_ZY
  simp only [map_sub,map_mul,map_smul] at h
  change TensorMatrix.atSite i TwoState.z*TensorMatrix.atSite i TwoState.y-
    TensorMatrix.atSite i TwoState.y*TensorMatrix.atSite i TwoState.z=
    (-2*Complex.I) • TensorMatrix.atSite i TwoState.swap at h
  simpa only [Ring.lie_def,pauliY,pauliX_eq_atSite,pauliZ_eq_atSite] using h

theorem commute_pauliX (i j : Fin n) : Commute (pauliX i) (pauliX j) := by
  by_cases h : i=j
  · subst j; exact Commute.refl _
  · rw [pauliX_eq_atSite,pauliX_eq_atSite]
    exact TensorMatrix.atSite_commute h _ _

theorem disjoint_ne {S T : Finset (Fin n)} (h : Disjoint S T)
    {i j : Fin n} (hi : i∈S) (hj : j∈T) : i≠j := by
  intro e
  subst j
  exact Finset.disjoint_left.mp h hi hj

 
theorem coefficient_bracket (B F : Operator n) (i : Fin n)
    (hBF : Commute B F) (hZ : Commute (pauliZ i) F)
    (hY : Commute (pauliY i) B) :
    ⁅B*pauliZ i,F*pauliY i⁆=(-2*Complex.I) • (B*F*pauliX i) := by
  rw [Ring.lie_def,hZ.mul_mul_mul_comm,hY.mul_mul_mul_comm,hBF.symm.eq,
    ←mul_sub,←Ring.lie_def,pauli_ZY,Matrix.mul_smul]

 

theorem pivot_sum_commutator (K : Finset (Fin n)) (B F : Fin n → Operator n)
    (hBF : ∀i∈K,∀j∈K,Commute (B i) (F j))
    (hB : ∀i∈K,∀j∈K,Commute (B i) (pauliY j))
    (hF : ∀i∈K,∀j∈K,Commute (F i) (pauliZ j)) :
    ⁅∑i∈K,B i*pauliZ i,∑i∈K,F i*pauliY i⁆=
      (-2*Complex.I) • ∑i∈K,B i*F i*pauliX i := by
  rw [sum_lie_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact coefficient_bracket _ _ _ (hBF i hi i hi) (hF i hi i hi).symm (hB i hi i hi).symm
  · intro j hj hji
    have hZY : Commute (pauliZ i) (pauliY j) := by
      rw [pauliY,pauliZ_eq_atSite]
      exact TensorMatrix.atSite_commute (Ne.symm hji) _ _
    have hc : Commute (B i*pauliZ i) (F j*pauliY j) :=
      ((hBF i hi j hj).mul_left (hF j hj i hi).symm).mul_right
        ((hB i hi j hj).mul_left hZY)
    exact sub_eq_zero.mpr hc.eq
  · exact fun h => (h hi).elim

 
def b (A : Fin n → Fin n → ℂ) (I : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (j : Fin n) : Operator n :=
  ∑i∈I,A j i • TensorMatrix.atSite i P

def B (A : Fin n → Fin n → ℂ) (I J : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (k : Fin n) : Operator n :=
  ∑j∈J,A k j • (pauliX j*b A I P j)

def F (A : Fin n → Fin n → ℂ) (J : Finset (Fin n)) (f : Fin n → ℂ)
    (k : Fin n) : Operator n :=
  ∑j∈J,(A k j*f j) • pauliX j

theorem b_commute_local (A : Fin n → Fin n → ℂ) (I : Finset (Fin n))
    (P Q : Matrix Bool Bool ℂ) (j k : Fin n) (hk : k∉I) :
    Commute (b A I P j) (TensorMatrix.atSite k Q) := by
  apply Commute.sum_left
  intro i hi
  exact (TensorMatrix.atSite_commute (i:=i) (j:=k) (fun h => hk (h ▸ hi)) P Q).smul_left _

theorem B_commute_local (A : Fin n → Fin n → ℂ) (I J : Finset (Fin n))
    (P Q : Matrix Bool Bool ℂ) (j k : Fin n) (hkI : k∉I) (hkJ : k∉J) :
    Commute (B A I J P j) (TensorMatrix.atSite k Q) := by
  apply Commute.sum_left
  intro i hi
  apply Commute.smul_left
  apply Commute.mul_left
  · rw [pauliX_eq_atSite]
    exact TensorMatrix.atSite_commute (i:=i) (j:=k) (fun h => hkJ (h ▸ hi)) _ _
  · exact b_commute_local _ _ _ _ _ _ hkI

theorem F_commute_local (A : Fin n → Fin n → ℂ) (J : Finset (Fin n))
    (f : Fin n → ℂ) (Q : Matrix Bool Bool ℂ) (j k : Fin n) (hk : k∉J) :
    Commute (F A J f j) (TensorMatrix.atSite k Q) := by
  apply Commute.sum_left
  intro i hi
  apply Commute.smul_left
  rw [pauliX_eq_atSite]
  exact TensorMatrix.atSite_commute (i:=i) (j:=k) (fun h => hk (h ▸ hi)) _ _

theorem B_commute_F (A : Fin n → Fin n → ℂ) (I J : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ) (k l : Fin n) (hIJ : Disjoint I J) :
    Commute (B A I J P k) (F A J f l) := by
  apply Commute.sum_right
  intro j hj
  apply Commute.smul_right
  apply Commute.sum_left
  intro i hi
  apply Commute.smul_left
  apply Commute.mul_left (commute_pauliX _ _)
  rw [pauliX_eq_atSite]
  exact b_commute_local _ _ _ _ _ _ (fun h => Finset.disjoint_left.mp hIJ h hj)

 

theorem helper_commutator (A : Fin n → Fin n → ℂ) (I J K : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K) :
    ⁅∑k∈K,B A I J P k*pauliZ k,∑k∈K,F A J f k*pauliY k⁆=
      (-2*Complex.I) • ∑k∈K,B A I J P k*F A J f k*pauliX k := by
  apply pivot_sum_commutator
  · intro i hi j hj
    exact B_commute_F _ _ _ _ _ _ _ hIJ
  · intro i hi j hj
    rw [pauliY]
    exact B_commute_local _ _ _ _ _ _ _
      (fun h => Finset.disjoint_left.mp hIK h hj)
      (fun h => Finset.disjoint_left.mp hJK h hj)
  · intro i hi j hj
    rw [pauliZ_eq_atSite]
    exact F_commute_local _ _ _ _ _ _
      (fun h => Finset.disjoint_left.mp hJK h hj)

end SKQAOA.Helpers

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SKQAOA.Masks
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
theorem maskedMixer_hermitian (R : Fin n → C) (ε : C → Bool) :
    (maskedMixer R ε).IsHermitian := by
  unfold maskedMixer Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : ε (R i) <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    Matrix.conjTranspose_zero]
  exact pauliX_hermitian i

 

omit [Fintype C] [DecidableEq C] in
theorem maskedMixer_conjugate (R : Fin n → C) (ε : C → Bool) (A : Operator n) :
    evolution (Real.pi/2) (maskedMixer R ε)*A*
      evolution (-(Real.pi/2)) (maskedMixer R ε)=flipGate R ε*A*flipGate R ε := by
  rw [evolution_neg_adjoint _ (maskedMixer_hermitian R ε),maskedMixer_flip,
    Matrix.conjTranspose_smul,flipGate_adjoint,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  have hp : (∏i : Fin n,if ε (R i) then (-Complex.I) else 1)*
      star (∏i : Fin n,if ε (R i) then (-Complex.I) else 1)=1 := by
    rw [star_prod,←Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    cases h : ε (R i) <;> simp [Complex.I_mul_I]
  rw [mul_comm (star _),hp,one_smul]

 

theorem pairCost_physical_word (R : Fin n → C) (J : Disorder n)
    {a b : C} (hab : a≠b) (t : ℝ) :
    evolution t (Locality.maskedCost J (pairEdges R a b))=
      (Finset.univ.toList.map (fun ε : C → Bool =>
        evolution (Real.pi/2) (maskedMixer R ε)*
          evolution (t*pairWeight a b ε) (cost n J)*
          evolution (-(Real.pi/2)) (maskedMixer R ε))).prod := by
  rw [pairCost_evolution_word R J hab t]
  congr 1
  apply List.map_congr_left
  intro ε hε
  exact (maskedMixer_conjugate R ε _).symm

end SKQAOA.Masks

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

namespace SKQAOA.Helpers
variable {n : ℕ}

@[simp] theorem pauliX_square (i : Fin n) : pauliX i*pauliX i=1 := by
  rw [pauliX_eq_atSite,←TensorMatrix.local_mul,←TensorMatrix.local_one i]
  congr 1
  ext a b
  cases a <;> cases b <;> norm_num [TwoState.swap,Matrix.mul_apply,Fintype.sum_bool]

 
theorem BF_expansion (A : Fin n → Fin n → ℂ) (I J : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ) (k : Fin n) :
    B A I J P k*F A J f k=
      ∑j∈J,∑l∈J,(A k j*(A k l*f l)) • (pauliX j*b A I P j*pauliX l) := by
  unfold B F
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]

 

theorem diagonal_sender (A : Fin n → Fin n → ℂ) (I J : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ) (k j : Fin n)
    (hIJ : Disjoint I J) (hj : j∈J) :
    (A k j • (pauliX j*b A I P j))*((A k j*f j) • pauliX j)=
      (A k j^2*f j) • b A I P j := by
  have hc : Commute (b A I P j) (pauliX j) := by
    rw [pauliX_eq_atSite]
    exact b_commute_local _ _ _ _ _ _ (fun h => Finset.disjoint_left.mp hIJ h hj)
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,←hc.eq,mul_assoc,pauliX_square,mul_one]
  congr 1
  ring

 

def diagonalGenerator (A : Fin n → Fin n → ℂ) (I J K : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ) : Operator n :=
  ∑k∈K,∑j∈J,(A k j^2*f j) • (b A I P j*pauliX k)

 

theorem diagonalGenerator_pinned (A : Fin n → Fin n → ℂ) (I J K : Finset (Fin n))
    (P : Matrix Bool Bool ℂ) (f : Fin n → ℂ) (ψ : State n)
    (hpin : ∀k∈K,(pauliX k).mulVec ψ=ψ) :
    (diagonalGenerator A I J K P f).mulVec ψ=
      (∑j∈J,((∑k∈K,A k j^2)*f j) • b A I P j).mulVec ψ := by
  simp only [diagonalGenerator,Matrix.sum_mulVec,Matrix.smul_mulVec,
    ←Matrix.mulVec_mulVec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hpin k hk]

 

theorem preserve_pin (i : Fin n) (U : Operator n) (ψ : State n)
    (hU : Commute (pauliX i) U) (hψ : (pauliX i).mulVec ψ=ψ) :
    (pauliX i).mulVec (U.mulVec ψ)=U.mulVec ψ := by
  rw [Matrix.mulVec_mulVec,hU.eq,←Matrix.mulVec_mulVec,hψ]

end SKQAOA.Helpers

end

end OAI
