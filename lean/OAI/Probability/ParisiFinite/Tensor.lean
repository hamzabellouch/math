import Mathlib
import OAI.Probability.ParisiFinite.MixedMatrixOne

namespace OAI

/-! Tensor. -/

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
open scoped InnerProductSpace BigOperators
open ContinuousLinearMap
namespace TwoHalfTree
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 

def tensor (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (ι×κ) :=
  WithLp.toLp 2 (fun ij => x ij.1*y ij.2)

omit [Fintype ι] [Fintype κ] in
@[simp] theorem tensor_apply (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) (i : ι) (j : κ) :
    tensor x y (i,j)=x i*y j := rfl

theorem inner_tensor (x u : EuclideanSpace ℂ ι) (y v : EuclideanSpace ℂ κ) :
    ⟪tensor x y,tensor u v⟫_ℂ=⟪x,u⟫_ℂ*⟪y,v⟫_ℂ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,tensor_apply,Fintype.sum_prod_type,map_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def right (Ω : EuclideanSpace ℂ κ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ι×κ) where
  toFun x := tensor x Ω
  map_add' x y := by ext ⟨i,j⟩; simp [tensor,add_mul]
  map_smul' c x := by ext ⟨i,j⟩; simp [tensor,mul_assoc]

 
def appendVacuum (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ι×κ) where
  toLinearMap := right Ω
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    change Real.sqrt (⟪tensor x Ω,tensor x Ω⟫_ℂ).re=‖x‖
    have he : ⟪Ω,Ω⟫_ℂ=(1:ℂ) := by
      rw [inner_self_eq_norm_sq_to_K Ω,hΩ]
      norm_num
    rw [inner_tensor,he,mul_one]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) x).symm

@[simp] theorem appendVacuum_apply (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) (x : EuclideanSpace ℂ ι) :
    appendVacuum Ω hΩ x=tensor x Ω := rfl

def contract (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) :
    EuclideanSpace ℂ (ι×κ) →L[ℂ] EuclideanSpace ℂ ι :=
  (appendVacuum Ω hΩ).toContinuousLinearMap.adjoint

def projection (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) :
    EuclideanSpace ℂ (ι×κ) →L[ℂ] EuclideanSpace ℂ (ι×κ) :=
  (appendVacuum (ι := ι) Ω hΩ).toContinuousLinearMap.comp (contract Ω hΩ)

@[simp] theorem projection_apply (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×κ)) :
    projection Ω hΩ f=tensor (contract Ω hΩ f) Ω := rfl

theorem inner_contract (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) (f : EuclideanSpace ℂ (ι×κ)) :
    ⟪x,contract Ω hΩ f⟫_ℂ=⟪tensor x Ω,f⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

theorem contract_tensor_general (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    contract Ω hΩ (tensor x y)=⟪Ω,y⟫_ℂ • x := by
  apply ext_inner_left ℂ
  intro z
  rw [inner_contract,inner_tensor,inner_smul_right]
  ring

theorem contract_norm_le (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×κ)) : ‖contract Ω hΩ f‖≤‖f‖ := by
  calc
    _ ≤ ‖(appendVacuum (ι := ι) Ω hΩ).toContinuousLinearMap.adjoint‖*‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1*‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact (appendVacuum (ι := ι) Ω hΩ).norm_toContinuousLinearMap_le
    _ = _ := one_mul _

theorem contract_tensor (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) : contract Ω hΩ (tensor x Ω)=x := by
  apply ext_inner_left ℂ
  intro y
  rw [inner_contract,inner_tensor,inner_self_eq_norm_sq_to_K,hΩ]
  norm_num

theorem projection_isStarProjection (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) :
    IsStarProjection (projection (ι := ι) Ω hΩ) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    simp only [mul_apply_eq_comp,projection_apply,contract_tensor]
  · change star ((appendVacuum (ι := ι) Ω hΩ).toContinuousLinearMap.comp
        (appendVacuum (ι := ι) Ω hΩ).toContinuousLinearMap.adjoint)=_
    rw [star_eq_adjoint,adjoint_comp,adjoint_adjoint]
    rfl

 
def swap : EuclideanSpace ℂ (ι×ι) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι×ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm ι ι)

@[simp] theorem swap_apply (f : EuclideanSpace ℂ (ι×ι)) (i j : ι) :
    swap f (i,j)=f (j,i) := rfl

theorem swap_involutive : Function.Involutive (swap (ι := ι)) := by
  intro f
  ext ⟨i,j⟩
  rfl

@[simp] theorem swap_tensor (x y : EuclideanSpace ℂ ι) : swap (tensor x y)=tensor y x := by
  ext ⟨i,j⟩
  simp only [swap_apply,tensor_apply,mul_comm]

theorem swap_selfadjoint (f g : EuclideanSpace ℂ (ι×ι)) :
    ⟪f,swap g⟫_ℂ=⟪swap f,g⟫_ℂ := by
  have h := (swap (ι := ι)).inner_map_map (swap f) g
  simpa only [swap_involutive f] using h

 
theorem centered_cross (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×ι)) (hf : ⟪tensor Ω Ω,f⟫_ℂ=0) :
    ⟪projection Ω hΩ f,swap (projection Ω hΩ f)⟫_ℂ=0 := by
  rw [projection_apply,swap_tensor,inner_tensor,inner_contract,hf,mul_zero]

 

theorem single_side_pairing (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×ι)) :
    ⟪projection Ω hΩ f,swap f⟫_ℂ=⟪tensor Ω (contract Ω hΩ f),f⟫_ℂ := by
  rw [swap_selfadjoint,projection_apply,swap_tensor]

 

theorem edge_decomposition (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×ι)) (hf : ⟪tensor Ω Ω,f⟫_ℂ=0) :
    |(⟪f,swap f⟫_ℂ).re-2*(⟪tensor Ω (contract Ω hΩ f),f⟫_ℂ).re|≤
      ‖f-projection Ω hΩ f‖^2 := by
  have h := EdgeProjection.real_decomposition (H := EuclideanSpace ℂ (ι×ι))
    (swap (ι := ι)) (swap_involutive (ι := ι)) (projection (ι := ι) Ω hΩ)
    (projection_isStarProjection (ι := ι) Ω hΩ) f (centered_cross Ω hΩ f hf)
  simpa only [single_side_pairing] using h

end TwoHalfTree

 

open scoped InnerProductSpace BigOperators
namespace TwoHalfTree
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

def row (f : EuclideanSpace ℂ (ι×κ)) (i : ι) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j => f (i,j))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem row_apply (f : EuclideanSpace ℂ (ι×κ)) (i : ι) (j : κ) : row f i j=f (i,j) := rfl

def rightMapLinear (T : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ν) :
    EuclideanSpace ℂ (ι×κ) →ₗ[ℂ] EuclideanSpace ℂ (ι×ν) where
  toFun f := WithLp.toLp 2 (fun ij => T (row f ij.1) ij.2)
  map_add' f g := by
    have hr (i : ι) : row (f+g) i=row f i+row g i := rfl
    ext ⟨i,j⟩
    simp only [hr,map_add,PiLp.add_apply]
  map_smul' c f := by
    have hr (i : ι) : row (c • f) i=c • row f i := rfl
    ext ⟨i,j⟩
    simp only [hr,map_smul,PiLp.smul_apply,RingHom.id_apply]

theorem rightMap_inner (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (f g : EuclideanSpace ℂ (ι×κ)) :
    ⟪rightMapLinear T.toLinearMap f,rightMapLinear T.toLinearMap g⟫_ℂ=⟪f,g⟫_ℂ := by
  change (∑ij : ι×ν, ⟪T (row f ij.1) ij.2,T (row g ij.1) ij.2⟫_ℂ)=
    ∑ij : ι×κ,⟪f ij,g ij⟫_ℂ
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  exact T.inner_map_map (row f i) (row g i)

 

def rightMap (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν) :
    EuclideanSpace ℂ (ι×κ) →ₗᵢ[ℂ] EuclideanSpace ℂ (ι×ν) where
  toLinearMap := rightMapLinear T.toLinearMap
  norm_map' f := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),rightMap_inner]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) f).symm

@[simp] theorem rightMap_tensor (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    rightMap T (tensor x y)=tensor x (T y) := by
  have hr (i : ι) : row (tensor x y) i=x i • y := by
    ext j
    rfl
  ext ⟨i,j⟩
  change T (row (tensor x y) i) j=x i*T y j
  rw [hr,map_smul]
  rfl

 
theorem contract_rightMap (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) (Ψ : EuclideanSpace ℂ ν) (hΨ : ‖Ψ‖=1)
    (hT : T Ω=Ψ) (f : EuclideanSpace ℂ (ι×κ)) :
    contract Ψ hΨ (rightMap T f)=contract Ω hΩ f := by
  apply ext_inner_left ℂ
  intro x
  rw [inner_contract,inner_contract,←hT,←rightMap_tensor]
  exact (rightMap (ι := ι) T).inner_map_map _ _

theorem projection_rightMap (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) (Ψ : EuclideanSpace ℂ ν) (hΨ : ‖Ψ‖=1)
    (hT : T Ω=Ψ) (f : EuclideanSpace ℂ (ι×κ)) :
    projection Ψ hΨ (rightMap T f)=rightMap T (projection Ω hΩ f) := by
  rw [projection_apply,contract_rightMap T Ω hΩ Ψ hΨ hT,projection_apply,rightMap_tensor,hT]

theorem nonvacuum_rightMap_norm (T : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) (Ψ : EuclideanSpace ℂ ν) (hΨ : ‖Ψ‖=1)
    (hT : T Ω=Ψ) (f : EuclideanSpace ℂ (ι×κ)) :
    ‖rightMap T f-projection Ψ hΨ (rightMap T f)‖=‖f-projection Ω hΩ f‖ := by
  rw [projection_rightMap T Ω hΩ Ψ hΨ hT,←map_sub]
  exact (rightMap T).norm_map _

end TwoHalfTree

 

open scoped InnerProductSpace Topology BigOperators
open ContinuousLinearMap Filter
namespace FiniteTensor
variable {ι : Type*} [Fintype ι]

 
def splitChildIndex (D : ℕ) : (Fin (D+1) → ι) ≃ ((Fin D → ι)×ι) :=
  (Fin.consEquiv (fun _ : Fin (D+1) => ι)).symm.trans (Equiv.prodComm _ _)

def splitChild (D : ℕ) : EuclideanSpace ℂ (Fin (D+1) → ι) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ ((Fin D → ι)×ι) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitChildIndex D)

@[simp] theorem splitChild_apply (D : ℕ) (f : EuclideanSpace ℂ (Fin (D+1) → ι))
    (σ : Fin D → ι) (i : ι) : splitChild D f (σ,i)=f (Fin.cons i σ) := rfl

theorem splitChild_power (D : ℕ) (v : EuclideanSpace ℂ ι) :
    splitChild D (power (D+1) v)=TwoHalfTree.tensor (power D v) v := by
  ext ⟨σ,i⟩
  change (∏j : Fin (D+1),v ((Fin.cons i σ : Fin (D+1) → ι) j))=(∏j : Fin D,v (σ j))*v i
  rw [Fin.prod_univ_succ]
  exact mul_comm _ _

 

def deleteChild (D : ℕ) (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1) :
    EuclideanSpace ℂ (Fin (D+1) → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  (TwoHalfTree.contract Ω hΩ).comp (splitChild D).toContinuousLinearEquiv.toContinuousLinearMap

theorem deleteChild_power (D : ℕ) (Ω v : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1) :
    deleteChild D Ω hΩ (power (D+1) v)=⟪Ω,v⟫_ℂ • power D v := by
  change TwoHalfTree.contract Ω hΩ (splitChild D (power (D+1) v))=_
  rw [splitChild_power,TwoHalfTree.contract_tensor_general]

theorem deleteChild_norm_le (D : ℕ) (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (Fin (D+1) → ι)) : ‖deleteChild D Ω hΩ f‖≤‖f‖ := by
  change ‖TwoHalfTree.contract Ω hΩ (splitChild D f)‖≤‖f‖
  exact (TwoHalfTree.contract_norm_le Ω hΩ _).trans_eq ((splitChild D).norm_map f)

end FiniteTensor

namespace TensorPackets
open SpinOperators
variable {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]

 
def liftMap (T : H →L[ℂ] K) : Double H →L[ℂ] Double K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : Fin 2 => H) i)))

@[simp] theorem liftMap_apply (T : H →L[ℂ] K) (x : Double H) (i : Fin 2) :
    liftMap T x i=T (x i) := by simp [liftMap,PiLp.proj_apply]

theorem liftMap_term {κ : Type*} (T : H →L[ℂ] K) (s : List κ → H) (t : Term κ) :
    liftMap T (term s t)=term (T ∘ s) t := by
  classical
  ext i
  simp only [liftMap_apply,term_apply,Function.comp_apply]
  split_ifs <;> simp only [map_smul,map_zero]

theorem liftMap_packet {κ : Type*} (T : H →L[ℂ] K) (s : List κ → H) (ts : List (Term κ)) :
    liftMap T (packet s ts)=packet (T ∘ s) ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => rw [packet_cons,map_add,liftMap_term,ih,packet_cons]

end TensorPackets

 

open scoped InnerProductSpace BigOperators
namespace TensorEmbedding
open Matrix
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

 

def matrixPower (D : ℕ) (A : Matrix κ ι ℂ) : Matrix (Fin D → κ) (Fin D → ι) ℂ :=
  fun σ τ => ∏i,A (σ i) (τ i)

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
theorem matrixPower_mul (D : ℕ) (A : Matrix ν κ ℂ) (B : Matrix κ ι ℂ) :
    matrixPower D (A*B)=matrixPower D A*matrixPower D B := by
  ext σ τ
  simp only [matrixPower,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixPower_adjoint (D : ℕ) (A : Matrix κ ι ℂ) :
    matrixPower D A.conjTranspose=(matrixPower D A).conjTranspose := by
  ext σ τ
  simp only [matrixPower,conjTranspose_apply,star_prod]

omit [Fintype ι] in
theorem matrixPower_one (D : ℕ) : matrixPower D (1 : Matrix ι ι ℂ)=1 :=
  FiniteTensor.matrixPower_one D

def map (D : ℕ) (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (Fin D → ι) →ₗ[ℂ] EuclideanSpace ℂ (Fin D → κ) :=
  Matrix.toEuclideanLin (matrixPower D (Matrix.toEuclideanLin.symm T))

omit [Fintype ν] [DecidableEq ν] in
theorem map_comp (D : ℕ) (S : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ν)
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    map D (S.comp T)=(map D S).comp (map D T) := by
  simp only [map,Matrix.toLpLin_symm_comp,matrixPower_mul,Matrix.toLpLin_mul_same]

theorem map_id (D : ℕ) : map D (LinearMap.id : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)=LinearMap.id := by
  simp only [map,Matrix.toLpLin_symm_id,matrixPower_one,Matrix.toLpLin_one]

theorem map_adjoint (D : ℕ) (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    map D T.adjoint=(map D T).adjoint := by
  have he : Matrix.toEuclideanLin.symm T.adjoint=(Matrix.toEuclideanLin.symm T).conjTranspose := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin.apply_symm_apply,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin.apply_symm_apply]
  simp only [map,he,matrixPower_adjoint,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem map_inner (D : ℕ) (T : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (x y : EuclideanSpace ℂ (Fin D → ι)) :
    ⟪map D T.toLinearMap x,map D T.toLinearMap y⟫_ℂ=⟪x,y⟫_ℂ := by
  have he : T.toLinearMap.adjoint.comp T.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro w
    change ⟪w,T.toLinearMap.adjoint (T v)⟫_ℂ=⟪w,v⟫_ℂ
    rw [LinearMap.adjoint_inner_right]
    exact T.inner_map_map w v
  have hm : (map D T.toLinearMap).adjoint.comp (map D T.toLinearMap)=LinearMap.id := by
    rw [←map_adjoint,←map_comp,he,map_id]
  rw [←LinearMap.adjoint_inner_right]
  change ⟪x,((map D T.toLinearMap).adjoint.comp (map D T.toLinearMap)) y⟫_ℂ=_
  rw [hm]
  rfl

def isometry (D : ℕ) (T : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (Fin D → ι) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D → κ) where
  toLinearMap := map D T.toLinearMap
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),map_inner]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) x).symm

omit [Fintype κ] [DecidableEq κ] in
theorem map_power (D : ℕ) (T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ)
    (v : EuclideanSpace ℂ ι) :
    map D T (FiniteTensor.power D v)=FiniteTensor.power D (T v) := by
  let A := Matrix.toEuclideanLin.symm T
  have hT : T=Matrix.toEuclideanLin A := (Matrix.toEuclideanLin.apply_symm_apply T).symm
  rw [hT]
  simp only [map,Matrix.toEuclideanLin.symm_apply_apply]
  ext σ
  change (∑τ : Fin D → ι,(∏i,A (σ i) (τ i))*(∏i,v (τ i)))=∏i,∑j,A (σ i) j*v j
  simp_rw [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => A (σ i) j*v j)).symm

@[simp] theorem isometry_power (D : ℕ) (T : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (v : EuclideanSpace ℂ ι) :
    isometry D T (FiniteTensor.power D v)=FiniteTensor.power D (T v) :=
  map_power D T.toLinearMap v

end TensorEmbedding

 

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap
namespace TensorPackets
open SpinOperators
variable {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]

def liftIsometry (T : H →ₗᵢ[ℂ] K) : Double H →ₗᵢ[ℂ] Double K where
  toLinearMap := (liftMap T.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    have he : ⟪liftMap T.toContinuousLinearMap x,liftMap T.toContinuousLinearMap x⟫_ℂ=⟪x,x⟫_ℂ := by
      simp only [PiLp.inner_apply,liftMap_apply,LinearIsometry.coe_toContinuousLinearMap,
        T.inner_map_map]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    change Real.sqrt (⟪liftMap T.toContinuousLinearMap x,liftMap T.toContinuousLinearMap x⟫_ℂ).re=‖x‖
    rw [he]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) x).symm

@[simp] theorem liftIsometry_apply (T : H →ₗᵢ[ℂ] K) (x : Double H) (i : Fin 2) :
    liftIsometry T x i=T (x i) := by
  exact liftMap_apply T.toContinuousLinearMap x i

theorem liftIsometry_plus (T : H →ₗᵢ[ℂ] K) (v : H) :
    liftIsometry T (PointedTree.plusEmbedding v)=PointedTree.plusEmbedding (T v) := by
  ext i
  simp only [liftIsometry_apply,PointedTree.plusEmbedding_apply,map_smul]

theorem liftIsometry_act (T : H →ₗᵢ[ℂ] K) (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Double H) :
    liftIsometry T (act A v)=act A (liftIsometry T v) := by
  ext i
  simp only [liftIsometry_apply,act_apply,map_sum,map_smul]

def scalarVac (Ω : H) (hΩ : ‖Ω‖=1) : ℂ →ₗᵢ[ℂ] H where
  toFun c := c • Ω
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := (mul_smul _ _ _).trans rfl
  norm_map' c := by
    change ‖c • Ω‖=‖c‖
    rw [norm_smul,hΩ,mul_one]

theorem liftScalarVac_plus (Ω : H) (hΩ : ‖Ω‖=1) :
    liftIsometry (scalarVac Ω hΩ) PointedTree.plus=PointedTree.plusEmbedding Ω := by
  ext i
  rw [liftIsometry_apply]
  rfl

end TensorPackets

namespace FiniteTree
open TensorPackets SpinOperators

 
def pad (D : ℕ) : (h : ℕ) → Space D h →ₗᵢ[ℂ] Space D (h+1)
  | 0 => (split D 1).symm.toLinearIsometry.comp
      (liftIsometry (scalarVac (FiniteTensor.power D (vac D 0))
        (norm_power_of_norm_one D _ (norm_vac D 0))))
  | h+1 => (split D (h+2)).symm.toLinearIsometry.comp
      ((liftIsometry (TensorEmbedding.isometry D (pad D h))).comp (split D (h+1)).toLinearIsometry)

@[simp] theorem split_pad_zero (D : ℕ) (x : Space D 0) :
    split D 1 (pad D 0 x)=liftIsometry (scalarVac (FiniteTensor.power D (vac D 0))
        (norm_power_of_norm_one D _ (norm_vac D 0))) x := by
  change split D 1 ((split D 1).symm _)=_
  exact (split D 1).apply_symm_apply _

@[simp] theorem split_pad_succ (D h : ℕ) (x : Space D (h+1)) :
    split D (h+2) (pad D (h+1) x)=
      liftIsometry (TensorEmbedding.isometry D (pad D h)) (split D (h+1) x) := by
  change split D (h+2) ((split D (h+2)).symm _)=_
  exact (split D (h+2)).apply_symm_apply _

@[simp] theorem pad_vac (D h : ℕ) : pad D h (vac D h)=vac D (h+1) := by
  induction h with
  | zero =>
    apply (split D 1).injective
    rw [split_pad_zero]
    change liftIsometry _ PointedTree.plus=_
    rw [liftScalarVac_plus]
    exact ((split D 1).apply_symm_apply _).symm
  | succ h ih =>
    apply (split D (h+2)).injective
    rw [split_pad_succ]
    have hv (k : ℕ) : split D (k+1) (vac D (k+1))=
        PointedTree.plusEmbedding (FiniteTensor.power D (vac D k)) :=
      (split D (k+1)).apply_symm_apply _
    rw [hv h,hv (h+1),liftIsometry_plus,TensorEmbedding.isometry_power,ih]

theorem pad_root (D h : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Space D h) :
    pad D h (root D h A x)=root D (h+1) A (pad D h x) := by
  cases h with
  | zero =>
    apply (split D 1).injective
    rw [split_pad_zero,split_root,split_pad_zero]
    exact liftIsometry_act _ A x
  | succ h =>
    apply (split D (h+2)).injective
    rw [split_pad_succ,split_root,split_root,split_pad_succ,liftIsometry_act]

end FiniteTree

 

namespace OperatorIntertwine
open ContinuousLinearMap
variable {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem power (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (h : ∀x,T (A x)=B (T x)) (n : ℕ) (x : H) : T ((A^n) x)=(B^n) (T x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change T (A ((A^n) x))=B ((B^n) (T x))
    rw [h,ih]

 

theorem exponential (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (h : ∀x,T (A x)=B (T x)) (x : H) :
    T (NormedSpace.exp A x)=NormedSpace.exp B (T x) := by
  have hl := T.hasSum ((ContinuousLinearMap.apply ℂ H x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A))
  have hr := (ContinuousLinearMap.apply ℂ K (T x)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B)
  have hh (n : ℕ) : T (((n.factorial:ℂ)⁻¹ • A^n) x)=
      (((n.factorial:ℂ)⁻¹ • B^n) (T x)) := by
    simp only [smul_apply,map_smul,power T A B h]
  simp only [ContinuousLinearMap.apply_apply] at hl hr
  simp_rw [hh] at hl
  exact hl.unique hr

 

theorem adjoint (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (hA : A ∈ unitary _) (hB : B ∈ unitary _) (h : ∀x,T (A x)=B (T x)) (x : H) :
    T (star A x)=star B (T x) := by
  have ha : A (star A x)=x := by
    change (A*star A) x=x
    rw [(Unitary.mem_iff.mp hA).2]
    rfl
  have hh := congrArg (fun y => star B y) (h (star A x))
  rw [ha] at hh
  have hb : star B (B (T (star A x)))=T (star A x) := by
    change (star B*B) (T (star A x))=_
    rw [(Unitary.mem_iff.mp hB).1]
    rfl
  exact (hh.trans hb).symm

end OperatorIntertwine

 

namespace TensorEmbedding
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

 

theorem map_operator (D : ℕ) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    map D A.toLinearMap=(FiniteTensor.operatorPower D A).toLinearMap := by
  have he : Matrix.toEuclideanLin.symm A.toLinearMap=(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm A := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin.apply_symm_apply,←Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).apply_symm_apply]
  unfold map FiniteTensor.operatorPower
  rw [he]
  exact (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin _).symm

theorem isometry_intertwine (D : ℕ)
    (T : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ)
    (h : ∀x,T (A x)=B (T x)) (v : EuclideanSpace ℂ (Fin D → ι)) :
    isometry D T (FiniteTensor.operatorPower D A v)=
      FiniteTensor.operatorPower D B (isometry D T v) := by
  have he : T.toLinearMap.comp A.toLinearMap=B.toLinearMap.comp T.toLinearMap := by
    apply LinearMap.ext
    exact h
  have hh := congrArg (map D) he
  rw [map_comp,map_comp,map_operator,map_operator] at hh
  exact congrArg (fun L => L v) hh

end TensorEmbedding

 

namespace FiniteTree
open SpinOperators TensorPackets ContinuousLinearMap

theorem pad_control (D h : ℕ)
    (K : Fin 2 → Space D h →L[ℂ] Space D h)
    (L : Fin 2 → Space D (h+1) →L[ℂ] Space D (h+1))
    (hKL : ∀i x,pad D h (K i x)=L i (pad D h x)) (v : Space D (h+1)) :
    pad D (h+1) (control D h K v)=control D (h+1) L (pad D (h+1) v) := by
  apply (split D (h+2)).injective
  rw [split_pad_succ,split_control,split_control,split_pad_succ]
  ext i : 1
  simp only [liftIsometry_apply,diagonal_apply]
  exact TensorEmbedding.isometry_intertwine D (pad D h) (K i) (L i) (hKL i) _

namespace Even

theorem pad_observable {D h : ℕ} (U : Even D h) (V : Even D (h+1))
    (hUV : ∀x,pad D h (U.op x)=V.op (pad D h x)) (x : Space D h) :
    pad D h (U.observable x)=V.observable (pad D h x) := by
  change pad D h (star U.op (root D h RootSpin.Z (U.op x)))=
    star V.op (root D (h+1) RootSpin.Z (V.op (pad D h x)))
  have hs (y : Space D h) : pad D h (star U.op y)=star V.op (pad D h y) :=
    OperatorIntertwine.adjoint (pad D h).toContinuousLinearMap U.op V.op U.unitary V.unitary hUV y
  rw [hs,pad_root,hUV]

theorem pad_exponential {D h : ℕ} (U : Even D h) (V : Even D (h+1))
    (hUV : ∀x,pad D h (U.op x)=V.op (pad D h x)) (t : ℝ) (x : Space D h) :
    pad D h (U.exponential t x)=V.exponential t (pad D h x) := by
  apply OperatorIntertwine.exponential (pad D h).toContinuousLinearMap
  intro y
  change pad D h ((Complex.I*(t:ℂ)) • U.observable y)=
    (Complex.I*(t:ℂ)) • V.observable (pad D h y)
  rw [map_smul,U.pad_observable V hUV]

end Even

 

theorem pad_ordinary (D : ℕ) (w : List PointedTree.Gate) (h : ℕ)
    (hh : w.length≤h) (x : Space D h) :
    pad D h ((ordinary D w h).op x)=(ordinary D w (h+1)).op (pad D h x) := by
  induction w generalizing h with
  | nil => rfl
  | cons g w ih =>
    have hw : w.length≤h := by simpa only [List.length_cons] using (Nat.le_trans (Nat.le_succ w.length) hh)
    cases g with
    | mixer β =>
      change pad D h (root D h (RootSpin.R β) ((ordinary D w h).op x))=
        root D (h+1) (RootSpin.R β) ((ordinary D w (h+1)).op (pad D h x))
      rw [pad_root,ih h hw]
    | cost γ =>
      cases h with
      | zero => simp only [List.length_cons] at hh; omega
      | succ h =>
        have hlow : w.length≤h := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hh
        change pad D (h+1) (control D h
          (fun i => (ordinary D w h).exponential (if i=0 then -γ/Real.sqrt D else γ/Real.sqrt D))
          ((ordinary D w (h+1)).op x))=
          control D (h+1)
          (fun i => (ordinary D w (h+1)).exponential (if i=0 then -γ/Real.sqrt D else γ/Real.sqrt D))
          ((ordinary D w (h+2)).op (pad D (h+1) x))
        rw [pad_control D h _ _ (fun i y => Even.pad_exponential _ _ (ih h hlow) _ y),ih (h+1) hw]

 

theorem pad_insertion (D : ℕ) (w : List PointedTree.Gate) (h : ℕ) (hh : w.length≤h) :
    pad D h ((ordinary D w h).observable (vac D h))=
      (ordinary D w (h+1)).observable (vac D (h+1)) := by
  rw [Even.pad_observable _ _ (pad_ordinary D w h hh),pad_vac]

end FiniteTree

end

end OAI
