import Mathlib
import OAI.Probability.ParisiFinite.SumLeCode
import OAI.Probability.ParisiFinite.Tensor

namespace OAI

/-! Term Norm Sub. -/

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
open scoped InnerProductSpace Topology BigOperators
open ContinuousLinearMap Filter
namespace TensorPackets
open SpinOperators
variable {κ : Type*}

theorem term_norm_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s u : List κ → H) (t : Term κ) :
    ‖term s t-term u t‖=‖t.coeff‖*‖s t.history-u t.history‖ := by
  classical
  have he : term s t-term u t=t.coeff • PiLp.single 2 t.spin (s t.history-u t.history) := by
    ext i
    simp only [PiLp.sub_apply,term_apply,PiLp.smul_apply,PiLp.single_apply]
    split_ifs <;> simp [smul_sub]
  rw [he,norm_smul,PiLp.norm_single]

theorem packet_norm_sub_limit
    (Hn : ℕ → Type*) [∀n,NormedAddCommGroup (Hn n)] [∀n,InnerProductSpace ℂ (Hn n)]
    (s u : ∀n,List κ → Hn n)
    (hu : ∀w,Tendsto (fun n => ‖s n w-u n w‖) atTop (𝓝 0)) (ts : List (Term κ)) :
    Tendsto (fun n => ‖packet (s n) ts-packet (u n) ts‖) atTop (𝓝 0) := by
  induction ts with
  | nil => simpa only [packet_nil,sub_self,norm_zero] using tendsto_const_nhds
  | cons t ts ih =>
    have ht : Tendsto (fun n => ‖term (s n) t-term (u n) t‖) atTop (𝓝 0) := by
      simpa only [term_norm_sub,mul_zero] using (hu t.history).const_mul ‖t.coeff‖
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [add_zero] using ht.add ih)
    intro n
    simp only [packet_cons]
    rw [show term (s n) t+packet (s n) ts-(term (u n) t+packet (u n) ts)=
      (term (s n) t-term (u n) t)+(packet (s n) ts-packet (u n) ts) by abel]
    exact norm_add_le _ _

end TensorPackets

namespace FiniteTree.FullRoot
open RootTensorCLT TensorPackets SpinOperators

def deletion (D h : ℕ) : Space D h →L[ℂ] Double (FiniteTree.Tail D (h+1)) :=
  liftMap (FiniteTensor.deleteChild D (FiniteTree.vac D h) (FiniteTree.norm_vac D h))

theorem delete_tensorState (D h : ℕ) (l : List Label) :
    FiniteTensor.deleteChild D (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (tensorState D h l)=
      ⟪FiniteTree.vac D h,childState D h l⟫_ℂ •
        RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l := by
  exact FiniteTensor.deleteChild_power D _ _ _

theorem delete_tensorState_error (h : ℕ) (l : List Label) :
    Tendsto (fun D => ‖FiniteTensor.deleteChild D (FiniteTree.vac D h) (FiniteTree.norm_vac D h)
      (tensorState D h l)-RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l‖)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun D => ⟪FiniteTree.vac D h,childState D h l⟫_ℂ) atTop (𝓝 1) := by
    simpa only [childState,QuantumCLT.generators,List.map_nil,List.prod_nil,one_apply_eq_self]
      using child_Gram_limit h [] l
  apply (tendsto_iff_norm_sub_tendsto_zero.mp hg).congr
  intro D
  rw [delete_tensorState]
  have he : ⟪FiniteTree.vac D h,childState D h l⟫_ℂ •
      RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l-
      RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l=
      (⟪FiniteTree.vac D h,childState D h l⟫_ℂ-1) •
      RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l := by
    rw [sub_smul,one_smul]
  rw [he,norm_smul]
  rw [show ‖RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l‖=1
    from FiniteTree.norm_power_of_norm_one D (childState D h l) (norm_childState D h l)]
  exact (mul_one _).symm

 

theorem deletion_program_error (h : ℕ) (p : List (Pulse Label)) :
    Tendsto (fun D => ‖deletion D h (run (tensorPulse D h) p (vac D h))-
      run (RootTensorCLT.tensorPulse D (childGenerator D h)) p
        (PointedTree.plusEmbedding (FiniteTensor.power D (FiniteTree.vac D h)))‖)
      atTop (𝓝 0) := by
  have ht := TensorPackets.packet_norm_sub_limit
    (fun D => FiniteTree.Tail D (h+1))
    (fun D l => FiniteTensor.deleteChild D (FiniteTree.vac D h) (FiniteTree.norm_vac D h)
      (tensorState D h l))
    (fun D => RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h))
    (delete_tensorState_error h) (compile p start)
  have hc (D : ℕ) : run (RootTensorCLT.tensorPulse D (childGenerator D h)) p
      (PointedTree.plusEmbedding (FiniteTensor.power D (FiniteTree.vac D h)))=
      packet (RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h)) (compile p start) := by
    have he : RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) []=
        FiniteTensor.power D (FiniteTree.vac D h) := by
      simp [RootTensorCLT.tensorState,QuantumCLT.generators]
    rw [←he,←start_packet]
    exact RootTensorCLT.run_packet _ _ (RootTensorCLT.tensor_step D _ _) _ _
  simpa only [run_packet,deletion,liftMap_packet,hc,Function.comp_def] using ht

end FiniteTree.FullRoot

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree.FullRoot
open TensorPackets SpinOperators TwoHalfTree RootTensorCLT

def edgeIndex (D h : ℕ) :
    (Σ _ : Fin 2, Fin (D+1) → FiniteTree.Index D h) ≃
      (FiniteTree.Index D (h+1) × FiniteTree.Index D h) where
  toFun x := (⟨x.1,(FiniteTensor.splitChildIndex D x.2).1⟩,(FiniteTensor.splitChildIndex D x.2).2)
  invFun x := ⟨x.1.1,(FiniteTensor.splitChildIndex D).symm (x.1.2,x.2)⟩
  left_inv x := by
    rcases x with ⟨i,v⟩
    simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv x := by
    rcases x with ⟨⟨i,v⟩,c⟩
    simp only [Equiv.apply_symm_apply]

 

def edgeSplit (D h : ℕ) : Space D h ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (FiniteTree.Index D (h+1) × FiniteTree.Index D h) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2
    (fun (_ : Fin 2) (_ : Fin (D+1) → FiniteTree.Index D h) => ℂ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (edgeIndex D h))

@[simp] theorem edgeSplit_apply (D h : ℕ) (f : Space D h) (i : Fin 2)
    (σ : Fin D → FiniteTree.Index D h) (c : FiniteTree.Index D h) :
    edgeSplit D h f (⟨i,σ⟩,c)=f i (Fin.cons c σ) := rfl

 

def edgeEmbed (D h : ℕ) : Space D h →ₗᵢ[ℂ]
    EuclideanSpace ℂ (FiniteTree.Index D (h+1) × FiniteTree.Index D (h+1)) :=
  (rightMap (FiniteTree.pad D h)).comp (edgeSplit D h).toLinearIsometry

theorem edgeEmbed_apply (D h : ℕ) (f : Space D h) :
    edgeEmbed D h f=rightMap (FiniteTree.pad D h) (edgeSplit D h f) := rfl

theorem edgeSplit_term (D h : ℕ) (t : Term Label) :
    edgeSplit D h (term (tensorState D h) t)=
      tensor ((FiniteTree.split D (h+1)).symm
        (term (RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h)) t))
        (childState D h t.history) := by
  ext ⟨⟨i,σ⟩,c⟩
  rw [edgeSplit_apply,tensor_apply]
  change (term (tensorState D h) t i) (Fin.cons c σ)=
    (term (RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h)) t i) σ*
      childState D h t.history c
  rw [term_apply,term_apply]
  split_ifs with hi
  · change t.coeff*(∏j : Fin (D+1),childState D h t.history ((Fin.cons c σ : Fin (D+1) → FiniteTree.Index D h) j))=
      (t.coeff*(∏j : Fin D,childState D h t.history (σ j)))*childState D h t.history c
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    ring
  · simp

theorem edgeSplit_vac (D h : ℕ) :
    edgeSplit D h (vac D h)=tensor (FiniteTree.vac D (h+1)) (FiniteTree.vac D h) := by
  ext ⟨⟨i,σ⟩,c⟩
  rw [edgeSplit_apply,tensor_apply]
  change (((Real.sqrt 2)⁻¹:ℝ):ℂ)*(∏j : Fin (D+1),FiniteTree.vac D h
      ((Fin.cons c σ : Fin (D+1) → FiniteTree.Index D h) j))=
    ((((Real.sqrt 2)⁻¹:ℝ):ℂ)*(∏j : Fin D,FiniteTree.vac D h (σ j)))*FiniteTree.vac D h c
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

theorem edgeEmbed_vac (D h : ℕ) :
    edgeEmbed D h (vac D h)=tensor (FiniteTree.vac D (h+1)) (FiniteTree.vac D (h+1)) := by
  rw [edgeEmbed_apply,edgeSplit_vac,rightMap_tensor,FiniteTree.pad_vac]

theorem edgeSplit_deletion (D h : ℕ) (f : Space D h) :
    contract (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (edgeSplit D h f)=
      (FiniteTree.split D (h+1)).symm (deletion D h f) := by
  apply ext_inner_left ℂ
  intro x
  rw [inner_contract]
  
  rw [←(FiniteTree.split D (h+1)).inner_map_map x
    ((FiniteTree.split D (h+1)).symm (deletion D h f)),LinearIsometryEquiv.apply_symm_apply]
  have hc (u : EuclideanSpace ℂ (Fin D → FiniteTree.Index D h))
      (v : Tail D h) :
      ⟪u,FiniteTensor.deleteChild D (FiniteTree.vac D h) (FiniteTree.norm_vac D h) v⟫_ℂ=
        ⟪tensor u (FiniteTree.vac D h),FiniteTensor.splitChild D v⟫_ℂ :=
    TwoHalfTree.inner_contract _ _ u _
  conv_rhs => rw [PiLp.inner_apply]
  simp only [deletion,liftMap_apply,hc]
  simp only [PiLp.inner_apply,Fintype.sum_prod_type,Fintype.sum_sigma,
    RCLike.inner_apply,tensor_apply,FiniteTensor.splitChild_apply]
  rfl

end FiniteTree.FullRoot

 

open scoped InnerProductSpace
namespace TwoHalfTree
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem tensor_smul_left (c : ℂ) (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    tensor (c • x) y=c • tensor x y := by
  ext ⟨i,j⟩
  simp only [tensor_apply,PiLp.smul_apply,smul_eq_mul]
  ring

omit [Fintype ι] [Fintype κ] in
theorem tensor_smul_right (c : ℂ) (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    tensor x (c • y)=c • tensor x y := by
  ext ⟨i,j⟩
  simp only [tensor_apply,PiLp.smul_apply,smul_eq_mul]
  ring

omit [Fintype ι] [Fintype κ] in
theorem tensor_sub_right (x : EuclideanSpace ℂ ι) (y z : EuclideanSpace ℂ κ) :
    tensor x (y-z)=tensor x y-tensor x z := by
  ext ⟨i,j⟩
  simp only [tensor_apply,PiLp.sub_apply,mul_sub]

theorem norm_tensor (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    ‖tensor x y‖=‖x‖*‖y‖ := by
  have he := inner_tensor x x y y
  simp only [inner_self_eq_norm_sq_to_K] at he
  have hr : ‖tensor x y‖^2=‖x‖^2*‖y‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (tensor x y),mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem nonvacuum_tensor (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    tensor x y-projection Ω hΩ (tensor x y)=tensor x (y-⟪Ω,y⟫_ℂ • Ω) := by
  rw [projection_apply,contract_tensor_general,tensor_sub_right,tensor_smul_left,tensor_smul_right]

theorem nonvacuum_tensor_norm (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    ‖tensor x y-projection Ω hΩ (tensor x y)‖=‖x‖*‖y-⟪Ω,y⟫_ℂ • Ω‖ := by
  rw [nonvacuum_tensor,norm_tensor]

theorem vacuum_remainder_bound (Ω y : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1) :
    ‖y-⟪Ω,y⟫_ℂ • Ω‖≤2*‖y-Ω‖ := by
  let P : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ := 1-InnerProductSpace.rankOne ℂ Ω Ω
  have hP : P Ω=0 := by
    simp only [P,sub_apply,one_apply_eq_self,
      InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hΩ]
    norm_num
  have hn : ‖P‖≤2 := by
    calc
      _ ≤ ‖(1:EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ)‖+‖InnerProductSpace.rankOne ℂ Ω Ω‖ :=
        norm_sub_le _ _
      _ ≤ 1+1 := by
        apply add_le_add
        · exact ContinuousLinearMap.norm_id_le
        · simp [hΩ]
      _ = _ := by norm_num
  change ‖P y‖≤_
  have he : P y=P (y-Ω) := by rw [map_sub,hP,sub_zero]
  rw [he]
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

 

theorem nonvacuum_tensor_bound (Ω : EuclideanSpace ℂ κ) (hΩ : ‖Ω‖=1)
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) :
    ‖tensor x y-projection Ω hΩ (tensor x y)‖≤‖x‖*(2*‖y-Ω‖) := by
  rw [nonvacuum_tensor_norm]
  exact mul_le_mul_of_nonneg_left (vacuum_remainder_bound Ω y hΩ) (norm_nonneg _)

end TwoHalfTree

 

open scoped InnerProductSpace BigOperators Topology
open Filter
namespace FiniteTree.FullRoot
open TensorPackets SpinOperators TwoHalfTree RootTensorCLT

 

def edgeVector (D h : ℕ) (w : List PointedTree.Gate) :=
  edgeEmbed D h (insertion D h w)

theorem edgeVector_centered (D h : ℕ) (w : List PointedTree.Gate) :
    ⟪tensor (FiniteTree.vac D (h+1)) (FiniteTree.vac D (h+1)),edgeVector D h w⟫_ℂ=0 := by
  rw [←edgeEmbed_vac]
  exact ((edgeEmbed D h).inner_map_map _ _).trans (insertion_centered D h w)

theorem edgeVector_norm (D h : ℕ) (w : List PointedTree.Gate) :
    ‖edgeVector D h w‖=1 := by
  rw [edgeVector,(edgeEmbed D h).norm_map]
  exact norm_insertion D h w

theorem edge_contract (D h : ℕ) (w : List PointedTree.Gate) :
    contract (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1)) (edgeVector D h w)=
      (FiniteTree.split D (h+1)).symm (deletion D h (insertion D h w)) := by
  rw [edgeVector,edgeEmbed_apply,contract_rightMap (FiniteTree.pad D h)
    (FiniteTree.vac D h) (FiniteTree.norm_vac D h) _ _ (FiniteTree.pad_vac D h),edgeSplit_deletion]

 

theorem edge_deletion_limit (h : ℕ) (w : List PointedTree.Gate) :
    Tendsto (fun D => ‖contract (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1))
      (edgeVector D h w)-FiniteTree.insertion D (h+1) w‖) atTop (𝓝 0) := by
  have he (D : ℕ) : ‖contract (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1))
      (edgeVector D h w)-FiniteTree.insertion D (h+1) w‖=
      ‖deletion D h (insertion D h w)-
        run (RootTensorCLT.tensorPulse D (childGenerator D h)) (FiniteTree.insertionProgram w)
          (PointedTree.plusEmbedding (FiniteTensor.power D (FiniteTree.vac D h)))‖ := by
    rw [edge_contract,←(FiniteTree.split D (h+1)).norm_map,map_sub,
      LinearIsometryEquiv.apply_symm_apply,FiniteTree.split_insertion]
  simpa only [he,insertion] using deletion_program_error h (FiniteTree.insertionProgram w)

theorem edgeSplit_term_nonvacuum (D h : ℕ) (hD : 0<D) (t : Term Label) :
    ‖edgeSplit D h (term (tensorState D h) t)-
      projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h)
        (edgeSplit D h (term (tensorState D h) t))‖≤
      (‖t.coeff‖*(6*wordBound t.history))*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [edgeSplit_term]
  apply (nonvacuum_tensor_bound _ (FiniteTree.norm_vac D h) _ _).trans
  rw [LinearIsometryEquiv.norm_map,norm_term]
  have hn : ‖RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) t.history‖=1 :=
    FiniteTree.norm_power_of_norm_one D _ (norm_childState D h t.history)
  rw [hn,mul_one]
  calc
    _ ≤ ‖t.coeff‖*(2*(3*wordBound t.history*(Real.sqrt (D:ℝ))⁻¹)) := by
      gcongr
      exact child_word_vacuum_bound D h hD t.history
    _ = _ := by ring

theorem edgeSplit_packet_nonvacuum (D h : ℕ) (hD : 0<D) (ts : List (Term Label)) :
    ‖edgeSplit D h (packet (tensorState D h) ts)-
      projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h)
        (edgeSplit D h (packet (tensorState D h) ts))‖≤
      packetOccupationBound ts*(Real.sqrt (D:ℝ))⁻¹ := by
  induction ts with
  | nil => simp only [packet_nil,map_zero,sub_self,norm_zero,packetOccupationBound,List.map_nil,List.sum_nil,zero_mul,le_refl]
  | cons t ts ih =>
    rw [packet_cons,map_add,map_add]
    rw [show edgeSplit D h (term (tensorState D h) t)+edgeSplit D h (packet (tensorState D h) ts)-
      (projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (edgeSplit D h (term (tensorState D h) t))+
       projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (edgeSplit D h (packet (tensorState D h) ts)))=
      (edgeSplit D h (term (tensorState D h) t)-
       projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (edgeSplit D h (term (tensorState D h) t)))+
      (edgeSplit D h (packet (tensorState D h) ts)-
       projection (FiniteTree.vac D h) (FiniteTree.norm_vac D h) (edgeSplit D h (packet (tensorState D h) ts))) by abel]
    exact (norm_add_le _ _).trans ((add_le_add (edgeSplit_term_nonvacuum D h hD t) ih).trans_eq (by
      simp only [packetOccupationBound,List.map_cons,List.sum_cons,add_mul]))

 

theorem edge_nonvacuum_bound (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) :
    ‖edgeVector D h w-projection (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1))
      (edgeVector D h w)‖≤
      packetOccupationBound (compile (FiniteTree.insertionProgram w) start)*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [edgeVector,edgeEmbed_apply,nonvacuum_rightMap_norm (FiniteTree.pad D h)
    (FiniteTree.vac D h) (FiniteTree.norm_vac D h) _ _ (FiniteTree.pad_vac D h),insertion,run_packet]
  exact edgeSplit_packet_nonvacuum D h hD _

end FiniteTree.FullRoot

 

open scoped InnerProductSpace
namespace TwoHalfTree
variable {ι : Type*} [Fintype ι]

 

theorem replacement_pairing (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×ι)) (hf : ⟪tensor Ω Ω,f⟫_ℂ=0)
    (g : EuclideanSpace ℂ ι) :
    |(⟪tensor Ω (contract Ω hΩ f),f⟫_ℂ).re-(⟪tensor Ω g,f⟫_ℂ).re|≤
      ‖contract Ω hΩ f-g‖*‖f-projection Ω hΩ f‖ := by
  have hp : ⟪tensor Ω (contract Ω hΩ f-g),projection Ω hΩ f⟫_ℂ=0 := by
    rw [projection_apply,inner_tensor,inner_contract,hf,zero_mul]
  have he : ⟪tensor Ω (contract Ω hΩ f),f⟫_ℂ-⟪tensor Ω g,f⟫_ℂ=
      ⟪tensor Ω (contract Ω hΩ f-g),f-projection Ω hΩ f⟫_ℂ := by
    rw [inner_sub_right,hp,sub_zero,tensor_sub_right,inner_sub_left]
  calc
    _ = |(⟪tensor Ω (contract Ω hΩ f-g),f-projection Ω hΩ f⟫_ℂ).re| := by
      rw [←he,Complex.sub_re]
    _ ≤ ‖⟪tensor Ω (contract Ω hΩ f-g),f-projection Ω hΩ f⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖tensor Ω (contract Ω hΩ f-g)‖*‖f-projection Ω hΩ f‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_tensor,hΩ,one_mul]

 

theorem edge_replacement (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1)
    (f : EuclideanSpace ℂ (ι×ι)) (hf : ⟪tensor Ω Ω,f⟫_ℂ=0)
    (g : EuclideanSpace ℂ ι) :
    |(⟪f,swap f⟫_ℂ).re-2*(⟪tensor Ω g,f⟫_ℂ).re|≤
      ‖f-projection Ω hΩ f‖^2+
      2*‖contract Ω hΩ f-g‖*‖f-projection Ω hΩ f‖ := by
  let a := (⟪f,swap f⟫_ℂ).re
  let b := (⟪tensor Ω (contract Ω hΩ f),f⟫_ℂ).re
  let c := (⟪tensor Ω g,f⟫_ℂ).re
  have he : a-2*c=(a-2*b)+2*(b-c) := by ring
  change |a-2*c|≤_
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  exact add_le_add (edge_decomposition Ω hΩ f hf)
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (replacement_pairing Ω hΩ f hf g) (by norm_num : (0:ℝ)≤2))

end TwoHalfTree

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree.FullRoot
open TensorPackets SpinOperators TwoHalfTree RootTensorCLT ContinuousLinearMap

theorem excitation_pure (D h : ℕ) (w : List PointedTree.Gate) (y : FiniteTree.Space D h) :
    ⟪excitation D h w,FiniteTensor.power (D+1) y⟫_ℂ=
      (Real.sqrt ((D+1:ℕ):ℝ):ℂ)*⟪(FiniteTree.ordinary D w h).observable (FiniteTree.vac D h),y⟫_ℂ*
        ⟪FiniteTree.vac D h,y⟫_ℂ^D := by
  rw [←inner_conj_symm (excitation D h w) (FiniteTensor.power (D+1) y)]
  simp only [excitation,FiniteTensor.inner_normalizedInsertion,one_apply_eq_self,Nat.add_sub_cancel,
    map_mul,map_pow,Complex.conj_ofReal,inner_conj_symm]

 

theorem marked_term (D h : ℕ) (w : List PointedTree.Gate) (t : Term Label) :
    ⟪PointedTree.plusEmbedding (excitation D h w),term (tensorState D h) t⟫_ℂ=
      (Real.sqrt ((D+1:ℕ):ℝ):ℂ)*
      ⟪tensor (FiniteTree.vac D (h+1)) ((FiniteTree.ordinary D w h).observable (FiniteTree.vac D h)),
        edgeSplit D h (term (tensorState D h) t)⟫_ℂ := by
  rw [inner_plus_term,edgeSplit_term,inner_tensor]
  rw [←(FiniteTree.split D (h+1)).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply]
  have hv : FiniteTree.split D (h+1) (FiniteTree.vac D (h+1))=
      PointedTree.plusEmbedding (FiniteTensor.power D (FiniteTree.vac D h)) :=
    (FiniteTree.split D (h+1)).apply_symm_apply _
  rw [hv,inner_plus_term]
  change (((Real.sqrt 2)⁻¹:ℝ):ℂ)*t.coeff*
      ⟪excitation D h w,FiniteTensor.power (D+1) (childState D h t.history)⟫_ℂ=
    (Real.sqrt ((D+1:ℕ):ℝ):ℂ)*
      (((((Real.sqrt 2)⁻¹:ℝ):ℂ)*t.coeff*
        ⟪FiniteTensor.power D (FiniteTree.vac D h),FiniteTensor.power D (childState D h t.history)⟫_ℂ)*
      ⟪(FiniteTree.ordinary D w h).observable (FiniteTree.vac D h),childState D h t.history⟫_ℂ)
  rw [excitation_pure,FiniteTensor.inner_power]
  ring

theorem marked_packet (D h : ℕ) (w : List PointedTree.Gate) (ts : List (Term Label)) :
    ⟪PointedTree.plusEmbedding (excitation D h w),packet (tensorState D h) ts⟫_ℂ=
      (Real.sqrt ((D+1:ℕ):ℝ):ℂ)*
      ⟪tensor (FiniteTree.vac D (h+1)) ((FiniteTree.ordinary D w h).observable (FiniteTree.vac D h)),
        edgeSplit D h (packet (tensorState D h) ts)⟫_ℂ := by
  induction ts with
  | nil => simp only [packet_nil,map_zero,inner_zero_right,mul_zero]
  | cons t ts ih => simp only [packet_cons,map_add,inner_add_right,marked_term,ih,mul_add]

 

theorem marked_edge (D h : ℕ) (w u : List PointedTree.Gate) (hw : w.length≤h) :
    ⟪PointedTree.plusEmbedding (excitation D h w),insertion D h u⟫_ℂ=
      (Real.sqrt ((D+1:ℕ):ℝ):ℂ)*
      ⟪tensor (FiniteTree.vac D (h+1)) ((FiniteTree.ordinary D w (h+1)).observable (FiniteTree.vac D (h+1))),
        edgeEmbed D h (insertion D h u)⟫_ℂ := by
  rw [←FiniteTree.pad_insertion D w h hw,edgeEmbed_apply,←rightMap_tensor,
    (rightMap (FiniteTree.pad D h)).inner_map_map]
  simp only [insertion,run_packet]
  exact marked_packet D h w _

end FiniteTree.FullRoot

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace FiniteTree.FullRoot
open TwoHalfTree RootTensorCLT TensorPackets

 

def edgeValue (D h : ℕ) (w : List PointedTree.Gate) : ℝ :=
  Real.sqrt (D:ℝ)/2*(⟪edgeVector D h w,swap (edgeVector D h w)⟫_ℂ).re

def sideValue (D h : ℕ) (w : List PointedTree.Gate) : ℝ :=
  Real.sqrt (D:ℝ)*(⟪tensor (FiniteTree.vac D (h+1)) (FiniteTree.insertion D (h+1) w),
    edgeVector D h w⟫_ℂ).re

def deletionError (D h : ℕ) (w : List PointedTree.Gate) : ℝ :=
  ‖contract (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1)) (edgeVector D h w)-
    FiniteTree.insertion D (h+1) w‖

theorem edgeValue_error_bound (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) :
    |edgeValue D h w-sideValue D h w|≤
      (packetOccupationBound (compile (FiniteTree.insertionProgram w) start))^2/2*
        (Real.sqrt (D:ℝ))⁻¹+
      packetOccupationBound (compile (FiniteTree.insertionProgram w) start)*deletionError D h w := by
  let r := Real.sqrt (D:ℝ)
  have hr : 0<r := Real.sqrt_pos.2 (by exact_mod_cast hD)
  let C := packetOccupationBound (compile (FiniteTree.insertionProgram w) start)
  let e := ‖edgeVector D h w-projection (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1)) (edgeVector D h w)‖
  have he0 : 0≤e := norm_nonneg _
  have he : e≤C*r⁻¹ := edge_nonvacuum_bound D h hD w
  have hE : 0≤deletionError D h w := norm_nonneg _
  have hcmp := edge_replacement (FiniteTree.vac D (h+1)) (FiniteTree.norm_vac D (h+1))
    (edgeVector D h w) (edgeVector_centered D h w) (FiniteTree.insertion D (h+1) w)
  calc
    _ = r/2*|(⟪edgeVector D h w,swap (edgeVector D h w)⟫_ℂ).re-
        2*(⟪tensor (FiniteTree.vac D (h+1)) (FiniteTree.insertion D (h+1) w),edgeVector D h w⟫_ℂ).re| := by
      unfold edgeValue sideValue
      rw [show Real.sqrt (D:ℝ)/2*(⟪edgeVector D h w,swap (edgeVector D h w)⟫_ℂ).re-
        Real.sqrt (D:ℝ)*(⟪tensor (FiniteTree.vac D (h+1)) (FiniteTree.insertion D (h+1) w),edgeVector D h w⟫_ℂ).re=
        r/2*((⟪edgeVector D h w,swap (edgeVector D h w)⟫_ℂ).re-
          2*(⟪tensor (FiniteTree.vac D (h+1)) (FiniteTree.insertion D (h+1) w),edgeVector D h w⟫_ℂ).re) by dsimp [r]; ring]
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤r/2)]
    _ ≤ r/2*(e^2+2*deletionError D h w*e) := mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ ≤ r/2*((C*r⁻¹)^2+2*deletionError D h w*(C*r⁻¹)) := by
      gcongr
    _ = _ := by
      change r/2*((C*r⁻¹)^2+2*deletionError D h w*(C*r⁻¹))=
        C^2/2*r⁻¹+C*deletionError D h w
      field_simp [hr.ne']

theorem edge_side_difference_limit (h : ℕ) (w : List PointedTree.Gate) :
    Tendsto (fun D => edgeValue D h w-sideValue D h w) atTop (𝓝 0) := by
  have hr : Tendsto (fun D : ℕ => (Real.sqrt (D:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have he := edge_deletion_limit h w
  let C := packetOccupationBound (compile (FiniteTree.insertionProgram w) start)
  have hlim : Tendsto (fun D : ℕ => C^2/2*(Real.sqrt (D:ℝ))⁻¹+C*deletionError D h w) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,deletionError] using (hr.const_mul (C^2/2)).add (he.const_mul C)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_gt_atTop (0:ℕ)] with D hD
  simpa only [Real.norm_eq_abs] using edgeValue_error_bound D h hD w

theorem sideValue_marked (D h : ℕ) (w : List PointedTree.Gate) (hw : w.length≤h) :
    sideValue D h w=Real.sqrt (D:ℝ)/Real.sqrt ((D:ℝ)+1)*
      (⟪PointedTree.plusEmbedding (excitation D h w),insertion D h w⟫_ℂ).re := by
  have hm := congrArg Complex.re (marked_edge D h w w hw)
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Nat.cast_add,Nat.cast_one] at hm
  rw [hm]
  change Real.sqrt (D:ℝ)*_=Real.sqrt (D:ℝ)/Real.sqrt ((D:ℝ)+1)*(Real.sqrt ((D:ℝ)+1)*_)
  have hs : Real.sqrt ((D:ℝ)+1)≠0 := (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp
  rfl

theorem sideValue_limit (h : ℕ) (w : List PointedTree.Gate) (hw : w.length≤h) :
    Tendsto (fun D => sideValue D h w) atTop (𝓝 (PointedTree.ordinaryValue w)) := by
  have hr : Tendsto (fun D : ℕ => Real.sqrt (D:ℝ)/Real.sqrt ((D:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [inv_div,inv_one] using sqrt_ratio_limit.inv₀ (by norm_num : (1:ℝ)≠0)
  have hm := Complex.continuous_re.continuousAt.tendsto.comp (root_shift_insertion_limit h w w)
  have hv : (⟪PointedTree.rootShift h (PointedTree.ordinary w h).insertion,
      (PointedTree.ordinary w (h+1)).insertion⟫_ℂ).re=PointedTree.ordinaryValue w := by
    rw [←PointedTree.ordinary_insertion_empty w h hw]
    rw [←inner_conj_symm,Complex.conj_re]
    exact PointedTree.ordinary_energy_stable w h hw
  simpa only [Function.comp_apply,←sideValue_marked _ h w hw,one_mul,hv] using hr.mul hm

 

theorem edgeValue_limit (h : ℕ) (w : List PointedTree.Gate) (hw : w.length≤h) :
    Tendsto (fun D => edgeValue D h w) atTop (𝓝 (PointedTree.ordinaryValue w)) := by
  simpa only [sub_add_cancel,zero_add] using
    (edge_side_difference_limit h w).add (sideValue_limit h w hw)

end FiniteTree.FullRoot

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA
namespace Locality

 
theorem relevantEdges_qaoa_angles {n : ℕ} (E : Finset (Edge n)) (p : ℕ)
    (γ β γ' β' : Fin p → ℝ) (S : Finset (Fin n)) :
    relevantEdges E (qaoaWord p γ β) S=relevantEdges E (qaoaWord p γ' β') S := by
  induction p generalizing S with
  | zero => rfl
  | succ p ih =>
    simp only [qaoaWord,relevantEdges]
    rw [ih (fun i => γ i.castSucc) (fun i => β i.castSucc)
      (fun i => γ' i.castSucc) (fun i => β' i.castSucc)]

end Locality
namespace SiteHistories

lemma interaction_scale (p : ℕ) (c : ℝ) (γ : Fin p → ℝ) (a b : Bits p) :
    interaction p (fun i => c*γ i) a b=c*interaction p γ a b := by
  induction p with
  | zero => simp [interaction]
  | succ p ih => simp only [interaction,ih]; ring

lemma delta_scale (p : ℕ) (c : ℝ) (γ : Fin p → ℝ) (a b : Site p) :
    delta p (fun i => c*γ i) a b=c*delta p γ a b := by
  simp only [delta,interaction_scale]
  ring

lemma edgeKernel_scale (N m p : ℕ) (c : ℝ) (γ : Fin p → ℝ)
    (hscale : c^2/(m:ℝ)=(N:ℝ)⁻¹) (a b : Site p) :
    edgeKernel m p (fun i => c*γ i) a b=edgeKernel N p γ a b := by
  unfold edgeKernel
  rw [delta_scale]
  congr 1
  calc
    _ = -(delta p γ a b)^2/2*(c^2/(m:ℝ)) := by ring
    _ = _ := by rw [hscale]; ring

lemma rawGraphCoefficient_scale (N m p : ℕ) (c : ℝ) (γ β : Fin p → ℝ)
    (hscale : c^2/(m:ℝ)=(N:ℝ)⁻¹) (r : Edge m) (H : Finset (Edge m)) :
    rawGraphCoefficient m m p (fun i => c*γ i) β r H=
      (c:ℂ)*rawGraphCoefficient N m p γ β r H := by
  unfold rawGraphCoefficient FiniteHistory.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [delta_scale,edgeKernel_scale N m p c γ hscale,Complex.ofReal_mul]
  ring

 

theorem graphCoefficient_zero_of_not_cone (N m p : ℕ) (γ β : Fin p → ℝ)
    (hN : 0<N) (r : Edge m) (H : Finset (Edge m))
    (hc : ¬ H⊆Locality.relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)) :
    graphCoefficient N m p γ β r H=0 := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) r.1.2.isLt
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let c : ℝ := Real.sqrt ((m:ℝ)/(N:ℝ))
  have hcpos : 0<c := Real.sqrt_pos.2 (div_pos hmR hNR)
  have hscale : c^2/(m:ℝ)=(N:ℝ)⁻¹ := by
    dsimp [c]
    rw [Real.sq_sqrt (div_nonneg hmR.le hNR.le)]
    field_simp
  have hcone : ¬ H⊆Locality.relevantEdges (H∪{r})
      (qaoaWord p (fun i => c*γ i) β) (roots r) := by
    rw [Locality.relevantEdges_qaoa_angles (H∪{r}) p (fun i => c*γ i) β γ β]
    exact hc
  have hz := cluster_zero_of_not_cone p (fun i => c*γ i) β r H hcone
  rw [cluster_eq_inv_sqrt_mul_raw,
    rawGraphCoefficient_scale N m p c γ β hscale] at hz
  have hs : ((Real.sqrt (m:ℝ):ℂ))⁻¹≠0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hmR)))
  have hcz : (c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hcpos)
  have hr := (mul_eq_zero.mp hz).resolve_left hs
  have hr' := (mul_eq_zero.mp hr).resolve_left hcz
  rw [graphCoefficient_eq_pow_mul_raw,hr',mul_zero]

 

theorem graphCoefficientLimit_zero_of_not_cone (m p : ℕ) (γ β : Fin p → ℝ)
    (r : Edge m) (H : Finset (Edge m))
    (hc : ¬ H⊆Locality.relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)) :
    graphCoefficientLimit m p γ β r H=0 := by
  apply tendsto_nhds_unique (tendsto_graphCoefficient m p γ β r H)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (graphCoefficient_zero_of_not_cone N m p γ β (by omega) r H hc).symm

end SiteHistories
end SKQAOA

end

end OAI
