import Mathlib
import OAI.Probability.ParisiFinite.FlipStar

namespace OAI

/-! Child Moment Limit. -/

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
open scoped InnerProductSpace Topology
open Filter
namespace FiniteTree
open RootTensorCLT CoherentFock

 

theorem child_moment_limit (h : ℕ)
    (ih : ∀u w : List PointedTree.Gate,
      Tendsto (fun D => ⟪insertion D h u,insertion D h w⟫_ℂ) atTop
        (𝓝 ⟪(PointedTree.ordinary u h).insertion,(PointedTree.ordinary w h).insertion⟫_ℂ))
    (i j : Label) :
    Tendsto (fun D => ⟪vac D h,childGenerator D h i (childGenerator D h j (vac D h))⟫_ℂ)
      atTop (𝓝 (-⟪childDirection h i,childDirection h j⟫_ℂ)) := by
  have ht := (ih i.1 j.1).const_mul (-((i.2:ℂ)*(j.2:ℂ)))
  have he : -⟪childDirection h i,childDirection h j⟫_ℂ=
      -((i.2:ℂ)*(j.2:ℂ))*⟪(PointedTree.ordinary i.1 h).insertion,(PointedTree.ordinary j.1 h).insertion⟫_ℂ := by
    simp only [childDirection,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
    ring
  simpa only [child_second_moment,he] using ht

theorem program_limit_of_child (h : ℕ)
    (ih : ∀u w : List PointedTree.Gate,
      Tendsto (fun D => ⟪insertion D h u,insertion D h w⟫_ℂ) atTop
        (𝓝 ⟪(PointedTree.ordinary u h).insertion,(PointedTree.ordinary w h).insertion⟫_ℂ))
    (u w : List (Pulse Label)) :
    Tendsto (fun D =>
      ⟪run (tensorPulse D (childGenerator D h)) u
          (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h))),
        run (tensorPulse D (childGenerator D h)) w
          (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))⟫_ℂ)
      atTop (𝓝 ⟪run (W ∘ childDirection h) u (PointedTree.vac (h+1)),
        run (W ∘ childDirection h) w (PointedTree.vac (h+1))⟫_ℂ) := by
  exact root_circuit_Gram_local_limit (fun D => Index D h) (fun D => vac D h)
    (fun D => childGenerator D h) negateLabel negateLabel_involutive (childDirection h)
    (fun i => |i.2|) (fun i => abs_nonneg i.2) (fun D => norm_vac D h)
    (fun D i => le_of_eq ((ordinary D i.1 h).norm_generator i.2))
    (fun D i => childGenerator_neg D h i) (fun D i => childGenerator_star D h i)
    (fun i => childDirection_neg h i)
    (fun D i => (ordinary D i.1 h).generator_centered i.2)
    (child_moment_limit h ih) u w

 

theorem insertion_Gram_limit (h : ℕ) (u w : List PointedTree.Gate) :
    Tendsto (fun D => ⟪insertion D h u,insertion D h w⟫_ℂ) atTop
      (𝓝 ⟪(PointedTree.ordinary u h).insertion,(PointedTree.ordinary w h).insertion⟫_ℂ) := by
  induction h generalizing u w with
  | zero =>
    change Tendsto (fun D => ⟪insertion D 0 u,insertion D 0 w⟫_ℂ) atTop
      (𝓝 ⟪((PointedTree.ordinary u 0).insertion : PointedTree.Level 0),
        ((PointedTree.ordinary w 0).insertion : PointedTree.Level 0)⟫_ℂ)
    simp_rw [insertion_zero]
    exact tendsto_const_nhds
  | succ h ih =>
    have hg := program_limit_of_child h ih (insertionProgram u) (insertionProgram w)
    have hn (D : ℕ) : ⟪insertion D (h+1) u,insertion D (h+1) w⟫_ℂ=
        ⟪run (tensorPulse D (childGenerator D h)) (insertionProgram u)
            (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h))),
          run (tensorPulse D (childGenerator D h)) (insertionProgram w)
            (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))⟫_ℂ := by
      rw [←split_insertion,←split_insertion,LinearIsometryEquiv.inner_map_map]
    have hf : ⟪(PointedTree.ordinary u (h+1)).insertion,(PointedTree.ordinary w (h+1)).insertion⟫_ℂ=
        ⟪run (W ∘ childDirection h) (insertionProgram u) (PointedTree.vac (h+1)),
          run (W ∘ childDirection h) (insertionProgram w) (PointedTree.vac (h+1))⟫_ℂ := by
      change ⟪((PointedTree.ordinary u (h+1)).insertion : PointedTree.Level (h+1)),
        ((PointedTree.ordinary w (h+1)).insertion : PointedTree.Level (h+1))⟫_ℂ=_
      rw [limiting_insertion,limiting_insertion]
    simpa only [hn,hf] using hg

 

theorem program_Gram_limit (h : ℕ) (u w : List (Pulse Label)) :
    Tendsto (fun D =>
      ⟪run (tensorPulse D (childGenerator D h)) u
          (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h))),
        run (tensorPulse D (childGenerator D h)) w
          (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))⟫_ℂ)
      atTop (𝓝 ⟪run (W ∘ childDirection h) u (PointedTree.vac (h+1)),
        run (W ∘ childDirection h) w (PointedTree.vac (h+1))⟫_ℂ) :=
  program_limit_of_child h (insertion_Gram_limit h) u w

end FiniteTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter ContinuousLinearMap
namespace FiniteTree
open QuantumCLT RootTensorCLT CoherentFock

 

theorem marked_child_moment (D h : ℕ) (w : List PointedTree.Gate) (i : Label) :
    ⟪vac D h,(ordinary D w h).observable (childGenerator D h i (vac D h))⟫_ℂ=
      (Complex.I*(i.2:ℂ))*⟪insertion D h w,insertion D h i.1⟫_ℂ := by
  simp only [childGenerator,Even.generator,smul_apply,map_smul,inner_smul_right]
  congr 1
  rw [←ContinuousLinearMap.adjoint_inner_left,←ContinuousLinearMap.star_eq_adjoint,
    Even.observable_star]
  rfl

theorem marked_child_limit (h : ℕ) (w : List PointedTree.Gate) (i : Label) :
    Tendsto (fun D => ⟪vac D h,(ordinary D w h).observable
      (childGenerator D h i (vac D h))⟫_ℂ) atTop
      (𝓝 (Complex.I*⟪(PointedTree.ordinary w h).insertion,childDirection h i⟫_ℂ)) := by
  have ht := (insertion_Gram_limit h w i.1).const_mul (Complex.I*(i.2:ℂ))
  simpa only [marked_child_moment,childDirection,inner_smul_right,mul_assoc] using ht

theorem marked_child_sum_limit (h : ℕ) (w : List PointedTree.Gate) (l : List Label) :
    Tendsto (fun D => ⟪vac D h,(ordinary D w h).observable
      ((l.map (childGenerator D h)).sum (vac D h))⟫_ℂ) atTop
      (𝓝 (Complex.I*⟪(PointedTree.ordinary w h).insertion,(l.map (childDirection h)).sum⟫_ℂ)) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,add_apply,map_add,inner_add_right,mul_add]
    exact (marked_child_limit h w i).add ih

theorem child_sum_centered (D h : ℕ) (l : List Label) :
    ⟪vac D h,(l.map (childGenerator D h)).sum (vac D h)⟫_ℂ=0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,add_apply,inner_add_right,ih,add_zero]
    exact (ordinary D i.1 h).generator_centered i.2

theorem child_second_limit (h : ℕ) (l : List Label) :
    Tendsto (fun D => ⟪vac D h,second (l.map (childGenerator D h)) (vac D h)⟫_ℂ)
      atTop (𝓝 (secondCoefficient (fun i j => -⟪childDirection h i,childDirection h j⟫_ℂ) l)) := by
  have he (D : ℕ) : ⟪vac D h,second (l.map (childGenerator D h)) (vac D h)⟫_ℂ=
      secondCoefficient (fun i j => ⟪vac D h,childGenerator D h i (childGenerator D h j (vac D h))⟫_ℂ) l :=
    second_matrixElement l (childGenerator D h) (vacuumFunctional (vac D h))
  simp_rw [he]
  exact secondCoefficient_tendsto l _ _ (fun i hi j hj =>
    child_moment_limit h (insertion_Gram_limit h) i j)

 

theorem marked_tensor_limit (h : ℕ) (w : List PointedTree.Gate) (l : List Label) :
    Tendsto (fun D => ⟪FiniteTensor.power D (vac D h),FiniteTensor.normalizedInsertion D
      (generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹)
      ((ordinary D w h).observable*generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹)
      (FiniteTensor.power D (vac D h))⟫_ℂ) atTop
      (𝓝 ((Complex.I*⟪(PointedTree.ordinary w h).insertion,(l.map (childDirection h)).sum⟫_ℂ)*
        Complex.exp (secondCoefficient (fun i j => -⟪childDirection h i,childDirection h j⟫_ℂ) l))) := by
  classical
  let L : ℝ := ∑i∈l.toFinset, |i.2|
  have hL : 0≤L := Finset.sum_nonneg (fun i hi => abs_nonneg i.2)
  apply FiniteTensor.moving_tensor_insertion_limit (fun D => Index D h) (fun D => vac D h)
    l (fun D => childGenerator D h) (fun D => (ordinary D w h).observable) L 1 hL (by norm_num)
    (fun D => norm_vac D h)
  · intro D i hi
    exact ((ordinary D i.1 h).norm_generator i.2).le.trans
      (Finset.single_le_sum (fun j hj => abs_nonneg j.2) (List.mem_toFinset.mpr hi))
  · intro D
    exact (ordinary D w h).norm_observable.le
  · exact fun D => child_sum_centered D h l
  · exact fun D => (ordinary D w h).observable_centered
  · exact child_second_limit h l
  · exact marked_child_sum_limit h w l

end FiniteTree

 

open scoped InnerProductSpace Topology
open ContinuousLinearMap
namespace QuantumCLT
open CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_creation_coherent (a e : E) :
    ⟪creationVacuum a,coherent e⟫_ℂ=
      Complex.I*(Real.exp (-‖e‖^2/2):ℂ)*⟪a,e⟫_ℂ := by
  rw [←inner_conj_symm,creationVacuum,inner_smul_right,inner_coherent_oneParticle]
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal,
    inner_conj_symm]
  ring

 

theorem inner_creation_weylProduct (a : E) (ds : List E) :
    ⟪creationVacuum a,weylProduct ds (coherent (0:E))⟫_ℂ=
      (Complex.I*⟪a,ds.sum⟫_ℂ)*
        Complex.exp (secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) ds) := by
  rw [weylProduct_coherent_zero,inner_smul_right,inner_creation_coherent]
  have he (q : ℂ) : Complex.exp (q+Complex.ofReal (‖ds.sum‖^2/2))*
      (Real.exp (-‖ds.sum‖^2/2):ℂ)=Complex.exp q := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = Complex.I*⟪a,ds.sum⟫_ℂ*(Complex.exp (_+Complex.ofReal (‖ds.sum‖^2/2))*
          (Real.exp (-‖ds.sum‖^2/2):ℂ)) := by ring
    _ = _ := by rw [he]

end QuantumCLT

namespace FiniteTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 

theorem inner_excitation_power (D : ℕ) (Ω : EuclideanSpace ℂ ι)
    (S G : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hS : star S=S) :
    ⟪normalizedInsertion D 1 S (power D Ω),power D (G Ω)⟫_ℂ=
      ⟪power D Ω,normalizedInsertion D G (S*G) (power D Ω)⟫_ℂ := by
  rw [←inner_conj_symm (normalizedInsertion D 1 S (power D Ω)) (power D (G Ω)),
    inner_normalizedInsertion,inner_normalizedInsertion]
  simp only [mul_apply_eq_comp,map_mul,map_pow,Complex.conj_ofReal,
    inner_conj_symm]
  have hs : ⟪S Ω,G Ω⟫_ℂ=⟪Ω,S (G Ω)⟫_ℂ := by
    rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.star_eq_adjoint,hS]
  rw [hs]
  rfl

end FiniteTensor

 

open scoped InnerProductSpace Topology
open Filter ContinuousLinearMap
namespace TensorPackets
open SpinOperators
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_plus_term (z : H) (s : List κ → H) (t : Term κ) :
    ⟪PointedTree.plusEmbedding z,term s t⟫_ℂ=
      (((Real.sqrt 2)⁻¹:ℝ):ℂ)*t.coeff*⟪z,s t.history⟫_ℂ := by
  obtain ⟨j,c,w⟩ := t
  simp only [PiLp.inner_apply,Fin.sum_univ_two,PointedTree.plusEmbedding_apply]
  fin_cases j <;> simp [term_apply,inner_smul_left,inner_smul_right,mul_assoc,mul_left_comm]

 

theorem marked_limit
    (Hn : ℕ → Type*) [∀n,NormedAddCommGroup (Hn n)] [∀n,InnerProductSpace ℂ (Hn n)]
    (sn : ∀n,List κ → Hn n) (s : List κ → H) (zn : ∀n,Hn n) (z : H)
    (hz : ∀w,Tendsto (fun n => ⟪zn n,sn n w⟫_ℂ) atTop (𝓝 ⟪z,s w⟫_ℂ))
    (ts : List (Term κ)) :
    Tendsto (fun n => ⟪PointedTree.plusEmbedding (zn n),packet (sn n) ts⟫_ℂ)
      atTop (𝓝 ⟪PointedTree.plusEmbedding z,packet s ts⟫_ℂ) := by
  induction ts with
  | nil => simp only [packet_nil,inner_zero_right]; exact tendsto_const_nhds
  | cons t ts ih =>
    simp only [packet_cons,inner_add_right,inner_plus_term]
    exact ((hz t.history).const_mul _).add ih
end TensorPackets

namespace FiniteTree
open QuantumCLT RootTensorCLT CoherentFock TensorPackets

 

def excitation (D h : ℕ) (w : List PointedTree.Gate) : Tail D (h+1) :=
  FiniteTensor.normalizedInsertion D 1 (ordinary D w h).observable
    (FiniteTensor.power D (vac D h))

theorem excitation_tensor_limit (h : ℕ) (w : List PointedTree.Gate) (l : List Label) :
    Tendsto (fun D => ⟪excitation D h w,tensorState D (vac D h) (childGenerator D h) l⟫_ℂ)
      atTop (𝓝 ⟪creationVacuum (PointedTree.ordinary w h).insertion,fockState (childDirection h) l⟫_ℂ) := by
  have hn (D : ℕ) : ⟪excitation D h w,tensorState D (vac D h) (childGenerator D h) l⟫_ℂ=
      ⟪FiniteTensor.power D (vac D h),FiniteTensor.normalizedInsertion D
        (generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹)
        ((ordinary D w h).observable*generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹)
        (FiniteTensor.power D (vac D h))⟫_ℂ :=
    FiniteTensor.inner_excitation_power D (vac D h) _ _ (ordinary D w h).observable_star
  simp only [hn,fockState,inner_creation_weylProduct,secondCoefficient_map]
  exact marked_tensor_limit h w l

theorem excitation_program_limit (h : ℕ) (w : List PointedTree.Gate) (p : List (Pulse Label)) :
    Tendsto (fun D => ⟪PointedTree.plusEmbedding (excitation D h w),
      run (tensorPulse D (childGenerator D h)) p (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))⟫_ℂ)
      atTop (𝓝 ⟪PointedTree.plusEmbedding (creationVacuum (PointedTree.ordinary w h).insertion),
        run (W ∘ childDirection h) p (PointedTree.vac (h+1))⟫_ℂ) := by
  have ht := TensorPackets.marked_limit (fun D => Tail D (h+1))
    (fun D => tensorState D (vac D h) (childGenerator D h)) (fockState (childDirection h))
    (fun D => excitation D h w) (creationVacuum (PointedTree.ordinary w h).insertion)
    (excitation_tensor_limit h w) (compile p start)
  have hn (D : ℕ) : run (tensorPulse D (childGenerator D h)) p
      (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))=
        packet (tensorState D (vac D h) (childGenerator D h)) (compile p start) := by
    have he : tensorState D (vac D h) (childGenerator D h) []=FiniteTensor.power D (vac D h) := by
      simp [tensorState,generators]
    rw [←he,←start_packet,run_packet _ _ (tensor_step D (vac D h) (childGenerator D h))]
  have hf : run (W ∘ childDirection h) p (PointedTree.vac (h+1))=
      packet (fockState (childDirection h)) (compile p start) := by
    change run (W ∘ childDirection h) p (PointedTree.plusEmbedding (fockState (childDirection h) []))=_
    rw [←start_packet]
    exact run_packet _ _ (fock_step _) p start
  simpa only [hn,hf] using ht

 
def rootExcitation (D h : ℕ) (w : List PointedTree.Gate) : Space D (h+1) :=
  (split D (h+1)).symm (PointedTree.plusEmbedding (excitation D h w))

 

theorem root_shift_insertion_limit (h : ℕ) (w u : List PointedTree.Gate) :
    Tendsto (fun D => ⟪rootExcitation D h w,insertion D (h+1) u⟫_ℂ) atTop
      (𝓝 ⟪PointedTree.rootShift h (PointedTree.ordinary w h).insertion,
        (PointedTree.ordinary u (h+1)).insertion⟫_ℂ) := by
  have ht := excitation_program_limit h w (insertionProgram u)
  have hn (D : ℕ) : ⟪rootExcitation D h w,insertion D (h+1) u⟫_ℂ=
      ⟪PointedTree.plusEmbedding (excitation D h w),
        run (tensorPulse D (childGenerator D h)) (insertionProgram u)
          (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))⟫_ℂ := by
    rw [←(split D (h+1)).inner_map_map,rootExcitation,LinearIsometryEquiv.apply_symm_apply,split_insertion]
  have hf : ⟪PointedTree.rootShift h (PointedTree.ordinary w h).insertion,
      (PointedTree.ordinary u (h+1)).insertion⟫_ℂ=
      ⟪PointedTree.plusEmbedding (creationVacuum (PointedTree.ordinary w h).insertion),
        run (W ∘ childDirection h) (insertionProgram u) (PointedTree.vac (h+1))⟫_ℂ := by
    change ⟪(PointedTree.rootShift h (PointedTree.ordinary w h).insertion : PointedTree.Level (h+1)),
      ((PointedTree.ordinary u (h+1)).insertion : PointedTree.Level (h+1))⟫_ℂ=_
    rw [PointedTree.rootShift_coe,limiting_insertion]
  simpa only [hn,hf] using ht

end FiniteTree

 

open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
namespace FiniteTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem norm_mixedPower (D : ℕ) (v : Fin D → EuclideanSpace ℂ ι) :
    ‖mixedPower D v‖=∏i,‖v i‖ := by
  have hh := inner_mixedPower D v v
  simp only [inner_self_eq_norm_sq_to_K] at hh
  have hs : ‖mixedPower D v‖^2=(∏i,‖v i‖)^2 := by
    norm_cast at hh
    simpa only [Finset.prod_pow] using hh
  nlinarith [norm_nonneg (mixedPower D v),Finset.prod_nonneg (fun i (_ : i∈Finset.univ) => norm_nonneg (v i))]

 

def vacuumComplement (Ω : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  1-rankOne ℂ Ω Ω

omit [DecidableEq ι] [Nonempty ι] in
@[simp] theorem vacuumComplement_vac (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1) :
    vacuumComplement Ω Ω=0 := by
  simp only [vacuumComplement,sub_apply,one_apply_eq_self,rankOne_apply,
    inner_self_eq_norm_sq_to_K,hΩ]
  norm_num

omit [DecidableEq ι] in
theorem vacuumComplement_norm (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1) :
    ‖vacuumComplement Ω‖≤2 := by
  calc
    _ ≤ ‖(1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖+‖rankOne ℂ Ω Ω‖ := norm_sub_le _ _
    _ ≤ 1+1 := by simp [hΩ]
    _ = _ := by norm_num

 
def excitedSlot (D : ℕ) (Ω : EuclideanSpace ℂ ι) (j : Fin D) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  mixedOperator D (fun i => if i=j then vacuumComplement Ω else 1)

omit [Nonempty ι] in
theorem excitedSlot_power_norm (D : ℕ) (Ω v : EuclideanSpace ℂ ι) (hv : ‖v‖=1) (j : Fin D) :
    ‖excitedSlot D Ω j (power D v)‖=‖vacuumComplement Ω v‖ := by
  change ‖mixedOperator D _ (mixedPower D (fun _ => v))‖=_
  rw [mixedOperator_apply,norm_mixedPower]
  have he (i : Fin D) : ‖(if i=j then vacuumComplement Ω else 1) v‖=
      if i=j then ‖vacuumComplement Ω v‖ else 1 := by
    split_ifs <;> simp_all only [one_apply_eq_self]
  simp_rw [he]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]

theorem excitedSlot_power_bound (D : ℕ) (Ω v : EuclideanSpace ℂ ι)
    (hΩ : ‖Ω‖=1) (hv : ‖v‖=1) (j : Fin D) :
    ‖excitedSlot D Ω j (power D v)‖≤2*‖v-Ω‖ := by
  rw [excitedSlot_power_norm D Ω v hv j]
  have he : vacuumComplement Ω v=vacuumComplement Ω (v-Ω) := by
    rw [map_sub,vacuumComplement_vac Ω hΩ,sub_zero]
  rw [he]
  exact ((vacuumComplement Ω).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (vacuumComplement_norm Ω hΩ) (norm_nonneg _))

end FiniteTensor

 

open scoped InnerProductSpace Topology BigOperators
namespace QuantumCLT
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]

 

omit [NormOneClass A] [CompleteSpace A] in
theorem JetBound.first_bound {C : ℝ} (hC : 0≤C)
    {f : ℝ → A} {a b : A} (hf : JetBound C f a b) {r : ℝ} (hr : |r|≤1) :
    ‖f r-1‖≤3*C*|r| := by
  have hs : |r|^2≤|r| := by nlinarith [abs_nonneg r]
  have hc : |r|^3≤|r| := by
    calc
      |r|^3=|r|^2*|r| := by ring
      _ ≤ |r| * |r| := mul_le_mul_of_nonneg_right hs (abs_nonneg r)
      _ ≤ |r| := by nlinarith [abs_nonneg r]
  calc
    _ ≤ ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖+
        ‖(r:ℂ) • a‖+‖((r:ℂ)^2) • b‖ := by
      have he : f r-1=(f r-1-(r:ℂ) • a-((r:ℂ)^2) • b)+(r:ℂ) • a+((r:ℂ)^2) • b := by abel
      conv_lhs => rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C*|r|^3+|r| * C+|r|^2*C := by
      simp only [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr
      · exact hf.2.2 r hr
      · exact hf.1
      · exact hf.2.1
    _ ≤ 3*C*|r| := by nlinarith [mul_le_mul_of_nonneg_left hs hC,mul_le_mul_of_nonneg_left hc hC]

end QuantumCLT

namespace FiniteTree
open QuantumCLT RootTensorCLT

def wordBound (l : List Label) : ℝ :=
  orderedBound (l.map (fun i => |i.2|)).sum l.length

theorem wordBound_nonneg (l : List Label) : 0≤wordBound l :=
  orderedBound_nonneg (List.sum_nonneg (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)) _

theorem child_word_unitary (D h : ℕ) (l : List Label) (r : ℝ) :
    generators (l.map (childGenerator D h)) r ∈ unitary _ := by
  induction l with
  | nil => exact (unitary _).one_mem
  | cons i l ih =>
    change NormedSpace.exp ((r:ℂ) • childGenerator D h i)*
      generators (l.map (childGenerator D h)) r ∈ unitary _
    apply (unitary _).mul_mem _ ih
    change NormedSpace.exp ((r:ℂ) • (ordinary D i.1 h).generator i.2) ∈ unitary _
    rw [generator_scaled]
    exact (ordinary D i.1 h).exponential_unitary (r*i.2)

 

theorem child_word_vacuum_bound (D h : ℕ) (hD : 0<D) (l : List Label) :
    ‖generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹ (vac D h)-vac D h‖≤
      3*wordBound l*(Real.sqrt (D:ℝ))⁻¹ := by
  let L := (l.map (fun i => |i.2|)).sum
  have hL : 0≤L := List.sum_nonneg (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  have hx : ∀X ∈ l.map (childGenerator D h),‖X‖≤L := by
    intro X hX
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hX
    rw [childGenerator,Even.norm_generator]
    have hall : ∀j∈l.map (fun i => |i.2|),0≤j := by
      intro j hj; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj; exact abs_nonneg _
    exact List.single_le_sum hall _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  let : CompleteSpace (Space D h) := PiLp.completeSpace 2 (fun _ : Index D h => ℂ)
  let : CompleteSpace (Space D h →L[ℂ] Space D h) := ContinuousLinearMap.instCompleteSpace
  have hj := generators_jetBound (l.map (childGenerator D h)) hL hx
  have hb := hj.first_bound (orderedBound_nonneg hL _) (sqrt_inverse_bound D hD)
  have ha : |(Real.sqrt (D:ℝ))⁻¹|=(Real.sqrt (D:ℝ))⁻¹ := abs_of_nonneg (by positivity)
  calc
    _ = ‖(generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹-1) (vac D h)‖ := rfl
    _ ≤ ‖generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹-1‖*‖vac D h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 3*wordBound l*(Real.sqrt (D:ℝ))⁻¹ := by
      rw [norm_vac,mul_one]
      simpa only [List.length_map,ha,wordBound,L] using hb

 theorem tensor_word_excited_bound (D h : ℕ) (hD : 0<D) (l : List Label) (j : Fin D) :
    ‖FiniteTensor.excitedSlot D (vac D h) j (tensorState D (vac D h) (childGenerator D h) l)‖≤
      6*wordBound l*(Real.sqrt (D:ℝ))⁻¹ := by
  unfold tensorState
  have hu := ContinuousLinearMap.norm_map_of_mem_unitary
    (child_word_unitary D h l (Real.sqrt (D:ℝ))⁻¹) (vac D h)
  have hn : ‖generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹ (vac D h)‖=1 := by simpa only [norm_vac] using hu
  calc
    _ ≤ 2*‖generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹ (vac D h)-vac D h‖ :=
      FiniteTensor.excitedSlot_power_bound _ _ _ (norm_vac _ _) hn _
    _ ≤ 2*(3*wordBound l*(Real.sqrt (D:ℝ))⁻¹) := mul_le_mul_of_nonneg_left (child_word_vacuum_bound D h hD l) (by norm_num)
    _ = _ := by ring

end FiniteTree

 

open scoped InnerProductSpace BigOperators
namespace TensorPackets
open SpinOperators
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem norm_term (s : List κ → H) (t : Term κ) :
    ‖term s t‖=‖t.coeff‖*‖s t.history‖ := by
  simp only [term,norm_smul,PiLp.norm_single]

theorem diagonal_constant_term (s : List κ → H) (A : H →L[ℂ] H) (t : Term κ) :
    diagonal (fun _ => A) (term s t)=term (A ∘ s) t := by
  classical
  ext i
  simp only [diagonal_apply,term_apply,Function.comp_apply]
  split_ifs
  · exact map_smul A _ _
  · exact map_zero A

theorem diagonal_constant_packet (s : List κ → H) (A : H →L[ℂ] H)
    (ts : List (Term κ)) :
    diagonal (fun _ => A) (packet s ts)=packet (A ∘ s) ts := by
  induction ts with
  | nil => exact map_zero _
  | cons t ts ih => simp only [packet_cons,map_add,diagonal_constant_term,ih]

 

theorem packet_bound (s : List κ → H) (b : List κ → ℝ) (_ : ∀l,0≤b l)
    (r : ℝ) (_ : 0≤r) (hs : ∀l,‖s l‖≤b l*r) (ts : List (Term κ)) :
    ‖packet s ts‖≤(ts.map (fun t => ‖t.coeff‖*b t.history)).sum*r := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [packet_cons,List.map_cons,List.sum_cons,add_mul]
    exact (norm_add_le _ _).trans (add_le_add
      (by rw [norm_term]; exact (mul_le_mul_of_nonneg_left (hs t.history) (norm_nonneg _)).trans_eq (by ring)) ih)

end TensorPackets

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree
open RootTensorCLT TensorPackets SpinOperators

 
def packetOccupationBound (ts : List (Term Label)) : ℝ :=
  (ts.map (fun t => ‖t.coeff‖*(6*wordBound t.history))).sum

theorem packetOccupationBound_nonneg (ts : List (Term Label)) :
    0≤packetOccupationBound ts := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (wordBound_nonneg _))

theorem packet_excited_bound (D h : ℕ) (hD : 0<D) (ts : List (Term Label)) (j : Fin D) :
    ‖TensorPackets.diagonal (fun _ => FiniteTensor.excitedSlot D (vac D h) j)
      (packet (tensorState D (vac D h) (childGenerator D h)) ts)‖≤
        packetOccupationBound ts*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [diagonal_constant_packet]
  exact packet_bound _ (fun l => 6*wordBound l) (fun l => mul_nonneg (by norm_num) (wordBound_nonneg l))
    _ (by positivity) (fun l => by simpa only [Function.comp_apply,mul_assoc] using tensor_word_excited_bound D h hD l j) _

 

def rootSlot (D h : ℕ) (j : Fin D) : Space D (h+1) →L[ℂ] Space D (h+1) :=
  (split D (h+1)).symm.conjStarAlgEquiv
    (TensorPackets.diagonal (fun _ => FiniteTensor.excitedSlot D (vac D h) j))

@[simp] theorem split_rootSlot (D h : ℕ) (j : Fin D) (x : Space D (h+1)) :
    split D (h+1) (rootSlot D h j x)=
      TensorPackets.diagonal (fun _ => FiniteTensor.excitedSlot D (vac D h) j) (split D (h+1) x) := by
  simp only [rootSlot,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm,LinearIsometryEquiv.apply_symm_apply]

 

def topOccupation (D h : ℕ) (x : Space D (h+1)) : ℝ :=
  ∑j : Fin D, ‖rootSlot D h j x‖^2

theorem topOccupation_nonneg (D h : ℕ) (x : Space D (h+1)) :
    0≤topOccupation D h x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem insertion_packet (D h : ℕ) (w : List PointedTree.Gate) :
    split D (h+1) (insertion D (h+1) w)=
      packet (tensorState D (vac D h) (childGenerator D h)) (compile (insertionProgram w) start) := by
  rw [split_insertion]
  have he : tensorState D (vac D h) (childGenerator D h) []=FiniteTensor.power D (vac D h) := by
    simp only [tensorState,QuantumCLT.generators,List.map_nil,List.prod_nil,one_apply_eq_self]
  rw [←he,←start_packet]
  exact run_packet _ _ (tensor_step D (vac D h) (childGenerator D h)) _ _

theorem insertion_slot_bound (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) (j : Fin D) :
    ‖rootSlot D h j (insertion D (h+1) w)‖≤
      packetOccupationBound (compile (insertionProgram w) start)*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [←(split D (h+1)).norm_map,split_rootSlot,insertion_packet]
  exact packet_excited_bound D h hD _ j

 

theorem insertion_occupation_bound (D h : ℕ) (w : List PointedTree.Gate) :
    topOccupation D h (insertion D (h+1) w)≤
      (packetOccupationBound (compile (insertionProgram w) start))^2 := by
  by_cases hD : D=0
  · subst D
    simp only [topOccupation,Finset.univ_eq_empty,Finset.sum_empty]
    exact sq_nonneg _
  have hDp : 0<D := Nat.pos_of_ne_zero hD
  let C := packetOccupationBound (compile (insertionProgram w) start)
  have hC : 0≤C := packetOccupationBound_nonneg _
  calc
    _ ≤ ∑j : Fin D, (C*(Real.sqrt (D:ℝ))⁻¹)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply pow_le_pow_left₀ (norm_nonneg _) (insertion_slot_bound D h hDp w j)
    _ = (D:ℝ)*(C*(Real.sqrt (D:ℝ))⁻¹)^2 := by simp
    _ = C^2 := by
      rw [mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg D)]
      have hn : (D:ℝ)≠0 := by exact_mod_cast hD
      field_simp

end FiniteTree

end

end OAI
