import Mathlib
import OAI.Probability.ParisiFinite.ChildMomentLimit

namespace OAI

/-! Mixed Matrix One. -/

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
open ContinuousLinearMap InnerProductSpace
namespace FiniteTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
 theorem mixedMatrix_one (D : ℕ) : mixedMatrix D (fun _ => (1 : Matrix ι ι ℂ))=1 := by
  ext σ τ
  simp only [mixedMatrix,Matrix.one_apply]
  by_cases h : σ=τ
  · subst τ; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq ι] in
 theorem mixedMatrix_mul (D : ℕ) (A B : Fin D → Matrix ι ι ℂ) :
    mixedMatrix D (fun i => A i*B i)=mixedMatrix D A*mixedMatrix D B := by
  ext σ τ
  simp only [mixedMatrix,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [Fintype ι] [DecidableEq ι] in
 theorem mixedMatrix_star (D : ℕ) (A : Fin D → Matrix ι ι ℂ) :
    mixedMatrix D (fun i => star (A i))=star (mixedMatrix D A) := by
  ext σ τ
  simp only [mixedMatrix,Matrix.star_apply,star_prod]

 theorem mixedOperator_one (D : ℕ) :
    mixedOperator D (fun _ => (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))=1 := by
  simp only [mixedOperator,map_one,mixedMatrix_one]

 theorem mixedOperator_mul (D : ℕ)
    (A B : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    mixedOperator D (fun i => A i*B i)=mixedOperator D A*mixedOperator D B := by
  simp only [mixedOperator,map_mul,mixedMatrix_mul]

 theorem mixedOperator_star (D : ℕ)
    (A : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    mixedOperator D (fun i => star (A i))=star (mixedOperator D A) := by
  unfold mixedOperator
  have hi (i : Fin D) : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm (star (A i))=
      star ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm (A i)) :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm.map_star' _
  simp_rw [hi]
  rw [mixedMatrix_star]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D → ι)).map_star' _

 theorem mixedOperator_projection (D : ℕ)
    (A : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (hA : ∀i,IsStarProjection (A i)) : IsStarProjection (mixedOperator D A) := by
  constructor
  · change mixedOperator D A*mixedOperator D A=mixedOperator D A
    rw [←mixedOperator_mul]
    congr 1
    funext i
    exact (hA i).isIdempotentElem
  · change star (mixedOperator D A)=mixedOperator D A
    rw [←mixedOperator_star]
    congr 1
    funext i
    exact (hA i).isSelfAdjoint

omit [DecidableEq ι] in
 theorem vacuumComplement_projection [Nonempty ι] (Ω : EuclideanSpace ℂ ι) (hΩ : ‖Ω‖=1) :
    IsStarProjection (vacuumComplement Ω) := (isStarProjection_rankOne_self hΩ).one_sub

 theorem excitedSlot_projection [Nonempty ι] (D : ℕ) (Ω : EuclideanSpace ℂ ι)
    (hΩ : ‖Ω‖=1) (j : Fin D) : IsStarProjection (excitedSlot D Ω j) := by
  apply mixedOperator_projection
  intro i
  split_ifs
  · exact vacuumComplement_projection Ω hΩ
  · exact IsStarProjection.one _

 

theorem excitedSlot_expectation [Nonempty ι] (D : ℕ) (Ω : EuclideanSpace ℂ ι)
    (hΩ : ‖Ω‖=1) (j : Fin D) (x : EuclideanSpace ℂ (Fin D → ι)) :
    ⟪x,excitedSlot D Ω j x⟫_ℂ=(‖excitedSlot D Ω j x‖^2:ℝ) := by
  have h := excitedSlot_projection D Ω hΩ j
  have he : ⟪excitedSlot D Ω j x,excitedSlot D Ω j x⟫_ℂ=⟪x,excitedSlot D Ω j x⟫_ℂ := by
    rw [←ContinuousLinearMap.adjoint_inner_right]
    rw [←ContinuousLinearMap.star_eq_adjoint,h.isSelfAdjoint]
    change ⟪x,(excitedSlot D Ω j*excitedSlot D Ω j) x⟫_ℂ=_
    rw [h.isIdempotentElem]
  rw [←he,inner_self_eq_norm_sq_to_K]
  norm_cast

end FiniteTensor

 

open scoped InnerProductSpace BigOperators
namespace TensorPackets
open SpinOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem diagonal_projection (A : Fin 2 → H →L[ℂ] H) (hA : ∀i,IsStarProjection (A i)) :
    IsStarProjection (diagonal A) := by
  constructor
  · change diagonal A*diagonal A=diagonal A
    rw [←diagonal_mul]
    congr 1
    funext i
    exact (hA i).isIdempotentElem
  · change star (diagonal A)=diagonal A
    rw [←diagonal_star]
    congr 1
    funext i
    exact (hA i).isSelfAdjoint

end TensorPackets

namespace FiniteTree

theorem rootSlot_projection (D h : ℕ) (j : Fin D) : IsStarProjection (rootSlot D h j) := by
  have hp := TensorPackets.diagonal_projection
    (fun _ : Fin 2 => FiniteTensor.excitedSlot D (vac D h) j)
    (fun _ => FiniteTensor.excitedSlot_projection D (vac D h) (norm_vac D h) j)
  let f := (split D (h+1)).symm.conjStarAlgEquiv
  change IsStarProjection (f _)
  constructor
  · change f _*f _=f _
    rw [←map_mul,hp.isIdempotentElem]
  · change star (f _)=f _
    exact (f.map_star' _).symm.trans (congrArg f hp.isSelfAdjoint)

 
def numberOperator (D h : ℕ) : Space D (h+1) →L[ℂ] Space D (h+1) :=
  ∑j : Fin D, rootSlot D h j

theorem rootSlot_expectation (D h : ℕ) (j : Fin D) (x : Space D (h+1)) :
    ⟪x,rootSlot D h j x⟫_ℂ=(‖rootSlot D h j x‖^2:ℝ) := by
  have hp := rootSlot_projection D h j
  have he : ⟪rootSlot D h j x,rootSlot D h j x⟫_ℂ=⟪x,rootSlot D h j x⟫_ℂ := by
    rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint]
    change ⟪x,(rootSlot D h j*rootSlot D h j) x⟫_ℂ=_
    rw [hp.isIdempotentElem]
  rw [←he,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem numberOperator_expectation (D h : ℕ) (x : Space D (h+1)) :
    ⟪x,numberOperator D h x⟫_ℂ=(topOccupation D h x:ℂ) := by
  simp only [numberOperator,topOccupation,_root_.sum_apply,inner_sum,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact rootSlot_expectation D h j x

 

theorem insertion_number_bound (D h : ℕ) (w : List PointedTree.Gate) :
    (⟪insertion D (h+1) w,numberOperator D h (insertion D (h+1) w)⟫_ℂ).re≤
      packetOccupationBound (RootTensorCLT.compile (insertionProgram w) RootTensorCLT.start)^2 := by
  rw [numberOperator_expectation,Complex.ofReal_re]
  exact insertion_occupation_bound D h w

end FiniteTree

 

open scoped InnerProductSpace Topology
open Filter
namespace RootTensorCLT
open SpinOperators
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def constantProgram (l : List κ) : List (Pulse κ) := l.map (fun i => .control (fun _ => i))

theorem constant_run (s : List κ → H) (K : κ → H →L[ℂ] H)
    (hs : ∀i l,K i (s l)=s (i::l)) (l : List κ) :
    run K (constantProgram l) (PointedTree.plusEmbedding (s []))=PointedTree.plusEmbedding (s l) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change TensorPackets.diagonal (fun _ => K i) (run K (constantProgram l) (PointedTree.plusEmbedding (s [])))=_
    rw [ih]
    ext j
    simp only [TensorPackets.diagonal_apply,PointedTree.plusEmbedding_apply,map_smul,hs]

end RootTensorCLT

namespace FiniteTree
open QuantumCLT RootTensorCLT CoherentFock

 

theorem tensor_Gram_limit (h : ℕ) (u w : List Label) :
    Tendsto (fun D => ⟪tensorState D (vac D h) (childGenerator D h) u,
      tensorState D (vac D h) (childGenerator D h) w⟫_ℂ) atTop
      (𝓝 ⟪fockState (childDirection h) u,fockState (childDirection h) w⟫_ℂ) := by
  have ht := program_Gram_limit h (constantProgram u) (constantProgram w)
  have hn (D : ℕ) (l : List Label) :
      run (tensorPulse D (childGenerator D h)) (constantProgram l)
        (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h)))=
        PointedTree.plusEmbedding (tensorState D (vac D h) (childGenerator D h) l) := by
    have he : tensorState D (vac D h) (childGenerator D h) []=FiniteTensor.power D (vac D h) := by
      simp [tensorState,generators]
    rw [←he]
    exact constant_run _ _ (tensor_step D (vac D h) (childGenerator D h)) l
  have hf (l : List Label) : run (W ∘ childDirection h) (constantProgram l) (PointedTree.vac (h+1))=
      PointedTree.plusEmbedding (fockState (childDirection h) l) :=
    constant_run _ _ (fock_step (childDirection h)) l
  simpa only [hn,hf,LinearIsometry.inner_map_map] using ht

def childState (D h : ℕ) (l : List Label) : Space D h :=
  generators (l.map (childGenerator D h)) (Real.sqrt (D:ℝ))⁻¹ (vac D h)

@[simp] theorem norm_childState (D h : ℕ) (l : List Label) : ‖childState D h l‖=1 := by
  exact (ContinuousLinearMap.norm_map_of_mem_unitary
    (child_word_unitary D h l (Real.sqrt (D:ℝ))⁻¹) (vac D h)).trans (norm_vac D h)

theorem child_Gram_bound (D h : ℕ) (hD : 0<D) (u w : List Label) :
    ‖⟪childState D h u,childState D h w⟫_ℂ-1‖≤
      3*(wordBound u+wordBound w)*(Real.sqrt (D:ℝ))⁻¹ := by
  have he : ⟪childState D h u,childState D h w⟫_ℂ-1=
      ⟪childState D h u-vac D h,childState D h w⟫_ℂ+
      ⟪vac D h,childState D h w-vac D h⟫_ℂ := by
    simp only [inner_sub_left,inner_sub_right,inner_self_eq_norm_sq_to_K,norm_vac]
    norm_num
  rw [he]
  calc
    _ ≤ ‖childState D h u-vac D h‖*‖childState D h w‖+
        ‖vac D h‖*‖childState D h w-vac D h‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ = ‖childState D h u-vac D h‖+‖childState D h w-vac D h‖ := by rw [norm_childState,norm_vac,mul_one,one_mul]
    _ ≤ 3*wordBound u*(Real.sqrt (D:ℝ))⁻¹+3*wordBound w*(Real.sqrt (D:ℝ))⁻¹ :=
      add_le_add (child_word_vacuum_bound D h hD u) (child_word_vacuum_bound D h hD w)
    _ = _ := by ring

 

theorem child_Gram_limit (h : ℕ) (u w : List Label) :
    Tendsto (fun D => ⟪childState D h u,childState D h w⟫_ℂ) atTop (𝓝 1) := by
  have hr : Tendsto (fun D : ℕ => (Real.sqrt (D:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using hr.const_mul (3*(wordBound u+wordBound w)))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with D hD
  exact child_Gram_bound D h hD u w

end FiniteTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace FiniteTree.FullRoot
open QuantumCLT RootTensorCLT CoherentFock TensorPackets SpinOperators

 

abbrev Tail (D h : ℕ) := EuclideanSpace ℂ (Fin (D+1) → FiniteTree.Index D h)
abbrev Space (D h : ℕ) := Double (Tail D h)

def vac (D h : ℕ) : Space D h :=
  PointedTree.plusEmbedding (FiniteTensor.power (D+1) (FiniteTree.vac D h))

def tensorState (D h : ℕ) (l : List Label) : Tail D h :=
  FiniteTensor.power (D+1) (childState D h l)

def tensorPulse (D h : ℕ) (i : Label) : Tail D h →L[ℂ] Tail D h :=
  FiniteTensor.operatorPower (D+1)
    (NormedSpace.exp (((Real.sqrt (D:ℝ))⁻¹:ℝ) • childGenerator D h i))

theorem tensor_step (D h : ℕ) (i : Label) (l : List Label) :
    tensorPulse D h i (tensorState D h l)=tensorState D h (i::l) := by
  rw [tensorPulse,tensorState,FiniteTensor.operatorPower_apply]
  congr 1

 

def ordinary (D h : ℕ) (w : List PointedTree.Gate) : Space D h →L[ℂ] Space D h :=
  run (tensorPulse D h) (program w)

def insertion (D h : ℕ) (w : List PointedTree.Gate) : Space D h :=
  run (tensorPulse D h) (insertionProgram w) (vac D h)

theorem run_packet (D h : ℕ) (p : List (Pulse Label)) :
    run (tensorPulse D h) p (vac D h)=packet (tensorState D h) (compile p start) := by
  have he : tensorState D h []=FiniteTensor.power (D+1) (FiniteTree.vac D h) := by
    simp only [tensorState,childState,generators,List.map_nil,List.prod_nil,one_apply_eq_self]
  rw [vac,←he,←start_packet]
  exact RootTensorCLT.run_packet _ _ (tensor_step D h) _ _

theorem tensor_Gram_factor (D h : ℕ) (u w : List Label) :
    ⟪tensorState D h u,tensorState D h w⟫_ℂ=
      ⟪RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) u,
        RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) w⟫_ℂ*
      ⟪childState D h u,childState D h w⟫_ℂ := by
  simp only [tensorState,RootTensorCLT.tensorState,childState,FiniteTensor.inner_power,pow_succ]

 

theorem tensor_Gram_limit (h : ℕ) (u w : List Label) :
    Tendsto (fun D => ⟪tensorState D h u,tensorState D h w⟫_ℂ) atTop
      (𝓝 ⟪fockState (childDirection h) u,fockState (childDirection h) w⟫_ℂ) := by
  simp only [tensor_Gram_factor]
  have ht := (FiniteTree.tensor_Gram_limit h u w).mul (child_Gram_limit h u w)
  simpa only [mul_one] using ht

theorem program_Gram_limit (h : ℕ) (u w : List (Pulse Label)) :
    Tendsto (fun D => ⟪run (tensorPulse D h) u (vac D h),run (tensorPulse D h) w (vac D h)⟫_ℂ)
      atTop (𝓝 ⟪run (W ∘ childDirection h) u (PointedTree.vac (h+1)),
        run (W ∘ childDirection h) w (PointedTree.vac (h+1))⟫_ℂ) := by
  have ht := TensorPackets.Gram_limit (fun D => Tail D h) (fun D => tensorState D h)
    (fockState (childDirection h)) (tensor_Gram_limit h) (compile u start) (compile w start)
  have hf (p : List (Pulse Label)) : run (W ∘ childDirection h) p (PointedTree.vac (h+1))=
      packet (fockState (childDirection h)) (compile p start) := by
    change run (W ∘ childDirection h) p (PointedTree.plusEmbedding (fockState (childDirection h) []))=_
    rw [←start_packet]
    exact RootTensorCLT.run_packet _ _ (fock_step _) _ _
  simpa only [run_packet,hf] using ht

 

theorem insertion_Gram_limit (h : ℕ) (u w : List PointedTree.Gate) :
    Tendsto (fun D => ⟪insertion D h u,insertion D h w⟫_ℂ) atTop
      (𝓝 ⟪(PointedTree.ordinary u (h+1)).insertion,(PointedTree.ordinary w (h+1)).insertion⟫_ℂ) := by
  have ht := program_Gram_limit h (insertionProgram u) (insertionProgram w)
  change Tendsto _ atTop (𝓝 ⟪((PointedTree.ordinary u (h+1)).insertion : PointedTree.Level (h+1)),
    ((PointedTree.ordinary w (h+1)).insertion : PointedTree.Level (h+1))⟫_ℂ)
  simpa only [insertion,FiniteTree.limiting_insertion] using ht

end FiniteTree.FullRoot

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree.FullRoot
open TensorPackets RootTensorCLT

 
def slot (D h : ℕ) (j : Fin (D+1)) : Space D h →L[ℂ] Space D h :=
  TensorPackets.diagonal (fun _ => FiniteTensor.excitedSlot (D+1) (FiniteTree.vac D h) j)

theorem slot_projection (D h : ℕ) (j : Fin (D+1)) : IsStarProjection (slot D h j) :=
  TensorPackets.diagonal_projection _ (fun _ => FiniteTensor.excitedSlot_projection
    (D+1) (FiniteTree.vac D h) (FiniteTree.norm_vac D h) j)

def occupation (D h : ℕ) (x : Space D h) : ℝ := ∑j : Fin (D+1),‖slot D h j x‖^2

theorem tensor_slot_bound (D h : ℕ) (hD : 0<D) (l : List Label) (j : Fin (D+1)) :
    ‖FiniteTensor.excitedSlot (D+1) (FiniteTree.vac D h) j (tensorState D h l)‖≤
      6*wordBound l*(Real.sqrt (D:ℝ))⁻¹ := by
  calc
    _ ≤ 2*‖childState D h l-FiniteTree.vac D h‖ :=
      FiniteTensor.excitedSlot_power_bound (D+1) _ _ (FiniteTree.norm_vac D h) (norm_childState D h l) j
    _ ≤ 2*(3*wordBound l*(Real.sqrt (D:ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left (child_word_vacuum_bound D h hD l) (by norm_num)
    _ = _ := by ring

theorem packet_slot_bound (D h : ℕ) (hD : 0<D) (ts : List (Term Label)) (j : Fin (D+1)) :
    ‖slot D h j (packet (tensorState D h) ts)‖≤
      packetOccupationBound ts*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [slot,diagonal_constant_packet]
  exact packet_bound _ (fun l => 6*wordBound l) (fun l => mul_nonneg (by norm_num) (wordBound_nonneg l))
    _ (by positivity) (fun l => by simpa only [Function.comp_apply,mul_assoc] using tensor_slot_bound D h hD l j) _

theorem insertion_slot_bound (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) (j : Fin (D+1)) :
    ‖slot D h j (insertion D h w)‖≤
      packetOccupationBound (compile (insertionProgram w) start)*(Real.sqrt (D:ℝ))⁻¹ := by
  rw [insertion,run_packet]
  exact packet_slot_bound D h hD _ j

 

theorem insertion_occupation_bound (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) :
    occupation D h (insertion D h w)≤
      2*packetOccupationBound (compile (insertionProgram w) start)^2 := by
  let C := packetOccupationBound (compile (insertionProgram w) start)
  have hC : 0≤C := packetOccupationBound_nonneg _
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have hDp : (0:ℝ)<D := by exact_mod_cast hD
  calc
    _ ≤ ∑j : Fin (D+1), (C*(Real.sqrt (D:ℝ))⁻¹)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ (norm_nonneg _) (insertion_slot_bound D h hD w j) _
    _ = ((D:ℝ)+1)*(C^2*(D:ℝ)⁻¹) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg D)]
    _ ≤ (2*(D:ℝ))*(C^2*(D:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2*C^2 := by field_simp

def numberOperator (D h : ℕ) : Space D h →L[ℂ] Space D h := ∑j : Fin (D+1),slot D h j

theorem slot_expectation (D h : ℕ) (j : Fin (D+1)) (x : Space D h) :
    ⟪x,slot D h j x⟫_ℂ=(‖slot D h j x‖^2:ℝ) := by
  have hp := slot_projection D h j
  have he : ⟪slot D h j x,slot D h j x⟫_ℂ=⟪x,slot D h j x⟫_ℂ := by
    rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint]
    change ⟪x,(slot D h j*slot D h j) x⟫_ℂ=_
    rw [hp.isIdempotentElem]
  rw [←he,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem number_expectation (D h : ℕ) (x : Space D h) :
    ⟪x,numberOperator D h x⟫_ℂ=(occupation D h x:ℂ) := by
  simp only [numberOperator,occupation,_root_.sum_apply,inner_sum,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact slot_expectation D h j x

end FiniteTree.FullRoot

 

open scoped InnerProductSpace
namespace FiniteTree.FullRoot
open RootTensorCLT TensorPackets SpinOperators

theorem pulse_exp (D h : ℕ) (i : Label) :
    tensorPulse D h i=FiniteTensor.operatorPower (D+1)
      ((FiniteTree.ordinary D i.1 h).exponential ((Real.sqrt (D:ℝ))⁻¹*i.2)) := by
  unfold tensorPulse Even.exponential
  congr 2
  exact generator_scaled _ _ _

theorem pulse_unitary (D h : ℕ) (i : Label) : tensorPulse D h i ∈ unitary _ := by
  rw [pulse_exp]
  exact FiniteTensor.operatorPower_unitary _ _ (Even.exponential_unitary _ _)

theorem pulse_star (D h : ℕ) (i : Label) :
    tensorPulse D h (negateLabel i)=star (tensorPulse D h i) := by
  let : NormedAlgebra ℚ (FiniteTree.Space D h →L[ℂ] FiniteTree.Space D h) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [pulse_exp,pulse_exp,←FiniteTensor.operatorPower_star]
  congr 1
  simp only [negateLabel,Even.exponential,mul_neg,Even.generator_neg,
    NormedSpace.star_exp,Even.generator_star]

theorem ordinary_unitary (D h : ℕ) (w : List PointedTree.Gate) :
    ordinary D h w ∈ unitary _ := by
  induction w with
  | nil => exact (unitary _).one_mem
  | cons g w ih =>
    cases g with
    | mixer β => exact (unitary _).mul_mem (act_mem_unitary (RootSpin.R_unitary β)) ih
    | cost γ => exact (unitary _).mul_mem (diagonal_unitary _ (fun i => pulse_unitary D h _)) ih

 

theorem insertion_eq (D h : ℕ) (w : List PointedTree.Gate) :
    insertion D h w=(star (ordinary D h w)*(act RootSpin.Z : Space D h →L[ℂ] Space D h)*ordinary D h w) (vac D h) := by
  rw [insertion,insertionProgram,run_append,run_append,run_adjoint _ negateLabel (pulse_star D h),
    run_cons,run_nil,mul_one]
  rfl

@[simp] theorem norm_vac (D h : ℕ) : ‖vac D h‖=1 := by
  exact (PointedTree.plusEmbedding.norm_map _).trans
    (FiniteTree.norm_power_of_norm_one (D+1) (FiniteTree.vac D h) (FiniteTree.norm_vac D h))

@[simp] theorem norm_insertion (D h : ℕ) (w : List PointedTree.Gate) : ‖insertion D h w‖=1 := by
  rw [insertion_eq]
  have hu : (star (ordinary D h w)*(act RootSpin.Z : Space D h →L[ℂ] Space D h)*ordinary D h w) ∈ unitary _ :=
    (unitary _).mul_mem ((unitary _).mul_mem (Unitary.star_mem (ordinary_unitary D h w))
    (act_mem_unitary RootSpin.Z_unitary)) (ordinary_unitary D h w)
  exact (Unitary.linearIsometryEquiv ⟨_,hu⟩).norm_map (vac D h) |>.trans (norm_vac D h)

def flip (D h : ℕ) : Space D h →L[ℂ] Space D h :=
  spinFlip (FiniteTensor.operatorPower (D+1) (FiniteTree.flip D h))

theorem flip_unitary (D h : ℕ) : flip D h ∈ unitary _ :=
  spinFlip_unitary _ (FiniteTensor.operatorPower_unitary _ _ (FiniteTree.flip_unitary D h))

theorem flip_square (D h : ℕ) : flip D h*flip D h=1 := by
  apply spinFlip_square
  rw [←FiniteTensor.operatorPower_mul,FiniteTree.flip_square,FiniteTensor.operatorPower_one]

theorem flip_vac (D h : ℕ) : flip D h (vac D h)=vac D h := by
  ext i
  simp only [flip,vac,spinFlip_apply,PointedTree.plusEmbedding_apply,map_smul,
    FiniteTensor.operatorPower_apply,FiniteTree.flip_vac]

@[simp] theorem flip_star (D h : ℕ) : star (flip D h)=flip D h := by
  calc
    star (flip D h)=star (flip D h)*(flip D h*flip D h) := by rw [flip_square,mul_one]
    _ = (star (flip D h)*flip D h)*flip D h := (mul_assoc _ _ _).symm
    _ = flip D h := by rw [(Unitary.mem_iff.mp (flip_unitary D h)).1,one_mul]

theorem flip_ordinary (D h : ℕ) (w : List PointedTree.Gate) :
    flip D h*ordinary D h w=ordinary D h w*flip D h := by
  induction w with
  | nil => simp [ordinary,program]
  | cons g w ih =>
    have commute_then (B : Space D h →L[ℂ] Space D h) (hh : flip D h*B=B*flip D h) :
        flip D h*(B*ordinary D h w)=(B*ordinary D h w)*flip D h := by
      rw [←mul_assoc,hh,mul_assoc,ih,←mul_assoc]
    cases g with
    | mixer β =>
      change flip D h*(act (RootSpin.R β)*ordinary D h w)=(act (RootSpin.R β)*ordinary D h w)*flip D h
      apply commute_then
      apply ContinuousLinearMap.ext
      intro x
      simp only [mul_apply_eq_comp,flip]
      exact spinFlip_R (H := Tail D h) (FiniteTensor.operatorPower (D+1) (FiniteTree.flip D h)) β x
    | cost γ =>
      change flip D h*(applyPulse (tensorPulse D h) (.control (fun i => (w,if i=0 then -γ else γ)))*ordinary D h w)=
        (applyPulse (tensorPulse D h) (.control (fun i => (w,if i=0 then -γ else γ)))*ordinary D h w)*flip D h
      apply commute_then
      apply ContinuousLinearMap.ext
      intro x
      simp only [mul_apply_eq_comp,flip,applyPulse]
      apply spinFlip_diagonal
      intro i
      simp only [Function.comp_apply]
      rw [pulse_exp,pulse_exp,←FiniteTensor.operatorPower_mul,←FiniteTensor.operatorPower_mul]
      congr 1
      have he (j : Fin 2) : (Real.sqrt (D:ℝ))⁻¹*(if j=0 then -γ else γ)=
          (if j=0 then -γ/Real.sqrt D else γ/Real.sqrt D) := by split <;> ring
      simp only [he]
      exact (FiniteTree.ordinary D w h).cost_blocks_flip γ i

theorem insertion_odd (D h : ℕ) (w : List PointedTree.Gate) :
    flip D h (insertion D h w)= -insertion D h w := by
  have hs : flip D h*star (ordinary D h w)=star (ordinary D h w)*flip D h := by
    have hh := congrArg star (flip_ordinary D h w)
    simpa only [star_mul,flip_star] using hh.symm
  have hZ : flip D h*(act RootSpin.Z : Space D h →L[ℂ] Space D h)= -(act RootSpin.Z : Space D h →L[ℂ] Space D h)*flip D h := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [mul_apply_eq_comp,neg_apply,flip]
    exact spinFlip_Z (H := Tail D h) (FiniteTensor.operatorPower (D+1) (FiniteTree.flip D h)) x
  rw [insertion_eq]
  change (flip D h*(star (ordinary D h w)*(act RootSpin.Z : Space D h →L[ℂ] Space D h)*ordinary D h w)) (vac D h)=_
  rw [←mul_assoc,←mul_assoc,hs,mul_assoc (star _),hZ]
  simp only [mul_assoc,flip_ordinary,mul_apply_eq_comp,neg_apply,flip_vac,map_neg]

 
theorem insertion_centered (D h : ℕ) (w : List PointedTree.Gate) :
    ⟪vac D h,insertion D h w⟫_ℂ=0 := by
  have hi := (Unitary.linearIsometryEquiv ⟨flip D h,flip_unitary D h⟩).inner_map_map
    (vac D h) (insertion D h w)
  change ⟪flip D h (vac D h),flip D h (insertion D h w)⟫_ℂ=⟪vac D h,insertion D h w⟫_ℂ at hi
  rw [flip_vac,insertion_odd,inner_neg_right] at hi
  linear_combination -(1/2:ℂ)*hi

end FiniteTree.FullRoot

 

open scoped InnerProductSpace Topology
open Filter ContinuousLinearMap
namespace FiniteTree.FullRoot
open QuantumCLT CoherentFock RootTensorCLT TensorPackets

 
def excitation (D h : ℕ) (w : List PointedTree.Gate) : Tail D h :=
  FiniteTensor.normalizedInsertion (D+1) 1 (FiniteTree.ordinary D w h).observable
    (FiniteTensor.power (D+1) (FiniteTree.vac D h))

theorem excitation_factor (D h : ℕ) (hD : 0<D) (w : List PointedTree.Gate) (l : List Label) :
    ⟪excitation D h w,tensorState D h l⟫_ℂ=
      ((Real.sqrt ((D:ℝ)+1)/Real.sqrt (D:ℝ):ℝ):ℂ)*
      ⟪FiniteTree.excitation D h w,RootTensorCLT.tensorState D (FiniteTree.vac D h) (childGenerator D h) l⟫_ℂ*
      ⟪FiniteTree.vac D h,childState D h l⟫_ℂ := by
  simp only [excitation,tensorState,FiniteTree.excitation,RootTensorCLT.tensorState,childState]
  rw [FiniteTensor.inner_excitation_power _ _ _ _ (Even.observable_star _),
    FiniteTensor.inner_excitation_power _ _ _ _ (Even.observable_star _),
    FiniteTensor.inner_normalizedInsertion,FiniteTensor.inner_normalizedInsertion]
  simp only [mul_apply_eq_comp,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  have hs : (Real.sqrt (D:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hD)).ne'
  have he : D-1+1=D := Nat.sub_add_cancel hD
  have hp (z : ℂ) : z^D=z^(D-1)*z := by
    calc
      z^D=z^(D-1+1) := by rw [he]
      _ = _ := pow_succ _ _
  rw [hp]
  push_cast
  field_simp

theorem sqrt_ratio_limit :
    Tendsto (fun D : ℕ => Real.sqrt ((D:ℝ)+1)/Real.sqrt (D:ℝ)) atTop (𝓝 1) := by
  have hi : Tendsto (fun D : ℕ => (D:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds.add hi) :
    Tendsto (fun D : ℕ => 1+(D:ℝ)⁻¹) atTop (𝓝 (1+0)))
  simp only [add_zero,Real.sqrt_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with D hD
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  change Real.sqrt (1+(D:ℝ)⁻¹)=Real.sqrt ((D:ℝ)+1)/Real.sqrt (D:ℝ)
  rw [←Real.sqrt_div (by positivity)]
  congr 1
  field_simp [hd]

theorem excitation_tensor_limit (h : ℕ) (w : List PointedTree.Gate) (l : List Label) :
    Tendsto (fun D => ⟪excitation D h w,tensorState D h l⟫_ℂ) atTop
      (𝓝 ⟪creationVacuum (PointedTree.ordinary w h).insertion,fockState (childDirection h) l⟫_ℂ) := by
  have hg : Tendsto (fun D => ⟪FiniteTree.vac D h,childState D h l⟫_ℂ) atTop (𝓝 1) := by
    have ht := child_Gram_limit h [] l
    simpa only [childState,generators,List.map_nil,List.prod_nil,one_apply_eq_self] using ht
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp sqrt_ratio_limit
  have ht := (hr.mul (FiniteTree.excitation_tensor_limit h w l)).mul hg
  simp only [Complex.ofReal_one,one_mul,mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with D hD
  exact (excitation_factor D h hD w l).symm

 
theorem root_shift_insertion_limit (h : ℕ) (w u : List PointedTree.Gate) :
    Tendsto (fun D => ⟪PointedTree.plusEmbedding (excitation D h w),insertion D h u⟫_ℂ) atTop
      (𝓝 ⟪PointedTree.rootShift h (PointedTree.ordinary w h).insertion,
        (PointedTree.ordinary u (h+1)).insertion⟫_ℂ) := by
  have ht := TensorPackets.marked_limit (fun D => Tail D h) (fun D => tensorState D h)
    (fockState (childDirection h)) (fun D => excitation D h w)
    (creationVacuum (PointedTree.ordinary w h).insertion)
    (excitation_tensor_limit h w) (compile (insertionProgram u) start)
  have hf : run (W ∘ childDirection h) (insertionProgram u) (PointedTree.vac (h+1))=
      packet (fockState (childDirection h)) (compile (insertionProgram u) start) := by
    change run (W ∘ childDirection h) (insertionProgram u)
      (PointedTree.plusEmbedding (fockState (childDirection h) []))=_
    rw [←start_packet]
    exact RootTensorCLT.run_packet _ _ (fock_step _) _ _
  change Tendsto _ atTop (𝓝 ⟪(PointedTree.rootShift h (PointedTree.ordinary w h).insertion : PointedTree.Level (h+1)),
    ((PointedTree.ordinary u (h+1)).insertion : PointedTree.Level (h+1))⟫_ℂ)
  rw [PointedTree.rootShift_coe,limiting_insertion,hf]
  simpa only [insertion,run_packet] using ht

end FiniteTree.FullRoot

 

open scoped InnerProductSpace ComplexConjugate
namespace EdgeProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

theorem decomposition (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S)
    (P : H →L[ℂ] H) (_ : IsStarProjection P) (f : H)
    (hc : ⟪P f,S (P f)⟫_ℂ=0) :
    ⟪f,S f⟫_ℂ=(2:ℂ)*((⟪P f,S f⟫_ℂ).re:ℂ)+⟪f-P f,S (f-P f)⟫_ℂ := by
  have hs (x y : H) : ⟪x,S y⟫_ℂ=⟪S x,y⟫_ℂ := by
    have hi := S.inner_map_map (S x) y
    simpa only [hS x] using hi
  have hcross : ⟪f-P f,S (P f)⟫_ℂ=star ⟪P f,S f⟫_ℂ := by
    rw [inner_sub_left,hc,sub_zero,hs]
    simpa only [Complex.star_def] using (inner_conj_symm (𝕜 := ℂ) (S f) (P f)).symm
  have hp : ⟪P f,S f⟫_ℂ=⟪P f,S (f-P f)⟫_ℂ := by
    rw [map_sub,inner_sub_right,hc,sub_zero]
  calc
    ⟪f,S f⟫_ℂ=⟪P f+(f-P f),S (P f+(f-P f))⟫_ℂ := by rw [add_sub_cancel]
    _ = ⟪P f,S (f-P f)⟫_ℂ + star ⟪P f,S f⟫_ℂ + ⟪f-P f,S (f-P f)⟫_ℂ := by
      rw [map_add,inner_add_left,inner_add_right,inner_add_right,hc,zero_add,hcross]
      abel
    _ = _ := by rw [←hp,Complex.star_def,Complex.add_conj]; push_cast; ring

 

omit [CompleteSpace H] in
theorem remainder_bound (S : H ≃ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (f : H) :
    ‖⟪f-P f,S (f-P f)⟫_ℂ‖ ≤ ‖f-P f‖^2 := by
  calc
    _ ≤ ‖f-P f‖*‖S (f-P f)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [S.norm_map]; ring

theorem real_decomposition (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (f : H)
    (hc : ⟪P f,S (P f)⟫_ℂ=0) :
    |(⟪f,S f⟫_ℂ).re-2*(⟪P f,S f⟫_ℂ).re| ≤ ‖f-P f‖^2 := by
  rw [decomposition S hS P hP f hc]
  have he : ((2:ℂ)*((⟪P f,S f⟫_ℂ).re:ℂ)+⟪f-P f,S (f-P f)⟫_ℂ).re-
      2*(⟪P f,S f⟫_ℂ).re=(⟪f-P f,S (f-P f)⟫_ℂ).re := by
    simp
  rw [he]
  exact (Complex.abs_re_le_norm ⟪f-P f,S (f-P f)⟫_ℂ).trans (remainder_bound S P f)

end EdgeProjection

end

end OAI
