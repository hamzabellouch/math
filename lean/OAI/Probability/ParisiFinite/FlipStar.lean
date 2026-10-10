import Mathlib
import OAI.Probability.ParisiFinite.MovingTensorInsertionLimit
import OAI.Probability.ParisiFinite.ReverseWord

namespace OAI

/-! Flip Star. -/

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
open scoped InnerProductSpace
namespace FiniteTree
open RootSpin SpinOperators

@[simp] theorem flip_star (D h : ℕ) : star (flip D h)=flip D h := by
  calc
    star (flip D h)=star (flip D h)*(flip D h*flip D h) := by rw [flip_square,mul_one]
    _ = (star (flip D h)*flip D h)*flip D h := (mul_assoc _ _ _).symm
    _ = flip D h := by rw [(Unitary.mem_iff.mp (flip_unitary D h)).1,one_mul]

 

structure Even (D h : ℕ) where
  op : Space D h →L[ℂ] Space D h
  unitary : op ∈ _root_.unitary _
  commutes : flip D h*op=op*flip D h

namespace Even
variable {D h : ℕ}

def ident (D h : ℕ) : Even D h where
  op := 1
  unitary := (_root_.unitary _).one_mem
  commutes := by simp

def followedBy (U V : Even D h) : Even D h where
  op := V.op*U.op
  unitary := (_root_.unitary _).mul_mem V.unitary U.unitary
  commutes := by
    rw [←mul_assoc,V.commutes,mul_assoc,U.commutes,←mul_assoc]

def mixer (D h : ℕ) (t : ℝ) : Even D h where
  op := root D h (R t)
  unitary := root_unitary D h (R_unitary t)
  commutes := by
    apply ContinuousLinearMap.ext
    intro x
    exact flip_rootR D h t x

theorem star_commutes (U : Even D h) : flip D h*star U.op=star U.op*flip D h := by
  have hs := congrArg star U.commutes
  simpa only [star_mul,flip_star] using hs.symm

 
def observable (U : Even D h) : Space D h →L[ℂ] Space D h :=
  star U.op*root D h Z*U.op

@[simp] theorem observable_star (U : Even D h) : star U.observable=U.observable := by
  simp only [observable,star_mul,star_star,←root_star,Matrix.star_eq_conjTranspose,Z_star,mul_assoc]

theorem observable_unitary (U : Even D h) : U.observable ∈ _root_.unitary _ :=
  (_root_.unitary _).mul_mem ((_root_.unitary _).mul_mem (Unitary.star_mem U.unitary)
    (root_unitary D h Z_unitary)) U.unitary

@[simp] theorem norm_observable (U : Even D h) : ‖U.observable‖=1 :=
  CStarRing.norm_of_mem_unitary U.observable_unitary

theorem observable_odd (U : Even D h) :
    flip D h*U.observable= -U.observable*flip D h := by
  have hz : flip D h*root D h Z= -root D h Z*flip D h := by
    apply ContinuousLinearMap.ext
    intro x
    exact flip_rootZ D h x
  change flip D h*(star U.op*root D h Z*U.op)= -(star U.op*root D h Z*U.op)*flip D h
  calc
    _ = (flip D h*star U.op)*root D h Z*U.op := by simp only [mul_assoc]
    _ = star U.op*(flip D h*root D h Z)*U.op := by rw [U.star_commutes]; simp only [mul_assoc]
    _ = _ := by
      rw [hz]
      simp only [mul_assoc,U.commutes]
      rw [neg_mul (root D h Z) (U.op*flip D h),
        mul_neg (star U.op) (root D h Z*(U.op*flip D h)),
        neg_mul (star U.op*(root D h Z*U.op)) (flip D h)]
      simp only [mul_assoc]

 

theorem observable_centered (U : Even D h) :
    ⟪vac D h,U.observable (vac D h)⟫_ℂ=0 := by
  have ho : flip D h (U.observable (vac D h))= -U.observable (vac D h) := by
    have hh := congrArg (fun A : Space D h →L[ℂ] Space D h => A (vac D h)) U.observable_odd
    simpa only [mul_apply_eq_comp,neg_apply,flip_vac] using hh
  have hi := (Unitary.linearIsometryEquiv ⟨flip D h,flip_unitary D h⟩).inner_map_map
    (vac D h) (U.observable (vac D h))
  change ⟪flip D h (vac D h),flip D h (U.observable (vac D h))⟫_ℂ=
    ⟪vac D h,U.observable (vac D h)⟫_ℂ at hi
  rw [flip_vac,ho,inner_neg_right] at hi
  linear_combination -(1/2:ℂ)*hi

 

def generator (U : Even D h) (t : ℝ) : Space D h →L[ℂ] Space D h :=
  (Complex.I*(t:ℂ)) • U.observable

@[simp] theorem generator_neg (U : Even D h) (t : ℝ) : U.generator (-t)= -U.generator t := by
  simp only [generator,Complex.ofReal_neg,mul_neg]
  exact _root_.neg_smul (Complex.I*(t:ℂ)) U.observable

@[simp] theorem generator_star (U : Even D h) (t : ℝ) : star (U.generator t)= -U.generator t := by
  simp only [generator,star_smul,star_mul,Complex.star_def,
    Complex.conj_I,Complex.conj_ofReal,U.observable_star]
  rw [show (t:ℂ)* -Complex.I= -(Complex.I*(t:ℂ)) by ring]
  exact _root_.neg_smul (Complex.I*(t:ℂ)) U.observable

@[simp] theorem norm_generator (U : Even D h) (t : ℝ) : ‖U.generator t‖=|t| := by
  simp [generator,norm_smul]

@[simp] theorem generator_centered (U : Even D h) (t : ℝ) :
    ⟪vac D h,U.generator t (vac D h)⟫_ℂ=0 := by
  simp only [generator,smul_apply,inner_smul_right,U.observable_centered,mul_zero]

def exponential (U : Even D h) (t : ℝ) : Space D h →L[ℂ] Space D h :=
  NormedSpace.exp (U.generator t)

theorem exponential_unitary (U : Even D h) (t : ℝ) : U.exponential t ∈ _root_.unitary _ := by
  let : NormedAlgebra ℚ (Space D h →L[ℂ] Space D h) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : CompleteSpace (Space D h) := PiLp.completeSpace 2 (fun _ : Index D h => ℂ)
  let : CompleteSpace (Space D h →L[ℂ] Space D h) := ContinuousLinearMap.instCompleteSpace
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff]
    exact U.generator_star t)

theorem generator_odd (U : Even D h) (t : ℝ) :
    flip D h*U.generator t=U.generator (-t)*flip D h := by
  simp only [generator,mul_smul_comm,smul_mul_assoc,U.observable_odd,Complex.ofReal_neg,mul_neg]
  rw [neg_mul U.observable (flip D h),
    smul_neg (Complex.I*(t:ℂ)) (U.observable*flip D h),
    neg_smul (Complex.I*(t:ℂ)) (U.observable*flip D h)]

theorem exponential_odd (U : Even D h) (t : ℝ) :
    flip D h*U.exponential t=U.exponential (-t)*flip D h := by
  let : NormedAlgebra ℚ (Space D h →L[ℂ] Space D h) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : CompleteSpace (Space D h) := PiLp.completeSpace 2 (fun _ : Index D h => ℂ)
  let : CompleteSpace (Space D h →L[ℂ] Space D h) := ContinuousLinearMap.instCompleteSpace
  exact (show SemiconjBy (flip D h) (U.generator t) (U.generator (-t)) from U.generator_odd t).exp_right

end Even
end FiniteTree

 

open scoped InnerProductSpace
namespace FiniteTree
open SpinOperators TensorPackets

 

theorem spinFlip_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (K : Fin 2 → H →L[ℂ] H)
    (hK : ∀i,T*K i=K (1-i)*T) (x : Double H) :
    spinFlip T (TensorPackets.diagonal K x)=TensorPackets.diagonal K (spinFlip T x) := by
  ext i
  simp only [spinFlip_apply,diagonal_apply]
  have hk := congrArg (fun A : H →L[ℂ] H => A (x (1-i))) (hK (1-i))
  have hi : (1-(1-i):Fin 2)=i := by omega
  simpa only [mul_apply_eq_comp,hi] using hk

theorem flip_control (D h : ℕ) (K : Fin 2 → Space D h →L[ℂ] Space D h)
    (hK : ∀i,flip D h*K i=K (1-i)*flip D h) :
    flip D (h+1)*control D h K=control D h K*flip D (h+1) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (split D (h+1)).injective
  change split D (h+1) (flip D (h+1) (control D h K x)) =
    split D (h+1) (control D h K (flip D (h+1) x))
  rw [split_flip,split_control,split_control,split_flip]
  apply spinFlip_diagonal
  intro i
  rw [←FiniteTensor.operatorPower_mul,hK i,FiniteTensor.operatorPower_mul]

namespace Even

theorem cost_blocks_flip {D h : ℕ} (U : Even D h) (γ : ℝ) (i : Fin 2) :
    flip D h*U.exponential (if i=0 then -γ/Real.sqrt D else γ/Real.sqrt D)=
      U.exponential (if 1-i=0 then -γ/Real.sqrt D else γ/Real.sqrt D)*flip D h := by
  rw [U.exponential_odd]
  congr 2
  fin_cases i <;> simp <;> ring

def cost (D h : ℕ) (U : Even D h) (γ : ℝ) : Even D (h+1) where
  op := control D h (fun i => U.exponential (if i=0 then -γ/(Real.sqrt D) else γ/(Real.sqrt D)))
  unitary := control_unitary D h _ (fun _ => U.exponential_unitary _)
  commutes := flip_control D h _ (U.cost_blocks_flip γ)

end Even

 

def ordinary (D : ℕ) : List PointedTree.Gate → (h : ℕ) → Even D h
  | [],h => Even.ident D h
  | PointedTree.Gate.mixer β::w,h => (ordinary D w h).followedBy (Even.mixer D h β)
  | PointedTree.Gate.cost _::w,0 => ordinary D w 0
  | PointedTree.Gate.cost γ::w,h+1 =>
      (ordinary D w (h+1)).followedBy (Even.cost D h (ordinary D w h) γ)

@[simp] theorem ordinary_zero_level (D : ℕ) (w : List PointedTree.Gate) :
    (ordinary D w 0).op=(PointedTree.ordinary w 0).op.toContinuousLinearEquiv.toContinuousLinearMap := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | mixer β =>
      apply ContinuousLinearMap.ext
      intro x
      change root D 0 (RootSpin.R β) ((ordinary D w 0).op x)=
        PointedTree.rootEquiv 0 (RootSpin.R β) (RootSpin.R_unitary β) ((PointedTree.ordinary w 0).op x)
      rw [ih]
      rfl
    | cost γ => exact ih

end FiniteTree

 

open scoped InnerProductSpace
namespace RootTensorCLT
open SpinOperators TensorPackets CoherentFock
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem run_nil (K : κ → H →L[ℂ] H) : run K []=1 := rfl
@[simp] theorem run_cons (K : κ → H →L[ℂ] H) (p : Pulse κ) (w : List (Pulse κ)) :
    run K (p::w)=applyPulse K p*run K w := rfl

theorem run_append (K : κ → H →L[ℂ] H) (u w : List (Pulse κ)) :
    run K (u++w)=run K u*run K w := by
  induction u with
  | nil => simp
  | cons p u ih => simp only [List.cons_append,run_cons,ih,mul_assoc]

def adjointPulse (neg : κ → κ) : Pulse κ → Pulse κ
  | .root A => .root A.conjTranspose
  | .control a => .control (neg ∘ a)

def adjointProgram (neg : κ → κ) : List (Pulse κ) → List (Pulse κ)
  | [] => []
  | p::w => adjointProgram neg w++[adjointPulse neg p]

variable [CompleteSpace H]

theorem applyPulse_adjoint (K : κ → H →L[ℂ] H) (neg : κ → κ)
    (hs : ∀i,K (neg i)=star (K i)) (p : Pulse κ) :
    applyPulse K (adjointPulse neg p)=star (applyPulse K p) := by
  cases p with
  | root A => exact (act_adjoint A).symm
  | control a =>
    change diagonal (K ∘ (neg ∘ a))=star (diagonal (K ∘ a))
    rw [←diagonal_star]
    congr 1
    funext i
    exact hs (a i)

theorem run_adjoint (K : κ → H →L[ℂ] H) (neg : κ → κ)
    (hs : ∀i,K (neg i)=star (K i)) (w : List (Pulse κ)) :
    run K (adjointProgram neg w)=star (run K w) := by
  induction w with
  | nil => simp [adjointProgram]
  | cons p w ih =>
    rw [adjointProgram,run_append,run_cons,run_nil,mul_one,ih,applyPulse_adjoint K neg hs,
      run_cons,star_mul]

theorem weyl_star {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (d : E) :
    W (-d)=star (W d) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  exact (inner_W_right d x y).symm

theorem tensorPulse_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (X : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (neg : κ → κ) (hn : ∀i,X (neg i)= -X i) (hs : ∀i,star (X i)= -X i) (i : κ) :
    tensorPulse D X (neg i)=star (tensorPulse D X i) := by
  let : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [tensorPulse,tensorPulse,←FiniteTensor.operatorPower_star]
  congr 1
  rw [NormedSpace.star_exp,star_smul,hs,hn]
  simp only [Complex.star_def,map_inv₀,Complex.conj_ofReal]

end RootTensorCLT

 

open scoped InnerProductSpace
namespace FiniteTree
open RootTensorCLT CoherentFock SpinOperators TensorPackets

abbrev Label := List PointedTree.Gate × ℝ

def negateLabel (i : Label) : Label := (i.1,-i.2)

theorem negateLabel_involutive : Function.Involutive negateLabel := by
  intro i
  cases i
  simp [negateLabel]

def childGenerator (D h : ℕ) (i : Label) : Space D h →L[ℂ] Space D h :=
  (ordinary D i.1 h).generator i.2

def childDirection (h : ℕ) (i : Label) : PointedTree.Mode h :=
  (i.2:ℂ) • (PointedTree.ordinary i.1 h).insertion

 

def program : List PointedTree.Gate → List (Pulse Label)
  | [] => []
  | .mixer β::w => .root (RootSpin.R β)::program w
  | .cost γ::w => .control (fun i => (w,if i=0 then -γ else γ))::program w

theorem generator_scaled {D h : ℕ} (U : Even D h) (s t : ℝ) :
    (s:ℂ) • U.generator t=U.generator (s*t) := by
  simp only [Even.generator,Complex.ofReal_mul,smul_smul]
  congr 1
  ring

theorem cost_tensorPulse (D h : ℕ) (w : List PointedTree.Gate) (γ : ℝ) (i : Fin 2) :
    FiniteTensor.operatorPower D ((ordinary D w h).exponential
        (if i=0 then -γ/Real.sqrt D else γ/Real.sqrt D))=
      tensorPulse D (childGenerator D h) (w,if i=0 then -γ else γ) := by
  simp only [tensorPulse,childGenerator,Even.exponential]
  rw [←Complex.ofReal_inv,generator_scaled]
  congr 2
  split <;> ring_nf

 
theorem split_ordinary (D h : ℕ) (w : List PointedTree.Gate) (x : Space D (h+1)) :
    split D (h+1) ((ordinary D w (h+1)).op x)=
      run (tensorPulse D (childGenerator D h)) (program w) (split D (h+1) x) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | mixer β =>
      change split D (h+1) (root D (h+1) (RootSpin.R β) ((ordinary D w (h+1)).op x))=_
      rw [split_root,ih]
      rfl
    | cost γ =>
      change split D (h+1) (control D h (fun i => (ordinary D w h).exponential
        (if i=0 then -γ/Real.sqrt D else γ/Real.sqrt D)) ((ordinary D w (h+1)).op x))=_
      rw [split_control,ih]
      change TensorPackets.diagonal _ _=TensorPackets.diagonal _ _
      congr 2
      funext i
      exact cost_tensorPulse D h w γ i

theorem weyl_cost_program (h : ℕ) (w : List PointedTree.Gate) (γ : ℝ) :
    WZ (-(γ:ℂ) • (PointedTree.ordinary w h).insertion)=
      applyPulse (W ∘ childDirection h) (.control (fun i => (w,if i=0 then -γ else γ))) := by
  ext x i
  simp only [applyPulse,diagonal_apply,Function.comp_apply,childDirection,WZ_apply]
  fin_cases i <;> simp

theorem limiting_ordinary (h : ℕ) (w : List PointedTree.Gate) :
    (PointedTree.ordinary w (h+1)).op.toContinuousLinearEquiv.toContinuousLinearMap=
      run (W ∘ childDirection h) (program w) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | mixer β =>
      apply ContinuousLinearMap.ext
      intro x
      change act (RootSpin.R β) ((PointedTree.ordinary w (h+1)).op x)=
        act (RootSpin.R β) (run (W ∘ childDirection h) (program w) x)
      rw [show (PointedTree.ordinary w (h+1)).op x=run (W ∘ childDirection h) (program w) x from
        congrArg (fun A : PointedTree.Level (h+1) →L[ℂ] PointedTree.Level (h+1) => A x) ih]
    | cost γ =>
      apply ContinuousLinearMap.ext
      intro x
      change WZ (-(γ:ℂ) • (PointedTree.ordinary w h).insertion) ((PointedTree.ordinary w (h+1)).op x)=_
      rw [weyl_cost_program]
      rw [show (PointedTree.ordinary w (h+1)).op x=run (W ∘ childDirection h) (program w) x from
        congrArg (fun A : PointedTree.Level (h+1) →L[ℂ] PointedTree.Level (h+1) => A x) ih]
      rfl

end FiniteTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace RootTensorCLT
open CoherentFock SpinOperators

variable {κ : Type*}

def Pulse.labels (p : Pulse κ) : Finset κ := by
  classical
  exact match p with
  | .root _ => ∅
  | .control a => Finset.univ.image a

def labels (w : List (Pulse κ)) : Finset κ := by
  classical
  exact w.toFinset.biUnion Pulse.labels

theorem control_mem_labels (w : List (Pulse κ)) (a : Fin 2 → κ)
    (ha : Pulse.control a ∈ w) (i : Fin 2) : a i ∈ labels w := by
  classical
  exact Finset.mem_biUnion.mpr ⟨Pulse.control a,List.mem_toFinset.mpr ha,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

theorem labels_tail (p : Pulse κ) (w : List (Pulse κ)) : labels w ⊆ labels (p::w) := by
  classical
  intro i hi
  obtain ⟨q,hq,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨q,List.mem_toFinset.mpr (List.mem_cons_of_mem p
    (List.mem_toFinset.mp hq)),hi⟩

theorem run_congr_labels {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K L : κ → H →L[ℂ] H) (w : List (Pulse κ))
    (hKL : ∀i∈labels w,K i=L i) : run K w=run L w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [run,run,ih (fun i hi => hKL i (labels_tail p w hi))]
    congr 1
    cases p with
    | root A => rfl
    | control a =>
      change TensorPackets.diagonal (K ∘ a)=TensorPackets.diagonal (L ∘ a)
      congr 1
      funext i
      exact hKL (a i) (control_mem_labels _ a (by simp) i)

def negClosure [DecidableEq κ] (neg : κ → κ) (S : Finset κ) : Finset κ :=
  S ∪ S.image neg

theorem mem_negClosure [DecidableEq κ] (neg : κ → κ) (hn : Function.Involutive neg)
    (S : Finset κ) (i : κ) : neg i ∈ negClosure neg S ↔ i ∈ negClosure neg S := by
  have step (j : κ) : j ∈ negClosure neg S → neg j ∈ negClosure neg S := by
    intro hj
    rcases Finset.mem_union.mp hj with hj|hj
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_union_left
      simpa only [hn k] using hk
  constructor
  · intro hi
    simpa only [hn i] using step (neg i) hi
  · exact step i

def mask [DecidableEq κ] {V : Type*} [Zero V] (S : Finset κ) (f : κ → V) (i : κ) : V :=
  if i∈S then f i else 0

 

theorem root_circuit_Gram_local_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : ℕ → Type*) [∀n,Fintype (ι n)] [∀n,DecidableEq (ι n)] [∀n,Nonempty (ι n)]
    (Ω : ∀n,EuclideanSpace ℂ (ι n))
    (X : ∀n,κ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (neg : κ → κ) (hn : Function.Involutive neg) (d : κ → E) (b : κ → ℝ)
    (hb : ∀i,0≤b i) (hΩ : ∀n,‖Ω n‖=1) (hX : ∀n i,‖X n i‖≤b i)
    (hneg : ∀n i,X n (neg i)= -X n i) (hstar : ∀n i,star (X n i)= -X n i)
    (hdneg : ∀i,d (neg i)= -d i)
    (hc : ∀n i,⟪Ω n,X n i (Ω n)⟫_ℂ=0)
    (hq : ∀i j,Tendsto (fun n => ⟪Ω n,X n i (X n j (Ω n))⟫_ℂ)
      atTop (𝓝 (-⟪d i,d j⟫_ℂ))) (u w : List (Pulse κ)) :
    Tendsto (fun n =>
      ⟪run (tensorPulse n (X n)) u (PointedTree.plusEmbedding (FiniteTensor.power n (Ω n))),
        run (tensorPulse n (X n)) w (PointedTree.plusEmbedding (FiniteTensor.power n (Ω n)))⟫_ℂ)
      atTop (𝓝 ⟪run (W ∘ d) u (PointedTree.vacuum E),run (W ∘ d) w (PointedTree.vacuum E)⟫_ℂ) := by
  classical
  let S := negClosure neg (labels u ∪ labels w)
  let L := ∑i∈S,b i
  have hL : 0≤L := Finset.sum_nonneg (fun i hi => hb i)
  have hxi (n : ℕ) (i : κ) : ‖mask S (X n) i‖≤L := by
    by_cases hi : i∈S
    · simp only [mask,ite_eq_left hi]
      exact (hX n i).trans (Finset.single_le_sum (fun j hj => hb j) hi)
    · simp only [mask,ite_eq_right hi,norm_zero]; exact hL
  have hmn (n : ℕ) (i : κ) : mask S (X n) (neg i)= -mask S (X n) i := by
    have hs := mem_negClosure neg hn (labels u ∪ labels w) i
    by_cases hi : i∈S <;> simp [mask,hi,show neg i∈S ↔ i∈S from hs,hneg]
  have hms (n : ℕ) (i : κ) : star (mask S (X n) i)= -mask S (X n) i := by
    by_cases hi : i∈S
    · simpa only [mask,ite_eq_left hi] using hstar n i
    · simp only [mask,ite_eq_right hi,neg_zero]
      exact star_zero (EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
  have hdn (i : κ) : mask S d (neg i)= -mask S d i := by
    have hs := mem_negClosure neg hn (labels u ∪ labels w) i
    by_cases hi : i∈S <;> simp [mask,hi,show neg i∈S ↔ i∈S from hs,hdneg]
  have hmc (n : ℕ) (i : κ) : ⟪Ω n,mask S (X n) i (Ω n)⟫_ℂ=0 := by
    by_cases hi : i∈S <;> simp [mask,hi,hc]
  have hmq (i j : κ) : Tendsto (fun n => ⟪Ω n,mask S (X n) i (mask S (X n) j (Ω n))⟫_ℂ)
      atTop (𝓝 (-⟪mask S d i,mask S d j⟫_ℂ)) := by
    by_cases hi : i∈S <;> by_cases hj : j∈S
    · simpa only [mask,ite_eq_left hi,ite_eq_left hj] using hq i j
    all_goals simp [mask,hi,hj]
  have hsU : labels u ⊆ S := fun i hi => Finset.mem_union_left _ (Finset.mem_union_left _ hi)
  have hsW : labels w ⊆ S := fun i hi => Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have hnrun (n : ℕ) (v : List (Pulse κ)) (hv : labels v ⊆ S) :
      run (tensorPulse n (mask S (X n))) v=run (tensorPulse n (X n)) v := by
    apply run_congr_labels
    intro i hi
    simp only [tensorPulse,mask,ite_eq_left (hv hi)]
  have hfrun (v : List (Pulse κ)) (hv : labels v ⊆ S) :
      run (W ∘ mask S d) v=run (W ∘ d) v := by
    apply run_congr_labels
    intro i hi
    simp only [Function.comp_apply,mask,ite_eq_left (hv hi)]
  simpa only [hnrun _ _ hsU,hnrun _ _ hsW,hfrun _ hsU,hfrun _ hsW] using
    root_circuit_Gram_limit ι Ω (fun n => mask S (X n)) neg (mask S d) L hL hΩ hxi hmn hms hdn hmc hmq u w

end RootTensorCLT

 

open scoped InnerProductSpace Topology
open Filter
namespace FiniteTree
open RootTensorCLT CoherentFock SpinOperators

def insertion (D h : ℕ) (w : List PointedTree.Gate) : Space D h :=
  (ordinary D w h).observable (vac D h)

def insertionProgram (w : List PointedTree.Gate) : List (Pulse Label) :=
  adjointProgram negateLabel (program w)++[.root RootSpin.Z]++program w

@[simp] theorem childGenerator_neg (D h : ℕ) (i : Label) :
    childGenerator D h (negateLabel i)= -childGenerator D h i :=
  (ordinary D i.1 h).generator_neg i.2

@[simp] theorem childGenerator_star (D h : ℕ) (i : Label) :
    star (childGenerator D h i)= -childGenerator D h i :=
  (ordinary D i.1 h).generator_star i.2

@[simp] theorem childDirection_neg (h : ℕ) (i : Label) :
    childDirection h (negateLabel i)= -childDirection h i := by
  simp only [childDirection,negateLabel,Complex.ofReal_neg,neg_smul]

theorem conj_split_ordinary (D h : ℕ) (w : List PointedTree.Gate) :
    (split D (h+1)).conjStarAlgEquiv (ordinary D w (h+1)).op=
      run (tensorPulse D (childGenerator D h)) (program w) := by
  apply ContinuousLinearMap.ext
  intro x
  change split D (h+1) ((ordinary D w (h+1)).op ((split D (h+1)).symm x))=_
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    split_ordinary D h w ((split D (h+1)).symm x)

theorem split_ordinary_star (D h : ℕ) (w : List PointedTree.Gate) (x : Space D (h+1)) :
    split D (h+1) (star (ordinary D w (h+1)).op x)=
      star (run (tensorPulse D (childGenerator D h)) (program w)) (split D (h+1) x) := by
  have hs : (split D (h+1)).conjStarAlgEquiv (star (ordinary D w (h+1)).op)=
      star ((split D (h+1)).conjStarAlgEquiv (ordinary D w (h+1)).op) :=
    (split D (h+1)).conjStarAlgEquiv.map_star' (ordinary D w (h+1)).op
  rw [conj_split_ordinary] at hs
  have hv := congrArg (fun A : Double (Tail D (h+1)) →L[ℂ] Double (Tail D (h+1)) => A (split D (h+1) x)) hs
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] using hv

theorem split_insertion (D h : ℕ) (w : List PointedTree.Gate) :
    split D (h+1) (insertion D (h+1) w)=
      run (tensorPulse D (childGenerator D h)) (insertionProgram w)
        (PointedTree.plusEmbedding (FiniteTensor.power D (vac D h))) := by
  simp only [insertion,Even.observable,mul_apply_eq_comp]
  rw [split_ordinary_star,split_root,split_ordinary]
  simp only [vac,LinearIsometryEquiv.apply_symm_apply]
  rw [insertionProgram,run_append,run_append,run_adjoint _ negateLabel
    (tensorPulse_star D _ negateLabel (childGenerator_neg D h) (childGenerator_star D h)),
    run_cons,run_nil,mul_one]
  rfl

theorem limiting_insertion (h : ℕ) (w : List PointedTree.Gate) :
    ((PointedTree.ordinary w (h+1)).insertion : PointedTree.Level (h+1))=
      run (W ∘ childDirection h) (insertionProgram w) (PointedTree.vac (h+1)) := by
  have hs (i : Label) : (W ∘ childDirection h) (negateLabel i)=star ((W ∘ childDirection h) i) := by
    simp only [Function.comp_apply,childDirection_neg,weyl_star]
  rw [insertionProgram,run_append,run_append,run_adjoint _ negateLabel hs,
    run_cons,run_nil,mul_one,←limiting_ordinary]
  change (PointedTree.ordinary w (h+1)).op.symm
      (act RootSpin.Z ((PointedTree.ordinary w (h+1)).op (PointedTree.vac (h+1))))=_
  rw [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.adjoint_eq_symm]
  rfl

theorem insertion_zero (D : ℕ) (w : List PointedTree.Gate) :
    insertion D 0 w=((PointedTree.ordinary w 0).insertion : PointedTree.Level 0) := by
  simp only [insertion,Even.observable,ordinary_zero_level,mul_apply_eq_comp]
  rw [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.adjoint_eq_symm]
  rfl

 

theorem child_second_moment (D h : ℕ) (i j : Label) :
    ⟪vac D h,childGenerator D h i (childGenerator D h j (vac D h))⟫_ℂ=
      -((i.2:ℂ)*(j.2:ℂ))*⟪insertion D h i.1,insertion D h j.1⟫_ℂ := by
  simp only [childGenerator,Even.generator,smul_apply,map_smul,inner_smul_right]
  have hadj : ⟪vac D h,(ordinary D i.1 h).observable ((ordinary D j.1 h).observable (vac D h))⟫_ℂ=
      ⟪insertion D h i.1,insertion D h j.1⟫_ℂ := by
    rw [←ContinuousLinearMap.adjoint_inner_left,←ContinuousLinearMap.star_eq_adjoint,
      Even.observable_star]
    rfl
  rw [hadj]
  have hi : Complex.I*Complex.I= -1 := Complex.I_mul_I
  calc
    _ = (Complex.I*Complex.I)*((i.2:ℂ)*(j.2:ℂ))*⟪insertion D h i.1,insertion D h j.1⟫_ℂ := by ring
    _ = _ := by rw [hi]; ring

end FiniteTree

end

end OAI
