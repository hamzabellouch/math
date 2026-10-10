import Mathlib
import OAI.Probability.ParisiFinite.Space

namespace OAI

/-! Param Gate. -/

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
namespace SeededTree
open CoherentFock Complex RootSpin PointedTree
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

inductive ParamGate (X : Type*)
  | mixer (beta : X → ℝ)
  | cost (gamma : X → ℝ)
  | seed (angles : Fin 2 → X → ℝ)

def ParamGate.eval (g : SeededTree.ParamGate X) (t : X) : SeededTree.Gate :=
  match g with
  | .mixer f => .mixer (f t)
  | .cost f => .cost (f t)
  | .seed f => .seed (fun q => f q t)

def ParamGate.regular (g : SeededTree.ParamGate X) (x : X) : Prop :=
  match g with
  | .mixer f => AnalyticAt ℝ f x
  | .cost f => AnalyticAt ℝ f x
  | .seed f => ∀q, AnalyticAt ℝ (f q) x

def evalWord (w : List (SeededTree.ParamGate X)) (t : X) : List SeededTree.Gate :=
  w.map (fun g => g.eval t)

@[simp] theorem rootEquiv_symm_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ unitary _) (v : Level n) :
    (rootEquiv n A hA).symm v=root n A.conjTranspose v :=
  SpinOperators.actEquiv_symm_apply A hA v

 

theorem seed_topRegular (n : ℕ) (f : Fin 2 → X → ℝ) (hf : ∀q, AnalyticAt ℝ (f q) x) :
    TopRegular x n (fun t => external n (WithLp.toLp 2 (fun q => -(f q t:ℂ)))) :=
  TopRegular.external n _ (fun q => ((Complex.ofRealCLM.analyticAt _).comp (hf q)).neg)

 

theorem circuit_packetRegular (w : List (SeededTree.ParamGate X))
    (hw : ∀g∈w, g.regular x) : ∀n,
    (∀v : X → Level n, PacketRegular x n v →
      PacketRegular x n (fun t => (circuit (evalWord w t) n).op (v t))) ∧
    (∀v : X → Level n, PacketRegular x n v →
      PacketRegular x n (fun t => (circuit (evalWord w t) n).op.symm (v t))) := by
  induction w with
  | nil =>
    intro n
    constructor <;> intro v hv <;> exact hv
  | cons g w ih =>
    have hg : g.regular x := hw g (by simp)
    have hw' : ∀g∈w, g.regular x := fun g hg => hw g (by simp [hg])
    have ih' := ih hw'
    intro n
    cases g with
    | mixer f =>
      change AnalyticAt ℝ f x at hg
      constructor
      · intro v hv
        change PacketRegular x n (fun t => rootEquiv n (R (f t)) (R_unitary (f t))
          ((circuit (evalWord w t) n).op (v t)))
        simp only [SeededTree.rootEquiv_apply]
        exact PacketRegular.root n (PointedTree.analyticAt_R hg) ((ih' n).1 v hv)
      · intro v hv
        change PacketRegular x n (fun t => (circuit (evalWord w t) n).op.symm
          ((rootEquiv n (R (f t)) (R_unitary (f t))).symm (v t)))
        simp only [SeededTree.rootEquiv_symm_apply,R_star]
        exact (ih' n).2 _ (PacketRegular.root n (PointedTree.analyticAt_R hg.neg) hv)
    | seed f =>
      have hseed := seed_topRegular n f hg
      constructor
      · intro v hv
        change PacketRegular x n (fun t => WZ (external n (WithLp.toLp 2 (fun q => -(f q t:ℂ))))
          ((circuit (evalWord w t) n).op (v t)))
        exact PacketRegular.pulse n hseed ((ih' n).1 v hv)
      · intro v hv
        change PacketRegular x n (fun t => (circuit (evalWord w t) n).op.symm
          (WZ (-external n (WithLp.toLp 2 (fun q => -(f q t:ℂ)))) (v t)))
        exact (ih' n).2 _ (PacketRegular.pulse n (TopRegular.neg n hseed) hv)
    | cost f =>
      change AnalyticAt ℝ f x at hg
      cases n with
      | zero => exact ih' 0
      | succ n =>
        have hins : PacketRegular x n
            (fun t => ((circuit (evalWord w t) n).insertion : Level n)) :=
          (ih' n).2 _ (PacketRegular.root n (fun _ _ => analyticAt_const)
            ((ih' n).1 _ (PacketRegular.vac n)))
        have hd : TopRegular x (n+1) (fun t => (-(f t:ℂ)) •
            endogenous n (circuit (evalWord w t) n).insertion) :=
          TopRegular.smul (n+1) ((Complex.ofRealCLM.analyticAt _).comp hg).neg
            (TopRegular.endogenous n _ hins)
        constructor
        · intro v hv
          change PacketRegular x (n+1) (fun t => WZ
            ((-(f t:ℂ)) • endogenous n (circuit (evalWord w t) n).insertion)
            ((circuit (evalWord w t) (n+1)).op (v t)))
          exact PacketRegular.pulse (n+1) hd ((ih' (n+1)).1 v hv)
        · intro v hv
          change PacketRegular x (n+1) (fun t => (circuit (evalWord w t) (n+1)).op.symm
            (WZ (-((-(f t:ℂ)) • endogenous n (circuit (evalWord w t) n).insertion)) (v t)))
          exact (ih' (n+1)).2 _ (PacketRegular.pulse (n+1) (TopRegular.neg (n+1) hd) hv)

theorem circuit_insertion_packetRegular (w : List (SeededTree.ParamGate X))
    (hw : ∀g∈w, g.regular x) (n : ℕ) :
    PacketRegular x n (fun t => ((circuit (evalWord w t) n).insertion : Level n)) := by
  have h := circuit_packetRegular w hw n
  exact h.2 _ (PacketRegular.root n (fun _ _ => analyticAt_const)
    (h.1 _ (PacketRegular.vac n)))

theorem analyticAt_insertionGram (w u : List (SeededTree.ParamGate X))
    (hw : ∀g∈w, g.regular x) (hu : ∀g∈u, g.regular x) (n : ℕ) :
    AnalyticAt ℝ (fun t => ⟪(circuit (evalWord w t) n).insertion,
      (circuit (evalWord u t) n).insertion⟫_ℂ) x :=
  PacketRegular.inner n (circuit_insertion_packetRegular w hw n) (circuit_insertion_packetRegular u hu n)

end SeededTree

namespace CoherentFock
open PointedTree
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

@[simp] theorem spinMap_spinPacket {ι : Type*} [Fintype ι] (T : E →ₗᵢ[ℂ] F)
    (a : ι → Fin 2 → ℂ) (d : ι → E) :
    spinMap (gammaEmbedding T) (spinPacket a d)=spinPacket a (fun i => T (d i)) := by
  ext q
  simp only [spinMap_apply,spinPacket_apply,map_sum,map_smul,gammaEmbedding_coherent]

namespace PacketForm

theorem gamma {D : (X → E) → Prop} {D' : (X → F) → Prop} (T : E →ₗᵢ[ℂ] F)
    (hT : ∀d, D d → D' (fun t => T (d t))) {v : X → SpinSpace E}
    (hv : PacketForm x D v) :
    PacketForm x D' (fun t => spinMap (gammaEmbedding T) (v t)) := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  refine ⟨ι,hi,a,fun t i => T (d t i),ha,fun i => hT _ (hd i),?_⟩
  intro t
  dsimp only
  rw [hv,spinMap_spinPacket]

end PacketForm
end CoherentFock

namespace SeededTree
open PointedTree CoherentFock Complex RootSpin
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

 

theorem topStep_empty_regular (n : ℕ) :
    (∀d : X → TopMode n, TopRegular x n d →
      TopRegular x (n+1) (fun t => topStep n (d t))) ∧
    (∀v : X → Level n, PacketRegular x n v →
      PacketRegular x (n+1) (fun t => (empty n).toLinearIsometry (v t))) := by
  induction n with
  | zero =>
    have ht : ∀d : X → TopMode 0, TopRegular x 0 d →
        TopRegular x 1 (fun t => topStep 0 (d t)) := by
      intro d hd
      exact TopRegular.external 1 d hd
    refine ⟨ht,?_⟩
    intro v hv
    change PacketForm x (TopRegular x 1) (fun t => (SeededTree.empty 0).toLinearIsometry (v t))
    exact PacketForm.gamma (topStep 0) ht hv
  | succ n ih =>
    have ht : ∀d : X → TopMode (n+1), TopRegular x (n+1) d →
        TopRegular x (n+2) (fun t => topStep (n+1) (d t)) := by
      intro d hd
      refine ⟨hd.1,?_⟩
      exact ih.2 (fun t => ((d t).snd : Level n)) hd.2
    refine ⟨ht,?_⟩
    intro v hv
    change PacketForm x (TopRegular x (n+2)) (fun t => (SeededTree.empty (n+1)).toLinearIsometry (v t))
    exact PacketForm.gamma (topStep (n+1)) ht hv

namespace PacketRegular

theorem empty (n : ℕ) {v : X → Level n} (hv : PacketRegular x n v) :
    PacketRegular x (n+1) (fun t => (SeededTree.empty n).toLinearIsometry (v t)) :=
  (topStep_empty_regular n).2 _ hv

theorem finsetSum {ι : Type*} (n : ℕ) (s : Finset ι) (v : ι → X → Level n)
    (hv : ∀i∈s, PacketRegular x n (v i)) :
    PacketRegular x n (fun t => ∑i∈s, v i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (x := x) n
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact add n (hv i (by simp)) (ih (fun j hj => hv j (by simp [hj])))

end PacketRegular

 

theorem analyticAt_treeEnergy (n : ℕ) (d : X → Mode n)
    (hd : PacketRegular x n (fun t => (d t:Level n))) :
    AnalyticAt ℝ (fun t => treeEnergy n (d t)) x := by
  have he := PacketRegular.empty n hd
  obtain ⟨ι,hi,a,e,ha,he,hpres⟩ := he
  let := hi
  have hinner : AnalyticAt ℝ (fun t => ⟪(SeededTree.empty n).toLinearIsometry (d t),
      plusEmbedding (creationVacuum (endogenous n (d t)))⟫_ℂ) x := by
    simp_rw [hpres]
    exact analyticAt_inner_spinPacket_creation a e (fun t => endogenous n (d t)) ha
      (fun i => TopRegular.inner (n+1) (he i) (he i))
      (fun i => TopRegular.inner (n+1) (he i) (TopRegular.endogenous n d hd))
  exact (Complex.reCLM.analyticAt _).comp hinner

theorem analyticAt_value (w : List (SeededTree.ParamGate X)) (hw : ∀g∈w, g.regular x) :
    AnalyticAt ℝ (fun t => value (evalWord w t)) x := by
  have h := analyticAt_treeEnergy w.length
    (fun t => (circuit (evalWord w t) w.length).insertion)
    (circuit_insertion_packetRegular w hw w.length)
  have hl (t : X) : (evalWord w t).length=w.length := by simp [evalWord]
  convert h using 1
  ext t
  rw [SeededTree.value,hl t]

 
def centerAccumulator {k : ℕ} (n : ℕ) (w : Fin k → List (SeededTree.ParamGate X))
    (t : Fin k → X → ℝ) (u : X) : Mode n :=
  ∑j, (-2*(t j u:ℂ)) • (circuit (evalWord (w j) u) n).insertion

theorem centerAccumulator_packetRegular {k : ℕ} (n : ℕ)
    (w : Fin k → List (SeededTree.ParamGate X)) (t : Fin k → X → ℝ)
    (hw : ∀j g, g∈w j → g.regular x) (ht : ∀j, AnalyticAt ℝ (t j) x) :
    PacketRegular x n (fun u => (centerAccumulator n w t u : Level n)) := by
  unfold centerAccumulator
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  apply PacketRegular.finsetSum n Finset.univ
  intro j hj
  exact PacketRegular.smul n
    ((show AnalyticAt ℝ (fun _ : X => (-2:ℂ)) x from analyticAt_const).mul
      ((Complex.ofRealCLM.analyticAt _).comp (ht j)))
    (circuit_insertion_packetRegular (w j) (hw j) n)

 

def formalVisibility {k : ℕ} (n : ℕ) (b z y : ℝ) (w : List (SeededTree.ParamGate X))
    (prefixes : Fin k → List (SeededTree.ParamGate X)) (times : Fin k → X → ℝ) (u : X) : ℝ :=
  -2*(⟪(circuit (evalWord w u) n).insertion,
    (-2*b*z:ℂ) • (EvenUnitary.ident n).insertion +
      (y:ℂ) • centerAccumulator n prefixes times u⟫_ℂ).im

theorem analyticAt_formalVisibility {k : ℕ} (n : ℕ) (b z y : ℝ)
    (w : List (SeededTree.ParamGate X)) (prefixes : Fin k → List (SeededTree.ParamGate X))
    (times : Fin k → X → ℝ) (hw : ∀g∈w, g.regular x)
    (hp : ∀j g, g∈prefixes j → g.regular x) (ht : ∀j, AnalyticAt ℝ (times j) x) :
    AnalyticAt ℝ (formalVisibility n b z y w prefixes times) x := by
  have he : PacketRegular x n (fun _ : X => ((EvenUnitary.ident n).insertion : Level n)) :=
    circuit_insertion_packetRegular [] (by simp) n
  have hc := centerAccumulator_packetRegular n prefixes times hp ht
  have hv := PacketRegular.inner n (circuit_insertion_packetRegular w hw n)
    (PacketRegular.add n (PacketRegular.smul n (z := fun _ : X => (-2*b*z:ℂ)) analyticAt_const he)
      (PacketRegular.smul n (z := fun _ : X => (y:ℂ)) analyticAt_const hc))
  exact (show AnalyticAt ℝ (fun _ : X => (-2:ℝ)) x from analyticAt_const).mul
    ((Complex.imCLM.analyticAt _).comp hv)

end SeededTree

namespace SeededTree
open PointedTree CoherentFock Complex RootSpin

@[ext] theorem EvenUnitary.ext {n : ℕ} {U V : EvenUnitary n} (h : U.op=V.op) : U=V := by
  cases U
  cases V
  cases h
  rfl

@[simp] theorem EvenUnitary.followedBy_ident {n : ℕ} (U : EvenUnitary n) :
    U.followedBy (ident n)=U := by
  apply EvenUnitary.ext
  ext v
  rfl

@[simp] theorem EvenUnitary.mixer_zero (n : ℕ) : mixer n 0=ident n := by
  apply EvenUnitary.ext
  apply LinearIsometryEquiv.ext
  intro v
  change SpinOperators.act (R 0) v=v
  rw [R_zero,SpinOperators.act_one]
  rfl

@[simp] theorem EvenUnitary.seed_zero (n : ℕ) : seed n (fun _ => 0)=ident n := by
  apply EvenUnitary.ext
  apply LinearIsometryEquiv.ext
  intro v
  change WZ (external n (WithLp.toLp 2 (fun _ : Fin 2 => -(0:ℂ)))) v=v
  have hz : WithLp.toLp 2 (fun _ : Fin 2 => -(0:ℂ))=(0:External) := by ext q; simp
  rw [hz,map_zero,WZ_zero]
  rfl

@[simp] theorem EvenUnitary.cost_zero (n : ℕ) (U : EvenUnitary n) : cost n U 0=ident (n+1) := by
  apply EvenUnitary.ext
  apply LinearIsometryEquiv.ext
  intro v
  change WZ (-(0:ℂ) • endogenous n U.insertion) v=v
  rw [neg_zero,zero_smul,WZ_zero]
  rfl

def Gate.IsZero : SeededTree.Gate → Prop
  | .mixer b => b=0
  | .cost g => g=0
  | .seed a => ∀q, a q=0

 

theorem circuit_zero_prefix (w u : List SeededTree.Gate) (hw : ∀g∈w, Gate.IsZero g) (n : ℕ) :
    circuit (w++u) n=circuit u n := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g (by simp)
    have hw' : ∀g∈w, Gate.IsZero g := fun g hg => hw g (by simp [hg])
    cases g with
    | mixer b =>
      change b=0 at hg
      subst b
      change (circuit (w++u) n).followedBy (EvenUnitary.mixer n 0)=circuit u n
      rw [EvenUnitary.mixer_zero,EvenUnitary.followedBy_ident,ih hw']
    | seed a =>
      have ha : a=fun _ => 0 := funext hg
      subst a
      change (circuit (w++u) n).followedBy (EvenUnitary.seed n (fun _ => 0))=circuit u n
      rw [EvenUnitary.seed_zero,EvenUnitary.followedBy_ident,ih hw']
    | cost g =>
      change g=0 at hg
      subst g
      cases n with
      | zero => exact ih hw'
      | succ n =>
        change (circuit (w++u) (n+1)).followedBy (EvenUnitary.cost n (circuit (w++u) n) 0)=circuit u (n+1)
        rw [EvenUnitary.cost_zero,EvenUnitary.followedBy_ident,ih hw']

 
def ell : External := EuclideanSpace.single 0 1
@[simp] theorem norm_ell : ‖ell‖=1 := by simp [ell]

def initializationAngles (b : ℝ) : Fin 2 → ℝ := fun q => if q=0 then -2*b else 0

def initializationDisplacement (n : ℕ) (b : ℝ) : TopMode n :=
  external n (WithLp.toLp 2 (fun q => -(initializationAngles b q:ℂ)))

theorem initializationDisplacement_eq (n : ℕ) (b : ℝ) :
    initializationDisplacement n b=(2*b:ℂ) • external n ell := by
  unfold initializationDisplacement
  rw [←map_smul]
  congr 1
  ext q
  fin_cases q <;> simp [initializationAngles,ell,EuclideanSpace.single]

theorem initializationDisplacement_norm_sq (n : ℕ) (b : ℝ) :
    ‖initializationDisplacement n b‖^2=4*b^2 := by
  rw [initializationDisplacement_eq,norm_smul,(external n).norm_map,norm_ell,mul_one]
  norm_cast
  rw [Real.norm_eq_abs,sq_abs]
  ring

def initializationWord (b : ℝ) : List SeededTree.Gate :=
  [.mixer (Real.pi/4),.seed (initializationAngles b)]

 
theorem initialization_insertion_coe (n : ℕ) (b : ℝ) :
    ((circuit (initializationWord b) n).insertion : Level n)=
      SpinOperators.act Y (WZ (initializationDisplacement n b+initializationDisplacement n b) (vac n)) := by
  change (costEquiv (initializationDisplacement n b)).symm
    ((SpinOperators.actEquiv (R (Real.pi/4)) (R_unitary (Real.pi/4))).symm
      (SpinOperators.act Z (SpinOperators.actEquiv (R (Real.pi/4)) (R_unitary (Real.pi/4))
        (costEquiv (initializationDisplacement n b) (vac n)))))=_
  simp only [costEquiv_symm_apply,SpinOperators.actEquiv_symm_apply,
    SpinOperators.actEquiv_apply,costEquiv_apply]
  rw [one_layer_insertion,show 2*(Real.pi/4)=Real.pi/2 by ring]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,one_smul,zero_add]

 

theorem inner_initialization_initial (n : ℕ) (b : ℝ) :
    ⟪(circuit (initializationWord b) n).insertion,(EvenUnitary.ident n).insertion⟫_ℂ=
      I*(Real.exp (-8*b^2):ℂ) := by
  change ⟪((circuit (initializationWord b) n).insertion:Level n),SpinOperators.act Z (vac n)⟫_ℂ=_
  rw [initialization_insertion_coe,←inner_conj_symm]
  change (starRingEnd ℂ) ⟪SpinOperators.act Z (vacuum (TopMode n)),
    SpinOperators.act Y (WZ (initializationDisplacement n b+initializationDisplacement n b)
      (vacuum (TopMode n)))⟫_ℂ=_
  rw [inner_rootZ_vac_rootY_WZ]
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  have hn : ‖initializationDisplacement n b+initializationDisplacement n b‖^2=16*b^2 := by
    rw [←two_smul ℝ (initializationDisplacement n b),norm_smul,
      Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),mul_pow,initializationDisplacement_norm_sq]
    ring
  have he : -‖initializationDisplacement n b+initializationDisplacement n b‖^2/2= -8*b^2 := by
    rw [hn]
    ring
  rw [he]

end SeededTree

namespace SeededTree
open PointedTree CoherentFock Complex RootSpin
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

 

def initializationParam (b : ℝ) : List (SeededTree.ParamGate X) :=
  [.mixer (fun _ => Real.pi/4),.seed (fun q _ => initializationAngles b q)]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
@[simp] theorem eval_initializationParam (b : ℝ) (x : X) :
    evalWord (initializationParam b) x=initializationWord b := rfl

theorem initializationParam_regular (b : ℝ) (x : X) :
    ∀g∈initializationParam b, g.regular x := by
  intro g hg
  simp only [initializationParam,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl
  · exact analyticAt_const
  · exact fun _ => analyticAt_const

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
@[simp] theorem evalWord_append (w u : List (SeededTree.ParamGate X)) (x : X) :
    evalWord (w++u) x=evalWord w x++evalWord u x := List.map_append

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem centerAccumulator_zero {k : ℕ} (n : ℕ) (w : Fin k → List (SeededTree.ParamGate X))
    (times : Fin k → X → ℝ) (x : X) (ht : ∀j, times j x=0) :
    centerAccumulator n w times x=0 := by
  simp [centerAccumulator,ht]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
 

theorem formalVisibility_initialization {k : ℕ} (n : ℕ) (b z y : ℝ)
    (w : List (SeededTree.ParamGate X)) (prefixes : Fin k → List (SeededTree.ParamGate X))
    (times : Fin k → X → ℝ) (x : X)
    (hw : ∀g∈evalWord w x, Gate.IsZero g) (ht : ∀j, times j x=0) :
    formalVisibility n b z y (w++initializationParam b) prefixes times x=
      4*b*z*Real.exp (-8*b^2) := by
  unfold formalVisibility
  rw [evalWord_append,eval_initializationParam,circuit_zero_prefix _ _ hw,
    centerAccumulator_zero n prefixes times x ht,smul_zero,add_zero,inner_smul_right,
    inner_initialization_initial]
  have hc : (-2*b*z:ℂ)=((-2*b*z:ℝ):ℂ) := by simp
  rw [hc]
  simp only [Complex.mul_im,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,zero_add,add_zero]
  ring

 

inductive IndexedGate (M : ℕ)
  | mixer (i : Fin M)
  | cost (i : Fin M)
  | seed (i : Fin M)

def IndexedGate.param {M : ℕ} : IndexedGate M → SeededTree.ParamGate (Fin M → ℝ)
  | .mixer i => .mixer (fun t => t i)
  | .cost i => .cost (fun t => t i)
  | .seed i => .seed (fun q t => if q=0 then 0 else t i)

theorem IndexedGate.param_regular {M : ℕ} (g : IndexedGate M) (x : Fin M → ℝ) :
    g.param.regular x := by
  have h (i : Fin M) : AnalyticAt ℝ (fun t : Fin M → ℝ => t i) x :=
    (ContinuousLinearMap.proj i : (Fin M → ℝ) →L[ℝ] ℝ).analyticAt _
  cases g with
  | mixer i => exact h i
  | cost i => exact h i
  | seed i =>
    intro q
    change AnalyticAt ℝ (fun t : Fin M → ℝ => if q=0 then 0 else t i) x
    split_ifs
    · exact analyticAt_const
    · exact h i

theorem IndexedGate.param_zero {M : ℕ} (g : IndexedGate M) :
    Gate.IsZero (g.param.eval 0) := by
  cases g <;> simp [IndexedGate.param,ParamGate.eval,Gate.IsZero]

def indexedWord {M : ℕ} (w : List (IndexedGate M)) : List (SeededTree.ParamGate (Fin M → ℝ)) :=
  w.map IndexedGate.param

theorem indexedWord_regular {M : ℕ} (w : List (IndexedGate M)) (x : Fin M → ℝ) :
    ∀g∈indexedWord w, g.regular x := by
  intro g hg
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg
  exact g.param_regular x

theorem indexedWord_zero {M : ℕ} (w : List (IndexedGate M)) :
    ∀g∈evalWord (indexedWord w) 0, Gate.IsZero g := by
  intro g hg
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact q.param_zero

 
def indexedTime {M : ℕ} (i : Fin M) (x : Fin M → ℝ) : ℝ := x i/2

theorem indexedTime_regular {M : ℕ} (i : Fin M) (x : Fin M → ℝ) :
    AnalyticAt ℝ (indexedTime i) x :=
  ((ContinuousLinearMap.proj i : (Fin M → ℝ) →L[ℝ] ℝ).analyticAt _).div_const

@[simp] theorem indexedTime_zero {M : ℕ} (i : Fin M) : indexedTime i 0=0 := by
  simp [indexedTime]

 
theorem indexedVisibility_zero {M k : ℕ} (n : ℕ) (b z y : ℝ)
    (w : List (IndexedGate M))
    (prefixes : Fin k → List (SeededTree.ParamGate (Fin M → ℝ))) (times : Fin k → Fin M) :
    formalVisibility n b z y (indexedWord w++initializationParam b) prefixes
      (fun j => indexedTime (times j)) 0=4*b*z*Real.exp (-8*b^2) :=
  formalVisibility_initialization n b z y (indexedWord w) prefixes _ 0
    (indexedWord_zero w) (fun j => indexedTime_zero (times j))

end SeededTree

namespace SeededTree
open PointedTree CoherentFock Complex RootSpin

 

theorem exists_visible_perturbation {M k : ℕ} {ι : Type*} [Finite ι]
    (n : ℕ) (b : ℝ) (hb : 0<b) (z y : ι → ℝ) (hz : ∀s, z s≠0)
    (stages : ι → List (IndexedGate M))
    (prefixes : ι → Fin k → List (IndexedGate M)) (times : ι → Fin k → Fin M)
    (echoes : List (Fin M)) (target : List (IndexedGate M)) (x : Fin M → ℝ)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃u : Fin M → ℝ, dist u x<δ ∧
      |value (evalWord (indexedWord target++initializationParam b) u)-
        value (evalWord (indexedWord target++initializationParam b) x)|<ε ∧
      (∀s, formalVisibility n b (z s) (y s)
        (indexedWord (stages s)++initializationParam b)
        (fun j => indexedWord (prefixes s j)++initializationParam b)
        (fun j => indexedTime (times s j)) u≠0) ∧
      (∀i∈echoes, indexedTime i u≠0) := by
  classical
  let f : (ι ⊕ {i : Fin M // i∈echoes}) → (Fin M → ℝ) → ℝ := fun s =>
    match s with
    | .inl s => formalVisibility n b (z s) (y s)
        (indexedWord (stages s)++initializationParam b)
        (fun j => indexedWord (prefixes s j)++initializationParam b)
        (fun j => indexedTime (times s j))
    | .inr i => indexedTime i.1
  have hreg (w : List (IndexedGate M)) (v : Fin M → ℝ) :
      ∀g∈indexedWord w++initializationParam b, g.regular v := by
    intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact indexedWord_regular w v g hg
    · exact initializationParam_regular b v g hg
  have hf : ∀s, AnalyticOnNhd ℝ (f s) Set.univ := by
    intro s v hv
    cases s with
    | inl s =>
      exact analyticAt_formalVisibility (X := Fin M → ℝ) (x := v) n b (z s) (y s) _ _ _
        (hreg (stages s) v) (fun j => hreg (prefixes s j) v)
        (fun j => indexedTime_regular (times s j) v)
    | inr i => exact indexedTime_regular i.1 v
  have hn : ∀s, ∃u, f s u≠0 := by
    intro s
    cases s with
    | inl s =>
      refine ⟨0,?_⟩
      change formalVisibility _ _ _ _ _ _ _ 0≠0
      rw [indexedVisibility_zero]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb.ne') (hz s))
        (Real.exp_ne_zero _)
    | inr i =>
      refine ⟨fun _ => 2,?_⟩
      norm_num [f,indexedTime]
  have he := (analyticAt_value (indexedWord target++initializationParam b) (hreg target x)).continuousAt
  obtain ⟨u,hu,he,hf⟩ := AnalyticVisibility.exists_perturbation f hf hn
    (fun v => value (evalWord (indexedWord target++initializationParam b) v)) x he hε hδ
  refine ⟨u,hu,he,fun s => hf (.inl s),?_⟩
  intro i hi
  exact hf (.inr ⟨i,hi⟩)

end SeededTree

namespace SeededTree
open PointedTree CoherentFock Complex RootSpin

 

def ordinaryLift : (n : ℕ) → PointedMap (PointedTree.level n) (SeededTree.level n)
  | 0 => ⟨spinMap (scalarEmbedding (coherent (0:External)) (norm_coherent _)),rfl⟩
  | n+1 => gaussianMap ((endogenous n).comp (centeredMap (ordinaryLift n)))

@[simp] theorem ordinaryLift_vac (n : ℕ) :
    (ordinaryLift n).toLinearIsometry (PointedTree.vac n)=SeededTree.vac n :=
  (ordinaryLift n).map_vac

@[simp] theorem ordinaryLift_root (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : PointedTree.Level n) :
    (ordinaryLift n).toLinearIsometry (PointedTree.root n A v)=
      SeededTree.root n A ((ordinaryLift n).toLinearIsometry v) := by
  cases n <;> exact spinMap_root _ _ _

@[simp] theorem ordinaryLift_cost (n : ℕ) (d : PointedTree.Mode n) (v : PointedTree.Level (n+1)) :
    (ordinaryLift (n+1)).toLinearIsometry (WZ d v)=
      WZ (endogenous n (centeredMap (ordinaryLift n) d))
        ((ordinaryLift (n+1)).toLinearIsometry v) :=
  spinMap_cost ((endogenous n).comp (centeredMap (ordinaryLift n))) d v

 
def LiftCompatible {n : ℕ} (U : PointedTree.EvenUnitary n) (V : SeededTree.EvenUnitary n) : Prop :=
  ∀v, (ordinaryLift n).toLinearIsometry (U.op v)=V.op ((ordinaryLift n).toLinearIsometry v)

theorem LiftCompatible.symm_apply {n : ℕ} {U : PointedTree.EvenUnitary n} {V : SeededTree.EvenUnitary n}
    (h : LiftCompatible U V) (v : PointedTree.Level n) :
    (ordinaryLift n).toLinearIsometry (U.op.symm v)=V.op.symm ((ordinaryLift n).toLinearIsometry v) := by
  apply V.op.injective
  rw [←h,U.op.apply_symm_apply,V.op.apply_symm_apply]

theorem LiftCompatible.insertion {n : ℕ} {U : PointedTree.EvenUnitary n} {V : SeededTree.EvenUnitary n}
    (h : LiftCompatible U V) : centeredMap (ordinaryLift n) U.insertion=V.insertion := by
  apply Subtype.ext
  change (ordinaryLift n).toLinearIsometry (U.op.symm
    (PointedTree.root n Z (U.op (PointedTree.vac n))))=
      V.op.symm (SeededTree.root n Z (V.op (SeededTree.vac n)))
  rw [h.symm_apply,ordinaryLift_root,h,ordinaryLift_vac]

 
def ordinaryGate : PointedTree.Gate → SeededTree.Gate
  | .mixer b => .mixer b
  | .cost g => .cost g

def ordinaryWord (w : List PointedTree.Gate) : List SeededTree.Gate := w.map ordinaryGate

@[simp] theorem ordinaryWord_length (w : List PointedTree.Gate) : (ordinaryWord w).length=w.length := by
  simp [ordinaryWord]

 

theorem circuit_ordinaryLift (w : List PointedTree.Gate) (n : ℕ) :
    LiftCompatible (PointedTree.ordinary w n) (circuit (ordinaryWord w) n) := by
  induction w generalizing n with
  | nil => exact fun _ => rfl
  | cons g w ih =>
    cases g with
    | mixer b =>
      intro v
      change (ordinaryLift n).toLinearIsometry
        (PointedTree.rootEquiv n (R b) (R_unitary b) ((PointedTree.ordinary w n).op v))=
          SeededTree.rootEquiv n (R b) (R_unitary b) ((circuit (ordinaryWord w) n).op ((ordinaryLift n).toLinearIsometry v))
      rw [PointedTree.rootEquiv_apply,SeededTree.rootEquiv_apply,ordinaryLift_root,ih n]
    | cost g =>
      cases n with
      | zero => exact ih 0
      | succ n =>
        intro v
        change (ordinaryLift (n+1)).toLinearIsometry
          (WZ (-(g:ℂ) • (PointedTree.ordinary w n).insertion)
            ((PointedTree.ordinary w (n+1)).op v))=
          WZ (-(g:ℂ) • endogenous n (circuit (ordinaryWord w) n).insertion)
            ((circuit (ordinaryWord w) (n+1)).op ((ordinaryLift (n+1)).toLinearIsometry v))
        rw [ordinaryLift_cost,map_smul,map_smul,(ih n).insertion,ih (n+1)]

@[simp] theorem ordinaryLift_rootShift (n : ℕ) (d : PointedTree.Mode n) :
    centeredMap (ordinaryLift (n+1)) (PointedTree.rootShift n d)=
      rootShift n (centeredMap (ordinaryLift n) d) := by
  apply Subtype.ext
  change spinMap (gammaEmbedding ((endogenous n).comp (centeredMap (ordinaryLift n))))
    (plusEmbedding (creationVacuum d))=
      plusEmbedding (creationVacuum (endogenous n (centeredMap (ordinaryLift n) d)))
  rw [spinMap_plusEmbedding]
  change plusEmbedding (Gamma ((endogenous n).comp (centeredMap (ordinaryLift n))) (creationVacuum d))=_
  rw [Gamma_creationVacuum]
  rfl

 
theorem value_ordinaryWord (w : List PointedTree.Gate) :
    value (ordinaryWord w)=PointedTree.ordinaryValue w := by
  rw [value,ordinaryWord_length,PointedTree.ordinaryValue,treeEnergy,PointedTree.treeEnergy,
    circuit_insertion_empty _ w.length (by simp),PointedTree.ordinary_insertion_empty _ w.length le_rfl]
  rw [←(circuit_ordinaryLift w (w.length+1)).insertion,
    ←(circuit_ordinaryLift w w.length).insertion,←ordinaryLift_rootShift]
  exact congrArg Complex.re ((centeredMap (ordinaryLift (w.length+1))).inner_map_map _ _)

end SeededTree

end

end OAI
