import Mathlib
import OAI.Probability.ParisiFinite.NegativeFlip

namespace OAI

/-! Energy. -/

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
namespace SeedInitialization.CausalFrame
open CoherentFock PointedTree GramCalculus
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

 

theorem energy (f : CausalFrame b n κ) (i : κ) :
    Tendsto (fun T => energyInfinity (f.actual T i)) atTop
      (𝓝 (SeededTree.treeEnergy n (f.formal i))) := by
  have hn : Tendsto (fun T => ‖f.actual T i‖) atTop
      (𝓝 ‖SeededTree.endogenous n (f.formal i)‖) := by
    have hh := (f.packet i).norm f.gram
    simp only [modeFock.norm_map,LinearIsometry.norm_map] at hh ⊢
    exact hh
  have hc := (f.packet i).creation f.gram (fun T => f.actual T i)
    (SeededTree.endogenous n (f.formal i))
    (fun j => f.gram j (Sum.inr i)) hn
  have hr := (Complex.continuous_re.tendsto _).comp hc
  change Tendsto (fun T => energyInfinity (f.actual T i)) atTop
    (𝓝 (⟪(SeededTree.empty n).toLinearIsometry (f.formal i : SeededTree.Level n),
      plusEmbedding (creationVacuum (SeededTree.endogenous n (f.formal i)))⟫_ℂ).re)
  simpa only [Function.comp_def,←energyInfinity_fock] using hr

end SeedInitialization.CausalFrame

 

open scoped InnerProductSpace Topology BigOperators
namespace GramCalculus
open CoherentFock PointedTree RootSpin

 

inductive TraceGate (κ : Type*)
  | mixer (beta : ℝ)
  | seed (angles : Fin 2 → ℝ)
  | cost (index : κ) (gamma : ℝ)

namespace TraceGate
variable {κ : Type*} [Fintype κ]

def forget : TraceGate κ → SeededTree.Gate
  | .mixer b => .mixer b
  | .seed a => .seed a
  | .cost _ c => .cost c

def coeffSeed (a : Fin 2 → ℝ) : Fin 2 ⊕ κ → ℂ :=
  Sum.elim (fun i => -(a i:ℂ)) (fun _ => 0)

def coeffCost (i : κ) (c : ℝ) : Fin 2 ⊕ κ → ℂ := by
  classical
  exact Pi.single (Sum.inr i) (-(c:ℂ))

def encode : TraceGate κ → WeylGate (Fin 2 ⊕ κ)
  | .mixer b => .root (R b) (R_unitary b)
  | .seed a => .pulse (coeffSeed a)
  | .cost i c => .pulse (coeffCost i c)

@[simp] theorem combination_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (d : Fin 2 ⊕ κ → E) (i : κ) (c : ℝ) :
    combination d (coeffCost i c)=-(c:ℂ) • d (Sum.inr i) := by
  classical
  simp [combination,coeffCost,Pi.single_apply]

 theorem basis_sum (a : Fin 2 → ℂ) :
    (∑i,a i • SeedInitialization.seedBasis i)=WithLp.toLp 2 a := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_two,SeedInitialization.seedBasis,EuclideanSpace.single]

@[simp] theorem combination_seed (n : ℕ) (d : κ → SeededTree.TopMode n) (a : Fin 2 → ℝ) :
    combination (Sum.elim (fun i => SeededTree.external n (SeedInitialization.seedBasis i)) d)
      (coeffSeed a)=SeededTree.external n (WithLp.toLp 2 (fun i => -(a i:ℂ))) := by
  rw [show coeffSeed (κ:=κ) a=Sum.elim (fun i => -(a i:ℂ)) 0 from rfl,combination_sum_zero]
  simp only [combination,←map_smul,←map_sum,basis_sum]

def reindex {ν : Type*} (f : κ → ν) : TraceGate κ → TraceGate ν
  | .mixer b => .mixer b
  | .seed a => .seed a
  | .cost i c => .cost (f i) c

end TraceGate
namespace TraceWord
variable {κ : Type*} [Fintype κ]

def forget (w : List (TraceGate κ)) : List SeededTree.Gate := w.map TraceGate.forget

def encode (w : List (TraceGate κ)) : List (WeylGate (Fin 2 ⊕ κ)) := w.map TraceGate.encode

 

def Valid (history : κ → List SeededTree.Gate) : List (TraceGate κ) → Prop
  | [] => True
  | .mixer _::w => Valid history w
  | .seed _::w => Valid history w
  | .cost i _::w => history i=forget w ∧ Valid history w

 

theorem op_model (w : List (TraceGate κ)) (history : κ → List SeededTree.Gate)
    (hv : Valid history w) (n : ℕ) :
    WeylWord.op
      (Sum.elim (fun i => SeededTree.external (n+1) (SeedInitialization.seedBasis i))
        (fun i => SeededTree.endogenous n (SeededTree.circuit (history i) n).insertion))
      (encode w)=(SeededTree.circuit (forget w) (n+1)).op := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    apply LinearIsometryEquiv.ext
    intro x
    cases g with
    | mixer beta =>
      have h := ih hv
      change SpinOperators.act (R beta) (WeylWord.op _ (encode w) x)=
        SpinOperators.act (R beta) ((SeededTree.circuit (forget w) (n+1)).op x)
      rw [h]
    | seed a =>
      have h := ih hv
      change WZ (combination _ (TraceGate.coeffSeed a)) (WeylWord.op _ (encode w) x)=
        WZ (SeededTree.external (n+1) (WithLp.toLp 2 (fun j => -(a j:ℂ))))
          ((SeededTree.circuit (forget w) (n+1)).op x)
      rw [TraceGate.combination_seed,h]
    | cost i c =>
      have h := ih hv.2
      change WZ (combination _ (TraceGate.coeffCost i c)) (WeylWord.op _ (encode w) x)=
        WZ (-(c:ℂ) • SeededTree.endogenous n (SeededTree.circuit (forget w) n).insertion)
          ((SeededTree.circuit (forget w) (n+1)).op x)
      rw [TraceGate.combination_cost,h]
      simp only [Sum.elim_inr,hv.1]

 
omit [Fintype κ] in
@[simp] theorem forget_reindex {ν : Type*} (f : κ → ν) (w : List (TraceGate κ)) :
    forget (w.map (TraceGate.reindex f))=forget w := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp_all [forget,TraceGate.reindex,TraceGate.forget]

omit [Fintype κ] in
 theorem valid_reindex {ν : Type*} (f : κ → ν) (w : List (TraceGate κ))
    (history : κ → List SeededTree.Gate) (history' : ν → List SeededTree.Gate)
    (h : ∀i,history' (f i)=history i) (hv : Valid history w) :
    Valid history' (w.map (TraceGate.reindex f)) := by
  induction w with
  | nil => trivial
  | cons g w ih =>
    cases g with
    | mixer b => exact ih hv
    | seed a => exact ih hv
    | cost i c =>
      exact ⟨by simpa only [forget_reindex,h] using hv.1,ih hv.2⟩

 

theorem op_reindex {ν E : Type*} [Fintype ν] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : κ → ν) (w : List (TraceGate κ)) (s : Fin 2 → E) (z : κ → E) (z' : ν → E)
    (hz : ∀i,z' (f i)=z i) :
    WeylWord.op (Sum.elim s z') (encode (w.map (TraceGate.reindex f)))=
      WeylWord.op (Sum.elim s z) (encode w) := by
  have hs (a : Fin 2 → ℝ) : combination (Sum.elim s z') (TraceGate.coeffSeed a)=
      combination (Sum.elim s z) (TraceGate.coeffSeed a) := by
    rw [show TraceGate.coeffSeed (κ:=ν) a=Sum.elim (fun i => -(a i:ℂ)) 0 from rfl,
      show TraceGate.coeffSeed (κ:=κ) a=Sum.elim (fun i => -(a i:ℂ)) 0 from rfl,
      combination_sum_zero,combination_sum_zero]
  induction w with
  | nil => rfl
  | cons g w ih =>
    apply LinearIsometryEquiv.ext
    intro x
    cases g with
    | mixer b =>
      change SpinOperators.act (R b) (WeylWord.op _ (encode (w.map _)) x)=
        SpinOperators.act (R b) (WeylWord.op _ (encode w) x)
      rw [ih]
    | seed a =>
      change WZ (combination _ (TraceGate.coeffSeed a)) (WeylWord.op _ (encode (w.map _)) x)=
        WZ (combination _ (TraceGate.coeffSeed a)) (WeylWord.op _ (encode w) x)
      rw [hs,ih]
    | cost i c =>
      change WZ (combination _ (TraceGate.coeffCost (f i) c)) (WeylWord.op _ (encode (w.map _)) x)=
        WZ (combination _ (TraceGate.coeffCost i c)) (WeylWord.op _ (encode w) x)
      simp only [TraceGate.combination_cost,Sum.elim_inr,hz,ih]

end TraceWord
end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus

 

structure TaggedFrame (b : ℝ) (n : ℕ) (κ : Type*) [Fintype κ] where
  frame : CausalFrame b n κ
  history : κ → List SeededTree.Gate
  length : ∀i,(history i).length≤n
  identifies : ∀i,frame.formal i=(SeededTree.circuit (history i) n).insertion

namespace TaggedFrame
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

def initial (b : ℝ) (hb : 0<b) (n : ℕ) : TaggedFrame b n PEmpty where
  frame := {
    actual := fun _ => PEmpty.elim
    formal := PEmpty.elim
    gram := by
      intro i j
      cases i with
      | inl i =>
        cases j with
        | inl j => simpa only [Sum.elim_inl,LinearIsometry.inner_map_map] using seedDirections_gram b hb i j
        | inr j => exact j.elim
      | inr i => exact i.elim
    bounded := fun i => i.elim
    packet := fun i => i.elim }
  history := PEmpty.elim
  length := fun i => i.elim
  identifies := fun i => i.elim

 

def append (f : TaggedFrame b n κ) (hb : 0<b)
    (z : ℝ → ModeInfinity) (w : List SeededTree.Gate) (hw : w.length≤n+1)
    (hz : ApproxPacket atTop (fun T => modeFock (z T)))
    (hm : ApproxMatch atTop f.frame.directions f.frame.model (fun T => modeFock (z T))
      ((SeededTree.circuit w (n+1)).insertion : SeededTree.Level (n+1))) :
    TaggedFrame b (n+1) (κ ⊕ Unit) where
  frame := f.frame.append hb z (SeededTree.circuit w (n+1)).insertion hz hm
  history := Sum.elim f.history (fun _ => w)
  length i := by
    cases i with
    | inl i => exact (f.length i).trans (Nat.le_succ n)
    | inr i => exact hw
  identifies i := by
    cases i with
    | inl i =>
      change centeredMap (SeededTree.empty n) (f.frame.formal i)=
        (SeededTree.circuit (f.history i) (n+1)).insertion
      rw [f.identifies,SeededTree.circuit_insertion_empty _ _ (f.length i)]
    | inr i => rfl

 

theorem op_model (f : TaggedFrame b n κ) (w : List (TraceGate κ))
    (hv : TraceWord.Valid f.history w) :
    WeylWord.op f.frame.model (TraceWord.encode w)=
      (SeededTree.circuit (TraceWord.forget w) (n+1)).op := by
  have h : f.frame.model=Sum.elim
      (fun i => SeededTree.external (n+1) (seedBasis i))
      (fun i => SeededTree.endogenous n (SeededTree.circuit (f.history i) n).insertion) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact congrArg (SeededTree.endogenous n) (f.identifies i)
  rw [h]
  exact TraceWord.op_model w f.history hv n

 

def record {ι : Type*} [Fintype ι] (f : TaggedFrame b n κ) (hb : 0<b)
    {centers : ι → ℝ → ModeInfinity} {spin : ι → Fin 2}
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) centers spin)
    (w : List (TraceGate κ)) (hv : TraceWord.Valid f.history w)
    (hw : (TraceWord.forget w).length≤n+1)
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family (TraceWord.encode w) f.frame.gram))
    (hr : Tendsto amplitude atTop (𝓝 0)) (hp : ∀ᶠ T in atTop,0<amplitude T) :
    TaggedFrame b (n+1) (κ ⊕ Unit) := by
  refine f.append hb (fun T => insertionInfinity (st.word T)) (TraceWord.forget w) hw
    (st.insertionZ_approx hr hp) ?_
  have h := st.insertionZ_match (TraceWord.encode w) f.frame.gram hc hr hp
  have he := f.op_model w hv
  simp only [CausalFrame.model] at he
  rw [he] at h
  exact h

end TaggedFrame
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

namespace PacketMatch
variable {d : α → ι → E} {d₀ : ι → F} {x y : α → SpinSpace E} {x₀ y₀ : SpinSpace F}

theorem zero : PacketMatch l d d₀ (fun _ => 0) 0 := by
  refine ⟨0,fun _ i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,?_,?_⟩
  · intro q; ext j; simp [spinPacket_apply]
  · ext j; simp [spinPacket_apply]
  · intro i; exact Fin.elim0 i

theorem add (hx : PacketMatch l d d₀ x x₀) (hy : PacketMatch l d d₀ y y₀) :
    PacketMatch l d d₀ (fun q => x q+y q) (x₀+y₀) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  obtain ⟨m,b,b₀,e,hy,hy₀,hb⟩ := hy
  let f : Fin (n+m) ≃ Fin n ⊕ Fin m := finSumFinEquiv.symm
  refine ⟨n+m,fun q i => Sum.elim (a q) (b q) (f i),fun i => Sum.elim a₀ b₀ (f i),
    fun i => Sum.elim c e (f i),?_,?_,?_⟩
  · intro q
    dsimp only
    have hd : (fun i => combination (d q) (Sum.elim c e i))=
        Sum.elim (fun i => combination (d q) (c i)) (fun i => combination (d q) (e i)) := by
      funext i; cases i <;> rfl
    rw [spinPacket_reindex f (Sum.elim (a q) (b q)) (fun i => combination (d q) (Sum.elim c e i)),
      hd,←spinPacket_sum,hx,hy]
  · have hd : (fun i => combination d₀ (Sum.elim c e i))=
        Sum.elim (fun i => combination d₀ (c i)) (fun i => combination d₀ (e i)) := by
      funext i; cases i <;> rfl
    rw [spinPacket_reindex f (Sum.elim a₀ b₀) (fun i => combination d₀ (Sum.elim c e i)),
      hd,←spinPacket_sum,hx₀,hy₀]
  · intro i j
    cases h : f i with
    | inl k => simpa only [h,Sum.elim_inl] using ha k j
    | inr k => simpa only [h,Sum.elim_inr] using hb k j

end PacketMatch
namespace ApproxMatch
variable {d : α → ι → E} {d₀ : ι → F} {x y : α → SpinSpace E} {x₀ y₀ : SpinSpace F}

theorem zero : ApproxMatch l d d₀ (fun _ => 0) 0 := PacketMatch.zero.approx

theorem add (hx : ApproxMatch l d d₀ x x₀) (hy : ApproxMatch l d d₀ y y₀) :
    ApproxMatch l d d₀ (fun q => x q+y q) (x₀+y₀) := by
  obtain ⟨x',hx',he⟩ := hx
  obtain ⟨y',hy',hf⟩ := hy
  refine ⟨fun q => x' q+y' q,hx'.add hy',?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using he.add hf)
  exact Eventually.of_forall fun q => by
    rw [show x q+y q-(x' q+y' q)=(x q-x' q)+(y q-y' q) by abel]
    exact norm_add_le _ _

theorem smul (hx : ApproxMatch l d d₀ x x₀) (z : ℂ) :
    ApproxMatch l d d₀ (fun q => z • x q) (z • x₀) := by
  obtain ⟨y,hy,he⟩ := hx
  refine ⟨fun q => z • y q,hy.smul z,?_⟩
  simpa only [←smul_sub,norm_smul,mul_zero] using he.const_mul ‖z‖

theorem finSum {κ : Type*} [Fintype κ] (x : κ → α → SpinSpace E) (x₀ : κ → SpinSpace F)
    (hx : ∀i,ApproxMatch l d d₀ (x i) (x₀ i)) :
    ApproxMatch l d d₀ (fun q => ∑i,x i q) (∑i,x₀ i) := by
  classical
  have h (s : Finset κ) : ApproxMatch l d d₀ (fun q => ∑i∈s,x i q) (∑i∈s,x₀ i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (zero (l:=l) (d:=d) (d₀:=d₀))
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hx i).add ih
  exact h Finset.univ

end ApproxMatch
end GramCalculus

namespace SeedInitialization.CausalFrame
open CoherentFock PointedTree GramCalculus
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

 

theorem combination_packet (f : CausalFrame b n κ) (c : κ → ℂ) :
    ApproxMatch atTop f.directions f.model
      (fun T => modeFock (combination (f.actual T) c))
      ((SeededTree.empty n).toLinearIsometry
        (combination (fun i => (f.formal i : SeededTree.Level n)) c)) := by
  unfold CausalFrame.directions CausalFrame.model
  simp only [combination,map_sum,map_smul]
  exact ApproxMatch.finSum (fun i T => c i • modeFock (f.actual T i))
      (fun i => c i • (SeededTree.empty n).toLinearIsometry (f.formal i : SeededTree.Level n))
      (fun i => (f.packet i).smul (c i))

end SeedInitialization.CausalFrame

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

@[simp] theorem amplitude_inverse (T : ℝ) : (amplitude T)⁻¹=T := inv_inv T

theorem amplitude_zero : Tendsto amplitude atTop (𝓝 0) := tendsto_inv_atTop_zero

theorem amplitude_eventually_pos : ∀ᶠ T : ℝ in atTop,0<amplitude T :=
  (eventually_ge_atTop (1:ℝ)).mono fun _ h => amplitude_pos h

def reciprocalInitialStage (b : ℝ) :
    PacketStage (atTop : Filter ℝ) amplitude (fun T => (amplitude T)⁻¹)
      (fun i : Fin 2×Fin 2 => fun _ => initialCenter b i.1) Prod.snd where
  word := (initialStage b).word
  ordinary := (initialStage b).ordinary
  special := (initialStage b).special
  split := (initialStage b).split
  special_norm := (initialStage b).special_norm
  low := (initialStage b).low
  phase := (initialStage b).phase
  phase_norm := (initialStage b).phase_norm
  ordinary_low x hx := by simpa only [amplitude_inverse,id_eq] using (initialStage b).ordinary_low x hx
  special_packets x hx := by
    rw [show (fun T => (amplitude T)⁻¹)=id from funext amplitude_inverse]
    exact (initialStage b).special_packets x hx

def initialTrace {κ : Type*} (b : ℝ) : List (TraceGate κ) :=
  [.mixer (Real.pi/4),.seed (SeededTree.initializationAngles b)]

@[simp] theorem initialTrace_forget {κ : Type*} [Fintype κ] (b : ℝ) :
    TraceWord.forget (initialTrace (κ:=κ) b)=SeededTree.initializationWord b := rfl

theorem initialTrace_valid {κ : Type*} [Fintype κ] (b : ℝ) (h : κ → List SeededTree.Gate) :
    TraceWord.Valid h (initialTrace b) := by trivial

theorem combination_initial {κ : Type*} [Fintype κ] (b T : ℝ) (z : κ → ModeInfinity) :
    combination (Sum.elim (seedDirections b T) z)
      (TraceGate.coeffSeed (SeededTree.initializationAngles b))=
      (2*b:ℂ) • highInfinity (gamma b T) := by
  rw [show TraceGate.coeffSeed (κ:=κ) (SeededTree.initializationAngles b)=
    Sum.elim (fun i => -(SeededTree.initializationAngles b i:ℂ)) 0 from rfl,
    combination_sum_zero]
  simp [combination,Fin.sum_univ_two,SeededTree.initializationAngles,seedDirections,
    -Complex.coe_smul,Complex.ofReal_mul]

 

theorem initial_lowClose {n : ℕ} {κ : Type*} [Fintype κ] (b : ℝ) (f : CausalFrame b n κ) :
    PacketUnitaryFamily.LowClose (lowInfinity b)
      (WeylWord.family (TraceWord.encode (initialTrace b)) f.gram) := by
  intro x hx
  have he : ∀ᶠ T : ℝ in atTop,‖(2*b:ℂ) • highInfinity (gamma b T)‖≤2*|b| := by
    exact Eventually.of_forall fun T => by
      simp only [norm_smul,norm_highInfinity,mul_one,Complex.norm_mul,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_eq_abs,le_refl]
  have hh := hx.pulse_close (dInfinity b) (fun T => (2*b:ℂ) • highInfinity (gamma b T))
    (2*|b|) he (by simpa only [←Complex.coe_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
      using dInfinity_approx_high b)
  change Tendsto (fun T => ‖SpinOperators.act (R (Real.pi/4)) (WZ (dInfinity b T) (x T))-
    SpinOperators.act (R (Real.pi/4)) (WZ
      (combination (Sum.elim (seedDirections b T) (f.actual T))
        (TraceGate.coeffSeed (SeededTree.initializationAngles b))) (x T))‖) atTop (𝓝 0)
  simp only [combination_initial,←map_sub,SpinOperators.norm_act (R_unitary _)]
  exact hh

 

def initialRecorded (b : ℝ) (hb : 0<b) (n : ℕ) : TaggedFrame b (n+1) (PEmpty ⊕ Unit) := by
  let f := TaggedFrame.initial b hb n
  refine f.append hb (fun _ => eInfinity) [] (by simp) ?_ ?_
  · simpa only [modeFock_eInfinity] using
      (BoundedPacket.root (BoundedPacket.vacuum (l:=(atTop : Filter ℝ)) (E:=ModeInfinity)) Z).approx
  · change ApproxMatch atTop f.frame.directions f.frame.model
        (fun _ => modeFock eInfinity)
        (SpinOperators.act Z (vacuum (SeededTree.TopMode (n+1))))
    simp only [modeFock_eInfinity]
    exact (PacketMatch.vacuum.root Z).approx

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

namespace CausalFrame
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

def centerModel (f : CausalFrame b n κ) (c : κ → ℂ) : SeededTree.Level (n+1) :=
  (SeededTree.empty n).toLinearIsometry
    (combination (fun i => (f.formal i : SeededTree.Level n)) c)

def visibility (f : CausalFrame b n κ) (w : List (TraceGate κ)) (c : κ → ℂ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -2*(⟪(WeylWord.op f.model (TraceWord.encode w)).symm
    (SpinOperators.act P (WeylWord.op f.model (TraceWord.encode w)
      (vacuum (SeededTree.TopMode (n+1))))),f.centerModel c⟫_ℂ).im

 

theorem center_match (f : CausalFrame b n κ) (c : κ → ℂ) (d : ℝ → ModeInfinity)
    (he : Tendsto (fun T => ‖d T-combination (f.actual T) c‖) atTop (𝓝 0)) :
    ApproxMatch atTop f.directions f.model (fun T => modeFock (d T)) (f.centerModel c) := by
  apply (f.combination_packet c).close
  simpa only [←map_sub,modeFock.norm_map] using he

 

theorem visibility_limit {ι : Type*} [Fintype ι] (f : CausalFrame b n κ)
    {centers : ι → ℝ → ModeInfinity} {spin : ι → Fin 2}
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) centers spin)
    (w : List (TraceGate κ))
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family (TraceWord.encode w) f.gram))
    (c : κ → ℂ) (d : ℝ → ModeInfinity)
    (he : Tendsto (fun T => ‖d T-combination (f.actual T) c‖) atTop (𝓝 0))
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    Tendsto (fun T => -2*(⟪(ordinaryLocal (st.word T)).symm
      (SpinOperators.act P (ordinaryLocal (st.word T) (vacuum ModeInfinity))),modeFock (d T)⟫_ℂ).im)
      atTop (𝓝 (f.visibility w c P)) := by
  have hz := st.actual_insertion_match (TraceWord.encode w) f.gram hc
    amplitude_zero amplitude_eventually_pos P hP
  have hh := hz.inner (f.center_match c d he) f.gram
  exact ((Complex.continuous_im.tendsto _).comp hh).const_mul (-2)

theorem visibility_Z {ι : Type*} [Fintype ι] (f : CausalFrame b n κ)
    {centers : ι → ℝ → ModeInfinity} {spin : ι → Fin 2}
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) centers spin)
    (w : List (TraceGate κ))
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family (TraceWord.encode w) f.gram))
    (c : κ → ℂ) (d : ℝ → ModeInfinity)
    (he : Tendsto (fun T => ‖d T-combination (f.actual T) c‖) atTop (𝓝 0)) :
    Tendsto (fun T => -2*(⟪insertionInfinity (st.word T),d T⟫_ℂ).im)
      atTop (𝓝 (f.visibility w c Z)) := by
  simpa only [←modeFock_insertion,modeFock.inner_map_map] using
    f.visibility_limit st w hc c d he Z Z_unitary

theorem visibility_Y {ι : Type*} [Fintype ι] (f : CausalFrame b n κ)
    {centers : ι → ℝ → ModeInfinity} {spin : ι → Fin 2}
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) centers spin)
    (w : List (TraceGate κ))
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family (TraceWord.encode w) f.gram))
    (c : κ → ℂ) (d : ℝ → ModeInfinity)
    (he : Tendsto (fun T => ‖d T-combination (f.actual T) c‖) atTop (𝓝 0)) :
    Tendsto (fun T => -2*(⟪insertionYInfinity (st.word T),d T⟫_ℂ).im)
      atTop (𝓝 (f.visibility w c Y)) := by
  simpa only [←modeFock_insertionY,modeFock.inner_map_map] using
    f.visibility_limit st w hc c d he Y Y_unitary

end CausalFrame
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem exists_compensated_transport
    (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (θ : ℝ)
    (address : α → SpinSpace ModeInfinity) (ht : st.Transported address)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0)
    (hZ : ∀i,Tendsto (fun q => -2*(⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (st' : PacketStage l r (fun q => (r q)⁻¹) d spin),
      (∀q,st'.word q=.mixer θ::probePrefix (r q) (st.word q) a K) ∧
      (∀q x,st'.low.op q x=SpinOperators.act (R θ) (st.low.op q x)) ∧ st'.Transported address := by
  obtain ⟨K,a,ho,hs⟩ := st.exists_standard_selector (-θ) hr hp C hC hd v hv hZ hY
  have hS : ∀ᶠ q in l,0≤(r q)⁻¹ := hp.mono fun _ hq => (inv_pos.mpr hq).le
  let st' := st.compensated θ a K hS ho (fun x hx => hs _ (st.special_packets x hx))
  refine ⟨K,a,st',fun _ => rfl,fun _ _ => rfl,?_⟩
  exact ht.compensated θ a K hS ho (fun x hx => hs _ (st.special_packets x hx))
    (hs _ (st.special_packets _ BoundedPacket.vacuum).rootZ)

end PacketStage
end PointedTree

end

end OAI
