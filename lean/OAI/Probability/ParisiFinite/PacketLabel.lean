import Mathlib
import OAI.Probability.ParisiFinite.Energy

namespace OAI

/-! Packet Label. -/

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
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

abbrev PacketLabel := Fin 2 × Fin 2

 

structure CausalStage (b : ℝ) (n : ℕ) (κ : Type*) [Fintype κ] where
  frame : TaggedFrame b n κ
  trace : List (TraceGate κ)
  valid : TraceWord.Valid frame.history trace
  depth : (TraceWord.forget trace).length≤n
  centers : PacketLabel → ℝ → ModeInfinity
  coefficients : PacketLabel → κ → ℂ
  stage : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) centers Prod.snd
  lowClose : PacketUnitaryFamily.LowClose stage.low
    (WeylWord.family (TraceWord.encode trace) frame.frame.gram)
  centerClose : ∀i,Tendsto (fun T => ‖centers i T-
    combination (frame.frame.actual T) (coefficients i)‖) atTop (𝓝 0)
  centerPacket : ∀i,ApproxPacket atTop (fun T => modeFock (centers i T))
  radius : ℝ
  radius_nonneg : 0≤radius
  centerBound : ∀i,∀ᶠ T in atTop,‖centers i T‖≤radius
  transport : stage.Transported (fun T => modeFock (addressInfinity b T))

namespace CausalStage
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

def visible (s : CausalStage b n κ) : Prop :=
  ∀i,s.frame.frame.visibility s.trace (s.coefficients i) Z≠0

def projections (s : CausalStage b n κ) (i : PacketLabel) : ℝ×ℝ :=
  (s.frame.frame.visibility s.trace (s.coefficients i) Z,
   s.frame.frame.visibility s.trace (s.coefficients i) Y)

theorem projections_nonzero (s : CausalStage b n κ) (hv : s.visible) (i : PacketLabel) :
    s.projections i≠0 := by
  intro h
  exact hv i (congrArg Prod.fst h)

theorem projections_Z (s : CausalStage b n κ) (i : PacketLabel) :
    Tendsto (fun T => -2*(⟪insertionInfinity (s.stage.word T),s.centers i T⟫_ℂ).im)
      atTop (𝓝 (s.projections i).1) :=
  s.frame.frame.visibility_Z s.stage s.trace s.lowClose (s.coefficients i) (s.centers i) (s.centerClose i)

theorem projections_Y (s : CausalStage b n κ) (i : PacketLabel) :
    Tendsto (fun T => -2*(⟪insertionYInfinity (s.stage.word T),s.centers i T⟫_ℂ).im)
      atTop (𝓝 (s.projections i).2) :=
  s.frame.frame.visibility_Y s.stage s.trace s.lowClose (s.coefficients i) (s.centers i) (s.centerClose i)

 

def record (s : CausalStage b n κ) (hb : 0<b) : CausalStage b (n+1) (κ ⊕ Unit) where
  frame := s.frame.record hb s.stage s.trace s.valid (s.depth.trans (Nat.le_succ n))
    s.lowClose amplitude_zero amplitude_eventually_pos
  trace := s.trace.map (TraceGate.reindex Sum.inl)
  valid := TraceWord.valid_reindex Sum.inl s.trace s.frame.history
    (Sum.elim s.frame.history (fun _ => TraceWord.forget s.trace)) (fun _ => rfl) s.valid
  depth := by simpa only [TraceWord.forget_reindex] using s.depth.trans (Nat.le_succ n)
  centers := s.centers
  coefficients i := Sum.elim (s.coefficients i) 0
  stage := s.stage
  lowClose := by
    intro x hx
    have hh := s.lowClose x hx
    convert hh using 1
    funext T
    congr 2
    exact congrArg (fun U : SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity => U (x T))
      (TraceWord.op_reindex Sum.inl s.trace (seedDirections b T)
        (s.frame.frame.actual T) (Sum.elim (s.frame.frame.actual T)
          (fun _ : Unit => insertionInfinity (s.stage.word T))) (fun _ => rfl))
  centerClose i := by
    change Tendsto (fun T => ‖s.centers i T-combination
      (Sum.elim (s.frame.frame.actual T) (fun _ : Unit => insertionInfinity (s.stage.word T)))
      (Sum.elim (s.coefficients i) 0)‖) atTop (𝓝 0)
    simpa only [combination_sum_zero] using s.centerClose i
  centerPacket := s.centerPacket
  radius := s.radius
  radius_nonneg := s.radius_nonneg
  centerBound := s.centerBound
  transport := s.transport

 

def cost (s : CausalStage b n κ) (hb : 0<b) (c : ℝ) : CausalStage b (n+1) (κ ⊕ Unit) := by
  let t := s.record hb
  refine {
    frame := t.frame
    trace := .cost (Sum.inr ()) c::t.trace
    valid := ⟨?_,t.valid⟩
    depth := ?_
    centers := t.centers
    coefficients := t.coefficients
    stage := t.stage.cost c
    lowClose := ?_
    centerClose := t.centerClose
    centerPacket := t.centerPacket
    radius := t.radius
    radius_nonneg := t.radius_nonneg
    centerBound := t.centerBound
    transport := t.transport.cost c }
  · exact (TraceWord.forget_reindex Sum.inl s.trace).symm
  · change (TraceWord.forget t.trace).length+1≤n+1
    dsimp only [t,record]
    rw [TraceWord.forget_reindex]
    exact Nat.add_le_add_right s.depth 1
  · intro x hx
    have hh := t.lowClose x hx
    change Tendsto (fun T => ‖WZ (-(c:ℂ) • insertionInfinity (t.stage.word T)) (t.stage.low.op T (x T))-
      WZ (combination (t.frame.frame.directions T) (TraceGate.coeffCost (Sum.inr ()) c))
        (WeylWord.op (t.frame.frame.directions T) (TraceWord.encode t.trace) (x T))‖) atTop (𝓝 0)
    have he (T : ℝ) : t.frame.frame.directions T (Sum.inr (Sum.inr ()))=
        insertionInfinity (t.stage.word T) := rfl
    simp only [TraceGate.combination_cost,he,←map_sub,norm_WZ]
    exact hh

end CausalStage
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
namespace CausalStage
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

 

theorem exists_mixer (s : CausalStage b n κ) (hb : 0<b) (theta : ℝ) (hv : s.visible) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (s' : CausalStage b (n+1) (κ ⊕ Unit)),
      s'.trace=.mixer theta::s.trace.map (TraceGate.reindex Sum.inl) ∧
      (∀T,s'.stage.word T=.mixer theta::probePrefix (amplitude T) (s.stage.word T) a K) ∧
      s'.centers=s.centers ∧ (∀i,s'.coefficients i=Sum.elim (s.coefficients i) 0) ∧
      s'.frame=(s.record hb).frame := by
  obtain ⟨K,a,st',hw,hl,ht⟩ := s.stage.exists_compensated_transport theta
    (fun T => modeFock (addressInfinity b T)) s.transport amplitude_zero amplitude_eventually_pos
    s.radius s.radius_nonneg s.centerBound s.projections (s.projections_nonzero hv)
    s.projections_Z s.projections_Y
  let t := s.record hb
  have hc : PacketUnitaryFamily.LowClose st'.low
      (WeylWord.family (TraceWord.encode (.mixer theta::t.trace)) t.frame.frame.gram) := by
    intro x hx
    have h := t.lowClose x hx
    change Tendsto (fun T => ‖st'.low.op T (x T)-
      SpinOperators.act (R theta) (WeylWord.op (t.frame.frame.directions T) (TraceWord.encode t.trace) (x T))‖)
      atTop (𝓝 0)
    simp only [hl,←map_sub,SpinOperators.norm_act (R_unitary _)]
    exact h
  have hd : (TraceWord.forget (.mixer theta::t.trace)).length≤n+1 := by
    change (TraceWord.forget t.trace).length+1≤n+1
    dsimp only [t,record]
    rw [TraceWord.forget_reindex]
    exact Nat.add_le_add_right s.depth 1
  let s' : CausalStage b (n+1) (κ ⊕ Unit) := {
    frame := t.frame
    trace := .mixer theta::t.trace
    valid := t.valid
    depth := hd
    centers := s.centers
    coefficients := t.coefficients
    stage := st'
    lowClose := hc
    centerClose := t.centerClose
    centerPacket := s.centerPacket
    radius := s.radius
    radius_nonneg := s.radius_nonneg
    centerBound := s.centerBound
    transport := ht }
  exact ⟨K,a,s',rfl,hw,rfl,(fun _ => rfl),rfl⟩

 
def initialCoefficient (b : ℝ) (i : PacketLabel) : ℂ :=
  if i.1=0 then (-2*b:ℂ) else (2*b:ℂ)

theorem initialCenter_coefficient (b : ℝ) (i : PacketLabel) :
    initialCenter b i.1=initialCoefficient b i • eInfinity := by
  unfold initialCenter signedMode initialCoefficient
  split_ifs <;> simp [←Complex.coe_smul,Complex.ofReal_mul]

 

def initial (b : ℝ) (hb : 0<b) : CausalStage b 2 (PEmpty ⊕ Unit) where
  frame := initialRecorded b hb 1
  trace := initialTrace b
  valid := initialTrace_valid b _
  depth := by
    change 2≤2
    omega
  centers i _ := initialCenter b i.1
  coefficients i := Sum.elim PEmpty.elim (fun _ => initialCoefficient b i)
  stage := reciprocalInitialStage b
  lowClose := initial_lowClose b _
  centerClose i := by
    have he (T : ℝ) : combination ((initialRecorded b hb 1).frame.actual T)
        (Sum.elim PEmpty.elim (fun _ => initialCoefficient b i))=initialCenter b i.1 := by
      change combination (Sum.elim PEmpty.elim (fun _ : Unit => eInfinity))
        (Sum.elim PEmpty.elim (fun _ => initialCoefficient b i))=_
      simp only [combination,Fintype.sum_sum_type,Fintype.sum_empty,zero_add,Fintype.sum_unique]
      exact (initialCenter_coefficient b i).symm
    change Tendsto (fun T => ‖initialCenter b i.1-combination
      ((initialRecorded b hb 1).frame.actual T)
      (Sum.elim PEmpty.elim (fun _ => initialCoefficient b i))‖) atTop (𝓝 0)
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0)) using 1
    funext T
    rw [he]
    simp
  centerPacket i := by
    simp only [initialCenter_coefficient,map_smul,modeFock_eInfinity]
    exact ((BoundedPacket.vacuum.root Z).approx).smul (initialCoefficient b i)
  radius := 2*|b|
  radius_nonneg := by positivity
  centerBound i := Eventually.of_forall fun _ => (norm_initialCenter b i.1).le
  transport := by
    have h := initialStage_transported b
    unfold PacketStage.Transported at h ⊢
    simpa only [reciprocalInitialStage,amplitude_inverse,id_eq] using h

end CausalStage
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance ecRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance ecRealSMul : SMul ℝ ModeInfinity := ecRealModule.toDistribMulAction.toSMul
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

def echoReference (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (i : κ) (q : α) : ModeInfinity :=
  d i q+signedMode (spin i) ((-2*t) • insertionInfinity (st.word q))

theorem halfEchoCenter_sub_reference (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (i : κ) (q : α) (hr : r q≠0) :
    st.halfEchoCenter t a K i q-st.echoReference t i q=
      -signedMode (spin i) (r q • st.halfEchoResidual t a K q) := by
  have hm : r q*(t/r q)=t := by field_simp
  have he : r q • st.halfEchoResidual t a K q=
      t • (insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)-
        insertionInfinity (st.word q)) := by
    unfold halfEchoResidual
    change (r q:ℂ) • (((t/r q:ℝ):ℂ) •
      (insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)-insertionInfinity (st.word q)))=
      (t:ℂ) • (insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)-insertionInfinity (st.word q))
    rw [smul_smul,←Complex.ofReal_mul,hm]
  rw [he]
  have hf (j : Fin 2) (v : ModeInfinity) : signedMode (1-j) v = -signedMode j v := by
    fin_cases j <;> simp [signedMode]
  unfold halfEchoCenter forwardCenter echoReference
  rw [hf]
  unfold signedMode
  split_ifs
  all_goals simp only [←Complex.coe_smul,Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_ofNat,neg_neg]
  all_goals module

theorem halfEchoCenter_close (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (i : κ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (G : ℝ) (hg : ∀ᶠ q in l,‖st.halfEchoResidual t a K q‖≤G) :
    Tendsto (fun q => ‖st.halfEchoCenter t a K i q-st.echoReference t i q‖) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [zero_mul] using hr.mul_const G)
  filter_upwards [hp,hg] with q hq hgq
  rw [st.halfEchoCenter_sub_reference t a K i q hq.ne',norm_neg,norm_signedMode,
    norm_smul,Real.norm_eq_abs,abs_of_pos hq]
  exact mul_le_mul_of_nonneg_left hgq hq.le

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
local instance ceRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance ceRealSMul : SMul ℝ ModeInfinity := ceRealModule.toDistribMulAction.toSMul
namespace CausalStage
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

def echoAngles (t : ℝ) (i : Fin 2) : ℝ := if i=0 then 0 else 2*t

def echoCoefficient (t : ℝ) (i : PacketLabel) : ℂ :=
  if i.2=0 then (-2*t:ℂ) else (2*t:ℂ)

def echoCoefficients (s : CausalStage b n κ) (t : ℝ) (i : PacketLabel) : κ ⊕ Unit → ℂ :=
  Sum.elim (s.coefficients i) (fun _ => echoCoefficient t i)

def echoTrace (s : CausalStage b n κ) (t : ℝ) : List (TraceGate (κ ⊕ Unit)) :=
  .seed (echoAngles t)::s.trace.map (TraceGate.reindex Sum.inl)

def echoVisible (s : CausalStage b n κ) (hb : 0<b) (t : ℝ) : Prop :=
  ∀i,(s.record hb).frame.frame.visibility (s.echoTrace t) (s.echoCoefficients t i) Z≠0

theorem signed_echo (t : ℝ) (i : PacketLabel) (v : ModeInfinity) :
    signedMode i.2 ((-2*t) • v)=echoCoefficient t i • v := by
  unfold signedMode echoCoefficient
  split_ifs <;> simp [←Complex.coe_smul,Complex.ofReal_mul]

theorem echo_combination (s : CausalStage b n κ) (hb : 0<b) (t : ℝ) (i : PacketLabel) (T : ℝ) :
    combination ((s.record hb).frame.frame.actual T) (s.echoCoefficients t i)=
      combination (s.frame.frame.actual T) (s.coefficients i)+
        signedMode i.2 ((-2*t) • insertionInfinity (s.stage.word T)) := by
  change combination (Sum.elim (s.frame.frame.actual T)
    (fun _ : Unit => insertionInfinity (s.stage.word T)))
    (Sum.elim (s.coefficients i) (fun _ => echoCoefficient t i))=_
  simp only [combination,Fintype.sum_sum_type,Fintype.sum_unique,Sum.elim_inl,Sum.elim_inr,signed_echo]

theorem echo_seed_combination (f : CausalFrame b n κ) (t T : ℝ) :
    combination (f.directions T) (TraceGate.coeffSeed (echoAngles t))=
      (-2*t) • addressInfinity b T := by
  rw [show TraceGate.coeffSeed (κ:=κ) (echoAngles t)=
    Sum.elim (fun i => -(echoAngles t i:ℂ)) 0 from rfl]
  change combination (Sum.elim (seedDirections b T) (f.actual T)) _=_
  rw [combination_sum_zero]
  simp [combination,Fin.sum_univ_two,echoAngles,seedDirections,←Complex.coe_smul,Complex.ofReal_mul]

theorem echo_centerClose (s : CausalStage b n κ) (hb : 0<b) (t : ℝ)
    (a : ℕ → ShortPulse) (K : ℕ)
    (G : ℝ) (hg : ∀ᶠ T in atTop,‖s.stage.halfEchoResidual t a K T‖≤G) (i : PacketLabel) :
    Tendsto (fun T => ‖s.stage.halfEchoCenter t a K i T-
      combination ((s.record hb).frame.frame.actual T) (s.echoCoefficients t i)‖) atTop (𝓝 0) := by
  have h1 := s.stage.halfEchoCenter_close t a K i amplitude_zero amplitude_eventually_pos G hg
  have h2 : Tendsto (fun T => ‖s.stage.echoReference t i T-
      combination ((s.record hb).frame.frame.actual T) (s.echoCoefficients t i)‖) atTop (𝓝 0) := by
    simpa only [PacketStage.echoReference,echo_combination,add_sub_add_right_eq_sub] using s.centerClose i
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using h1.add h2)
  exact Eventually.of_forall fun T => norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem echo_lowClose (s : CausalStage b n κ) (hb : 0<b) (t : ℝ)
    (a : ℕ → ShortPulse) (K : ℕ)
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹)
      (s.stage.halfEchoCenter t a K) (fun i => 1-i.2))
    (hl : ∀T x,st.low.op T x=WZ (s.stage.halfEchoResidual t a K T) (s.stage.low.op T x))
    (he : Tendsto (fun T => ‖s.stage.halfEchoResidual t a K T-(-2*t) • addressInfinity b T‖) atTop (𝓝 0)) :
    PacketUnitaryFamily.LowClose st.low
      (WeylWord.family (TraceWord.encode (s.echoTrace t)) (s.record hb).frame.frame.gram) := by
  intro x hx
  let f := (s.record hb).frame.frame
  let w := (s.record hb).trace
  let y (T : ℝ) := WeylWord.op (f.directions T) (TraceWord.encode w) (x T)
  have hy : BoundedPacket atTop y := (WeylWord.family (TraceWord.encode w) f.gram).forward x hx
  have h1 := (s.record hb).lowClose x hx
  change Tendsto (fun T => ‖s.stage.low.op T (x T)-y T‖) atTop (𝓝 0) at h1
  have h2 := hy.pulse_close (s.stage.halfEchoResidual t a K)
    (fun T => (-2*t) • addressInfinity b T) (2*|t|)
    (Eventually.of_forall fun T => by
      simp [norm_smul,Real.norm_eq_abs,norm_addressInfinity]) he
  change Tendsto (fun T => ‖st.low.op T (x T)-
    WZ (combination (f.directions T) (TraceGate.coeffSeed (echoAngles t))) (y T)‖) atTop (𝓝 0)
  simp only [hl,echo_seed_combination]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using h1.add h2)
  exact Eventually.of_forall fun T => by
    have h := norm_sub_le_norm_sub_add_norm_sub
      (WZ (s.stage.halfEchoResidual t a K T) (s.stage.low.op T (x T)))
      (WZ (s.stage.halfEchoResidual t a K T) (y T)) (WZ ((-2*t) • addressInfinity b T) (y T))
    simpa only [←map_sub,norm_WZ] using h

 

def restoredSpin {d : PacketLabel → ℝ → ModeInfinity}
    (st : PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) d (fun i => 1-(1-i.2))) :
    PacketStage atTop amplitude (fun T => (amplitude T)⁻¹) d Prod.snd where
  word := st.word
  ordinary := st.ordinary
  special := st.special
  split := st.split
  special_norm := st.special_norm
  low := st.low
  phase := st.phase
  phase_norm := st.phase_norm
  ordinary_low := st.ordinary_low
  special_packets x hx := by
    have h : (fun i : PacketLabel => 1-(1-i.2))=Prod.snd := by
      funext i
      rcases i with ⟨i,j⟩
      fin_cases j <;> rfl
    simpa only [h] using st.special_packets x hx

 

theorem exists_echo (s : CausalStage b n κ) (hb : 0<b) (t : ℝ) (ht : t≠0)
    (hv : s.visible) (hv' : s.echoVisible hb t) :
    ∃ (K L : ℕ) (a c : ℕ → ShortPulse) (s' : CausalStage b (n+1) (κ ⊕ Unit)),
      s'.trace=s.echoTrace t ∧
      (∀T,s'.stage.word T=probePrefix (amplitude T) (s.stage.halfEchoWord t a K T) c L) ∧
      s'.centers=s.stage.halfEchoCenter t a K ∧ s'.coefficients=s.echoCoefficients t ∧
      s'.frame=(s.record hb).frame := by
  have hZ (i : PacketLabel) : Tendsto
      (fun T => (⟪insertionInfinity (s.stage.word T),s.centers i T⟫_ℂ).im) atTop
      (𝓝 (-s.frame.frame.visibility s.trace (s.coefficients i) Z/2)) := by
    have h := (s.projections_Z i).div_const (-2)
    convert h using 1
    · funext T
      ring
    · congr 1
      dsimp only [projections]
      ring
  have hn (i : PacketLabel) : -s.frame.frame.visibility s.trace (s.coefficients i) Z/2≠0 := by
    exact div_ne_zero (neg_ne_zero.mpr (hv i)) (by norm_num)
  have hab : ∀ᶠ T in atTop,‖addressInfinity b T‖≤1 :=
    Eventually.of_forall fun T => (norm_addressInfinity b T).le
  obtain ⟨K,a,st,hw,hl,htrans,he,hpacket⟩ := s.stage.exists_halfEcho t ht
    amplitude_zero amplitude_eventually_pos s.radius s.radius_nonneg s.centerBound s.centerPacket
    (fun i => -s.frame.frame.visibility s.trace (s.coefficients i) Z/2) hn hZ
    (addressInfinity b) s.transport 1 (by norm_num) hab
  have hg := s.stage.halfEchoResidual_bounded (addressInfinity b) t a K 1 (by norm_num) hab he
  have hc := s.echo_centerClose hb t a K _ hg
  have hlow := s.echo_lowClose hb t a K st hl he
  let f := (s.record hb).frame.frame
  let v (i : PacketLabel) : ℝ×ℝ :=
    (f.visibility (s.echoTrace t) (s.echoCoefficients t i) Z,
     f.visibility (s.echoTrace t) (s.echoCoefficients t i) Y)
  have hvv (i : PacketLabel) : v i≠0 := by
    intro h
    exact hv' i (congrArg Prod.fst h)
  have hz (i : PacketLabel) : Tendsto
      (fun T => -2*(⟪insertionInfinity (st.word T),s.stage.halfEchoCenter t a K i T⟫_ℂ).im)
      atTop (𝓝 (v i).1) :=
    f.visibility_Z st (s.echoTrace t) hlow (s.echoCoefficients t i) _ (hc i)
  have hy (i : PacketLabel) : Tendsto
      (fun T => -2*(⟪insertionYInfinity (st.word T),s.stage.halfEchoCenter t a K i T⟫_ℂ).im)
      atTop (𝓝 (v i).2) :=
    f.visibility_Y st (s.echoTrace t) hlow (s.echoCoefficients t i) _ (hc i)
  have hbnd := s.stage.halfEchoCenter_bounded t a K s.radius s.centerBound
  have hradius : 0 ≤ s.radius+2*|t| := add_nonneg s.radius_nonneg (by positivity)
  obtain ⟨L,c,st',hw',hl',htrans'⟩ := st.exists_negativeFlip
    (fun T => -modeFock (addressInfinity b T)) htrans
    amplitude_zero amplitude_eventually_pos (s.radius+2*|t|) hradius hbnd v hvv hz hy
  let s' : CausalStage b (n+1) (κ ⊕ Unit) := {
    frame := (s.record hb).frame
    trace := s.echoTrace t
    valid := (s.record hb).valid
    depth := by
      change (TraceWord.forget (s.trace.map (TraceGate.reindex Sum.inl))).length+1≤n+1
      rw [TraceWord.forget_reindex]
      exact Nat.add_le_add_right s.depth 1
    centers := s.stage.halfEchoCenter t a K
    coefficients := s.echoCoefficients t
    stage := restoredSpin st'
    lowClose := by
      intro x hx
      simpa only [restoredSpin,hl'] using hlow x hx
    centerClose := hc
    centerPacket := hpacket
    radius := s.radius+2*|t|
    radius_nonneg := hradius
    centerBound := hbnd
    transport := by
      unfold PacketStage.Transported at htrans' ⊢
      simpa only [restoredSpin,neg_neg] using htrans' }
  exact ⟨K,L,a,c,s',rfl,fun T => by rw [show s'.stage.word T=st'.word T from rfl,hw',hw],rfl,rfl,rfl⟩

end CausalStage
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin
namespace CausalStage
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

 

theorem value_limit (s : CausalStage b n κ) (hb : 0<b) :
    Tendsto (fun T => ordinaryValue (s.stage.word T)) atTop
      (𝓝 (SeededTree.value (TraceWord.forget s.trace))) := by
  have h := (s.record hb).frame.frame.energy (Sum.inr ())
  change Tendsto (fun T => energyInfinity (insertionInfinity (s.stage.word T))) atTop
    (𝓝 (SeededTree.treeEnergy (n+1)
      (SeededTree.circuit (TraceWord.forget s.trace) (n+1)).insertion)) at h
  simpa only [energy_insertionInfinity,←SeededTree.value_eq_height _ _ (s.depth.trans (Nat.le_succ n))] using h

 

theorem exists_word_close (s : CausalStage b n κ) (hb : 0<b) {ε : ℝ} (hε : 0<ε) :
    ∃w : List PointedTree.Gate,
      |ordinaryValue w-SeededTree.value (TraceWord.forget s.trace)|<ε := by
  have h := (s.value_limit hb).eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨T,hT⟩ := h.exists
  exact ⟨s.stage.word T,by simpa only [Metric.mem_ball,Real.dist_eq] using hT⟩

end CausalStage
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus RootSpin

 

structure ControlSignature where
  word : List SeededTree.Gate
  echoes : List (ℝ × List SeededTree.Gate)

namespace ControlSignature

def initial (b : ℝ) : ControlSignature := ⟨SeededTree.initializationWord b,[]⟩

def mixer (s : ControlSignature) (a : ℝ) : ControlSignature := ⟨.mixer a::s.word,s.echoes⟩
def cost (s : ControlSignature) (a : ℝ) : ControlSignature := ⟨.cost a::s.word,s.echoes⟩
def echo (s : ControlSignature) (t : ℝ) : ControlSignature :=
  ⟨.seed (CausalStage.echoAngles t)::s.word,(t,s.word)::s.echoes⟩

def Causal (s : ControlSignature) (n : ℕ) : Prop :=
  s.word.length≤n ∧ ∀p∈s.echoes,p.2.length≤n

def centerTail (n : ℕ) (i : PacketLabel) : List (ℝ × List SeededTree.Gate) → SeededTree.Level n
  | [] => 0
  | (t,w)::l => CausalStage.echoCoefficient t i • ((SeededTree.circuit w n).insertion : SeededTree.Level n)+centerTail n i l

def center (s : ControlSignature) (b : ℝ) (n : ℕ) (i : PacketLabel) : SeededTree.Level n :=
  CausalStage.initialCoefficient b i • ((SeededTree.circuit [] n).insertion : SeededTree.Level n)+centerTail n i s.echoes

def visibility (s : ControlSignature) (b : ℝ) (n : ℕ) (i : PacketLabel) : ℝ :=
  -2*(⟪((SeededTree.circuit s.word n).insertion : SeededTree.Level n),s.center b n i⟫_ℂ).im

def Visible (s : ControlSignature) (b : ℝ) (n : ℕ) : Prop := ∀i,s.visibility b n i≠0

theorem centerTail_step (n : ℕ) (i : PacketLabel) (l : List (ℝ × List SeededTree.Gate))
    (hl : ∀p∈l,p.2.length≤n) :
    (SeededTree.empty n).toLinearIsometry (centerTail n i l)=centerTail (n+1) i l := by
  induction l with
  | nil => simp only [centerTail,map_zero]
  | cons p l ih =>
    have hp := hl p (by simp)
    have hh : ∀q∈l,q.2.length≤n := fun q hq => hl q (by simp [hq])
    rcases p with ⟨t,w⟩
    simp only [centerTail,map_add,map_smul,ih hh]
    congr 1
    exact congrArg (fun v : SeededTree.Mode (n+1) => CausalStage.echoCoefficient t i • (v : SeededTree.Level (n+1)))
      (SeededTree.circuit_insertion_empty w n hp)

theorem center_step (s : ControlSignature) (b : ℝ) (n : ℕ)
    (hs : s.Causal n) (i : PacketLabel) :
    (SeededTree.empty n).toLinearIsometry (s.center b n i)=s.center b (n+1) i := by
  simp only [center,map_add,map_smul,centerTail_step n i s.echoes hs.2]
  congr 1
  exact congrArg (fun v : SeededTree.Mode (n+1) => CausalStage.initialCoefficient b i • (v : SeededTree.Level (n+1)))
    (SeededTree.circuit_insertion_empty [] n (by simp))

theorem causal_succ (s : ControlSignature) {n : ℕ} (hs : s.Causal n) : s.Causal (n+1) :=
  ⟨hs.1.trans (Nat.le_succ n),fun p hp => (hs.2 p hp).trans (Nat.le_succ n)⟩

theorem causal_mixer (s : ControlSignature) {n : ℕ} (hs : s.Causal n) (a : ℝ) :
    (s.mixer a).Causal (n+1) :=
  ⟨Nat.add_le_add_right hs.1 1,fun p hp => (hs.2 p hp).trans (Nat.le_succ n)⟩

theorem causal_cost (s : ControlSignature) {n : ℕ} (hs : s.Causal n) (a : ℝ) :
    (s.cost a).Causal (n+1) :=
  ⟨Nat.add_le_add_right hs.1 1,fun p hp => (hs.2 p hp).trans (Nat.le_succ n)⟩

theorem causal_echo (s : ControlSignature) {n : ℕ} (hs : s.Causal n) (t : ℝ) :
    (s.echo t).Causal (n+1) := by
  refine ⟨Nat.add_le_add_right hs.1 1,?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl|hp
  · exact hs.1.trans (Nat.le_succ n)
  · exact (hs.2 p hp).trans (Nat.le_succ n)

theorem visibility_step (s : ControlSignature) (b : ℝ) (n : ℕ)
    (hs : s.Causal n) (i : PacketLabel) :
    s.visibility b (n+1) i=s.visibility b n i := by
  unfold visibility
  rw [←s.center_step b n hs i,←SeededTree.circuit_insertion_empty s.word n hs.1]
  change -2*(⟪(SeededTree.empty n).toLinearIsometry ((SeededTree.circuit s.word n).insertion : SeededTree.Level n),
    (SeededTree.empty n).toLinearIsometry (s.center b n i)⟫_ℂ).im = _
  rw [LinearIsometry.inner_map_map]

end ControlSignature
end SeedInitialization

end

end OAI
