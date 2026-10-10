import Mathlib
import OAI.Probability.ParisiFinite.InsertionApprox
import OAI.Probability.ParisiFinite.ParamGate

namespace OAI

/-! Negative Flip. -/

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
namespace PointedTree
open CoherentFock RootSpin
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

def negativeFlip (st : PacketStage l r S d spin) (a : ℕ → ShortPulse) (K : ℕ)
    (hS : ∀ᶠ q in l,0≤S q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (x q)-x q‖) l (𝓝 0))
    (hs : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (st.special q (x q))-
        SpinOperators.act (R (-(Real.pi/2))) (st.special q (x q))‖) l (𝓝 0)) :
    PacketStage l r S d (fun i => 1-spin i) where
  word q := probePrefix (r q) (st.word q) a K
  ordinary q := (probeGain (r q) (st.word q) a K).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.ordinary q)
  special q := (probeGain (r q) (st.word q) a K).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.special q)
  split q x := by
    rw [←probeGain_on_local,st.split,map_add]
    rfl
  special_norm := by
    filter_upwards [st.special_norm] with q hq x
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.norm_map] using hq x
  low := st.low
  phase := st.phase
  phase_norm := st.phase_norm
  ordinary_low x hx := by
    have he := st.ordinary_low x hx
    have hp := ho (fun q => st.phase q • st.low.op q (x q)) (st.low_bounded x hx)
    have ht := ForwardControl.scaled_identity_transfer
      (fun q => probeGain (r q) (st.word q) a K) S
      (fun q => st.ordinary q (x q)) (fun q => st.phase q • st.low.op q (x q)) hS hp he
    exact ForwardControl.scaled_triangle S _ _ _ hS ht he
  special_packets x hx := (st.special_packets x hx).negative_half_mixer.close hS (hs x hx)

theorem Transported.negativeFlip {st : PacketStage l r S d spin} {address : α → SpinSpace ModeInfinity}
    (ht : st.Transported address) (a : ℕ → ShortPulse) (K : ℕ) (hS : ∀ᶠ q in l,0≤S q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (x q)-x q‖) l (𝓝 0))
    (hs : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (st.special q (x q))-
        SpinOperators.act (R (-(Real.pi/2))) (st.special q (x q))‖) l (𝓝 0))
    (hz : Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K
      (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))-
      SpinOperators.act (R (-(Real.pi/2))) (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))‖) l (𝓝 0)) :
    (st.negativeFlip a K hS ho hs).Transported (fun q => -address q) := by
  have hh := ForwardControl.scaled_special_transport (fun q => ordinaryLocal (st.word q))
    (fun q => probeGain (r q) (st.word q) a K) (SpinOperators.act Z)
    (SpinOperators.act (R (-(Real.pi/2))))
    (fun x : SpinSpace ModeInfinity => (SpinOperators.norm_act Z_unitary x).le)
    negative_half_mixer_anticommutes (fun q => st.special q (vacuum ModeInfinity)) address S
    hS (hs _ BoundedPacket.vacuum) hz ht
  have he (q : α) (x : SpinSpace ModeInfinity) :
      (ordinaryLocal (probePrefix (r q) (st.word q) a K)).symm x=
        (ordinaryLocal (st.word q)).symm ((probeGain (r q) (st.word q) a K).symm x) :=
    local_symm_after_gain _ _ _ (probeGain_on_local _ _ _ _) x
  change Tendsto (fun q => ‖(S q:ℂ) • (ordinaryLocal (probePrefix (r q) (st.word q) a K)).symm
    (SpinOperators.act Z (probeGain (r q) (st.word q) a K (st.special q (vacuum ModeInfinity))))-(-address q)‖) l (𝓝 0)
  simpa only [he,sub_neg_eq_add] using hh

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
open RootSpin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_im_signed_self (v d : E) (i : Fin 2) (t : ℝ) :
    (⟪v,d+signedMode i (t • v)⟫_ℂ).im=(⟪v,d⟫_ℂ).im := by
  have hi : (⟪v,v⟫_ℂ).im=0 := inner_self_im (𝕜:=ℂ) v
  change (⟪v,d+signedMode i ((t:ℂ) • v)⟫_ℂ).im=_
  unfold signedMode
  split_ifs <;> simp only [inner_add_right,inner_neg_right,inner_smul_right,
    Complex.add_im,Complex.neg_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
    hi,mul_zero,zero_mul,add_zero,neg_zero]

end CoherentFock
namespace PointedTree
open CoherentFock RootSpin
local instance ssRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance ssRealSMul : SMul ℝ ModeInfinity := ssRealModule.toDistribMulAction.toSMul
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem exists_standard_selector (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0)
    (hZ : ∀i,Tendsto (fun q => -2*(⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀x,BoundedPacket l x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.word q) a K (x q)-x q‖) l (𝓝 0)) ∧
      (∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r d spin x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.word q) a K (x q)-
          SpinOperators.act (R θ) (x q)‖) l (𝓝 0)) := by
  let o (q : α) := st.ordinary q (vacuum ModeInfinity)
  let y (q : α) := st.phase q • st.low.op q (vacuum ModeInfinity)
  let s (q : α) := st.special q (vacuum ModeInfinity)
  obtain ⟨hS,hscale⟩ := reciprocal_scale_eventually r hr hp
  have he : Tendsto (fun q => ‖o q-y q‖) l (𝓝 0) :=
    PacketGeometry.tendsto_of_scaled (fun q => (r q)⁻¹) _ hS
      (Eventually.of_forall fun _ => norm_nonneg _) (st.ordinary_low _ BoundedPacket.vacuum)
  have hψ : ∀ᶠ q in l,ordinaryLocal (st.word q) (vacuum ModeInfinity)=y q+s q+(o q-y q) := by
    exact Eventually.of_forall fun q => by dsimp only [o,s]; rw [st.split]; abel
  exact standard_selective_bounded r st.word y s (fun q => o q-y q)
    (st.low_bounded _ BoundedPacket.vacuum) d spin C hC hd v hv θ hr hp hψ
    (st.special_vacuum_zero hr) he hZ hY

 

theorem exists_huge_selector_visible (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (ht : t≠0) (θ : ℝ) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (ha : ∀i,ApproxPacket l (fun q => modeFock (d i q)))
    (c : κ → ℝ) (hc : ∀i,c i≠0)
    (hZ : ∀i,Tendsto (fun q => (⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (c i))) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀x,BoundedPacket l x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
          (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0)) ∧
      (∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (x q)-
          SpinOperators.act (R θ) (x q)‖) l (𝓝 0)) := by
  have hbound (i : κ) : ∀ᶠ q in l,‖st.forwardCenter t i q‖≤C+|t| := by
    filter_upwards [hd i] with q hq
    apply (norm_add_le _ _).trans
    simp only [norm_signedMode,norm_smul,Real.norm_eq_abs,abs_neg,norm_insertionInfinity,mul_one]
    exact add_le_add hq le_rfl
  have hz (i : κ) : Tendsto (fun q => (⟪insertionInfinity (st.forwardWord t q),st.forwardCenter t i q⟫_ℂ).im)
      l (𝓝 (c i)) := by
    simpa only [forwardWord,insertionInfinity_cost,forwardCenter,inner_im_signed_self] using hZ i
  have hy (i : κ) : Tendsto (fun q => -2*(⟪insertionYInfinity (st.forwardWord t q),st.forwardCenter t i q⟫_ℂ).im)
      l (𝓝 0) := by
    have hi := (Complex.continuous_im.tendsto 0).comp
      (st.huge_transverse_approx t ht hr hp (st.forwardCenter t i) (st.forwardCenter_approx t hr hp ha i))
    simpa only [Function.comp_def,Complex.zero_im,mul_zero] using hi.const_mul (-2)
  exact st.exists_huge_selector t ht θ hr hp (C+|t|) (add_nonneg hC (abs_nonneg _)) hbound c (fun _ => 0) hc hz hy

 

theorem exists_negativeFlip (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (address : α → SpinSpace ModeInfinity) (ht : st.Transported address)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0)
    (hZ : ∀i,Tendsto (fun q => -2*(⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (st' : PacketStage l r (fun q => (r q)⁻¹) d (fun i => 1-spin i)),
      (∀q,st'.word q=probePrefix (r q) (st.word q) a K) ∧
      (∀q x,st'.low.op q x=st.low.op q x) ∧ st'.Transported (fun q => -address q) := by
  obtain ⟨K,a,ho,hs⟩ := st.exists_standard_selector (-(Real.pi/2)) hr hp C hC hd v hv hZ hY
  have hS : ∀ᶠ q in l,0≤(r q)⁻¹ := hp.mono fun _ hq => (inv_pos.mpr hq).le
  let st' := st.negativeFlip a K hS ho (fun x hx => hs _ (st.special_packets x hx))
  refine ⟨K,a,st',fun _ => rfl,fun _ _ => rfl,?_⟩
  exact ht.negativeFlip a K hS ho (fun x hx => hs _ (st.special_packets x hx))
    (hs _ (st.special_packets _ BoundedPacket.vacuum).rootZ)

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance esRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance esRealSMul : SMul ℝ ModeInfinity := esRealModule.toDistribMulAction.toSMul
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem halfEchoCenter_bounded (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (C : ℝ)
    (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C) (i : κ) :
    ∀ᶠ q in l,‖st.halfEchoCenter t a K i q‖≤C+2*|t| := by
  filter_upwards [hd i] with q hq
  unfold halfEchoCenter forwardCenter
  apply (norm_add_le _ _).trans
  have hh := (norm_add_le (d i q) (signedMode (spin i) ((-t) • insertionInfinity (st.word q))))
  simp only [norm_signedMode,norm_smul,Real.norm_eq_abs,abs_neg,norm_insertionInfinity,mul_one] at hh ⊢
  calc
    _ ≤ (‖d i q‖+|t|)+|t| := add_le_add hh le_rfl
    _ ≤ C+2*|t| := by linarith

 

theorem halfEchoCenter_approx (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ)
    (st' : PacketStage l r (fun q => (r q)⁻¹) (st.halfEchoCenter t a K) (fun i => 1-spin i))
    (hw : ∀q,st'.word q=st.halfEchoWord t a K q)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (hd : ∀i,ApproxPacket l (fun q => modeFock (d i q))) (i : κ) :
    ApproxPacket l (fun q => modeFock (st.halfEchoCenter t a K i q)) := by
  have ha : ApproxPacket l (fun q => modeFock
      (insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K))) := by
    simpa only [hw,halfEchoWord,insertionInfinity_cost] using st'.insertionZ_approx hr hp
  have he (v : ModeInfinity) : modeFock (t • v)=(t:ℂ) • modeFock v := by
    change modeFock ((t:ℂ) • v)=_
    exact map_smul _ _ _
  have hsum := st.forwardCenter_approx t hr hp hd i
  have hv := ha.smul (t:ℂ)
  unfold halfEchoCenter signedMode
  split_ifs
  · simpa only [map_add,he] using hsum.add hv
  · simpa only [map_add,map_neg,he] using hsum.add hv.neg

 

theorem exists_halfEcho (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (ht : t≠0) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (ha : ∀i,ApproxPacket l (fun q => modeFock (d i q)))
    (c : κ → ℝ) (hc : ∀i,c i≠0)
    (hZ : ∀i,Tendsto (fun q => (⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (c i)))
    (address : α → ModeInfinity) (htrans : st.Transported (fun q => modeFock (address q)))
    (A : ℝ) (hA : 0≤A) (haddr : ∀ᶠ q in l,‖address q‖≤A) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse)
      (st' : PacketStage l r (fun q => (r q)⁻¹) (st.halfEchoCenter t a K) (fun i => 1-spin i)),
      (∀q,st'.word q=st.halfEchoWord t a K q) ∧
      (∀q x,st'.low.op q x=WZ (st.halfEchoResidual t a K q) (st.low.op q x)) ∧
      st'.Transported (fun q => -modeFock (address q)) ∧
      Tendsto (fun q => ‖st.halfEchoResidual t a K q-(-2*t) • address q‖) l (𝓝 0) ∧
      (∀i,ApproxPacket l (fun q => modeFock (st.halfEchoCenter t a K i q))) := by
  obtain ⟨K,a,ho,hs⟩ := st.exists_huge_selector_visible t ht (Real.pi/2) hr hp C hC hd ha c hc hZ
  have he := st.halfEchoResidual_tendsto address htrans t a K hp ho hs
  let G : ℝ := 1+2*|t| *A
  have hG : 0≤G := by dsimp only [G]; positivity
  have hg : ∀ᶠ q in l,‖st.halfEchoResidual t a K q‖≤G :=
    st.halfEchoResidual_bounded address t a K A hA haddr he
  let st' := st.halfEcho t a K G hG hg hp ho (fun x hx => hs _ (st.forward_special_packets t x hx))
  refine ⟨K,a,st',fun _ => rfl,fun _ _ => rfl,?_,he,?_⟩
  · exact htrans.halfEcho t a K G hG hg hp ho hs
  · exact st.halfEchoCenter_approx t a K st' (fun _ => rfl) hr hp ha

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree
namespace WeylWord
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}
  {d : α → ι → E} {d₀ : ι → F}

 

def family (w : List (WeylGate ι)) (hg : GramConverges l d d₀) : PacketUnitaryFamily (E:=E) l where
  op q := op (d q) w
  forward x hx := bounded w hx hg
  backward x hx := by simpa only [op_inv] using bounded (inv w) hx hg

theorem low_insertion_match (w : List (WeylGate ι)) (hg : GramConverges l d d₀)
    (A : PacketUnitaryFamily (E:=E) l) (hc : PacketUnitaryFamily.LowClose A (family w hg))
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    ApproxMatch l d d₀
      (fun q => (A.op q).symm (SpinOperators.act P (A.op q (vacuum E))))
      ((op d₀ w).symm (SpinOperators.act P (op d₀ w (vacuum F)))) := by
  exact (insertion_match w P hg).approx.close (hc.insertion P hP)

end WeylWord
end GramCalculus

namespace PointedTree
open CoherentFock RootSpin GramCalculus
namespace PacketStage
variable {F α κ ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype κ] [Fintype ι] {l : Filter α} {r : α → ℝ}
  {centers : κ → α → ModeInfinity} {spin : κ → Fin 2}
  {d : α → ι → ModeInfinity} {d₀ : ι → F}

 

theorem actual_insertion_match (st : PacketStage l r (fun q => (r q)⁻¹) centers spin)
    (w : List (WeylGate ι)) (hg : GramConverges l d d₀)
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family w hg))
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    ApproxMatch l d d₀
      (fun q => (ordinaryLocal (st.word q)).symm
        (SpinOperators.act P (ordinaryLocal (st.word q) (vacuum ModeInfinity))))
      ((WeylWord.op d₀ w).symm (SpinOperators.act P (WeylWord.op d₀ w (vacuum F)))) := by
  apply (WeylWord.low_insertion_match w hg st.low hc P hP).close
  exact low_insertion_tendsto _ st.low st.ordinary st.special st.phase r (fun q => (r q)⁻¹)
    P hP hr (hp.mono fun q hq => ⟨hq.le,(inv_pos.mpr hq).le,inv_mul_cancel₀ hq.ne'⟩)
    (Eventually.of_forall st.split) (st.special_norm.mono fun _ hq x => (hq x).le) st.ordinary_low

theorem insertionZ_match (st : PacketStage l r (fun q => (r q)⁻¹) centers spin)
    (w : List (WeylGate ι)) (hg : GramConverges l d d₀)
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family w hg))
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q) :
    ApproxMatch l d d₀ (fun q => modeFock (insertionInfinity (st.word q)))
      ((WeylWord.op d₀ w).symm (SpinOperators.act Z (WeylWord.op d₀ w (vacuum F)))) := by
  simpa only [modeFock_insertion] using st.actual_insertion_match w hg hc hr hp Z Z_unitary

theorem insertionY_match (st : PacketStage l r (fun q => (r q)⁻¹) centers spin)
    (w : List (WeylGate ι)) (hg : GramConverges l d d₀)
    (hc : PacketUnitaryFamily.LowClose st.low (WeylWord.family w hg))
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q) :
    ApproxMatch l d d₀ (fun q => modeFock (insertionYInfinity (st.word q)))
      ((WeylWord.op d₀ w).symm (SpinOperators.act Y (WeylWord.op d₀ w (vacuum F)))) := by
  simpa only [modeFock_insertionY] using st.actual_insertion_match w hg hc hr hp Y Y_unitary

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 
theorem ApproxPacket.inner_escape {x z : α → SpinSpace E} (hx : ApproxPacket l x)
    (hz : ∀q,‖z q‖=1)
    (hescape : ∀y,BoundedPacket l y → Tendsto (fun q => ⟪y q,z q⟫_ℂ) l (𝓝 0)) :
    Tendsto (fun q => ⟪x q,z q⟫_ℂ) l (𝓝 0) := by
  obtain ⟨y,hy,he⟩ := hx
  have hd : Tendsto (fun q => ⟪x q,z q⟫_ℂ-⟪y q,z q⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ he
    exact Eventually.of_forall fun q => by
      rw [←inner_sub_left]
      simpa only [hz,mul_one] using norm_inner_le_norm (𝕜:=ℂ) (x q-y q) (z q)
  simpa only [sub_add_cancel,zero_add] using hd.add (hescape y hy)

end CoherentFock

namespace SeedInitialization
open CoherentFock PointedTree GramCalculus

def seedDirections (b T : ℝ) (i : Fin 2) : ModeInfinity :=
  if i=0 then highInfinity (gamma b T) else addressInfinity b T

def seedBasis (i : Fin 2) : SeededTree.External := EuclideanSpace.single i 1

@[simp] theorem norm_seedDirections (b T : ℝ) (i : Fin 2) : ‖seedDirections b T i‖=1 := by
  unfold seedDirections
  split_ifs <;> simp only [norm_highInfinity,norm_addressInfinity]

@[simp] theorem seedBasis_inner (i j : Fin 2) :
    ⟪seedBasis i,seedBasis j⟫_ℂ=if i=j then 1 else 0 := by
  simp [seedBasis,EuclideanSpace.inner_single_left]

 

theorem seedDirections_gram (b : ℝ) (hb : 0<b) :
    GramConverges atTop (seedDirections b) seedBasis := by
  intro i j
  rw [seedBasis_inner]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    have he (T : ℝ) : ⟪seedDirections b T i,seedDirections b T i⟫_ℂ=1 := by
      rw [inner_self_eq_norm_sq_to_K,norm_seedDirections]; norm_num
    simp only [he]
    exact tendsto_const_nhds
  · simp only [hij,ite_false]
    fin_cases i <;> fin_cases j <;> try contradiction
    · simpa [seedDirections] using
        high_addressInfinity_orthogonal b hb
    · have ht := (Complex.continuous_conj.tendsto _).comp (high_addressInfinity_orthogonal b hb)
      simpa [Function.comp_def,seedDirections,inner_conj_symm] using ht

 

theorem seedDirections_escape (b : ℝ) (hb : 0<b) (x : ℝ → SpinSpace ModeInfinity)
    (hx : ApproxPacket atTop x) (i : Fin 2) :
    Tendsto (fun T => ⟪x T,modeFock (seedDirections b T i)⟫_ℂ) atTop (𝓝 0) := by
  apply hx.inner_escape (fun T => by rw [modeFock.norm_map,norm_seedDirections])
  intro y hy
  unfold seedDirections
  split_ifs
  · exact highInfinity_escapes b hb y hy
  · exact addressInfinity_escapes b hb y hy

 

theorem extend_dictionary {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ℝ) (hb : 0<b) (n : ℕ)
    (d : ℝ → ι → ModeInfinity) (d₀ : ι → SeededTree.TopMode n)
    (hg : GramConverges atTop d d₀)
    (z : ℝ → κ → ModeInfinity) (z₀ : κ → SeededTree.Mode n)
    (hz : ∀i,ApproxPacket atTop (fun T => modeFock (z T i)))
    (hm : ∀i,ApproxMatch atTop d d₀ (fun T => modeFock (z T i)) (z₀ i : SeededTree.Level n)) :
    GramConverges atTop
      (fun T => Sum.elim (seedDirections b T) (z T))
      (Sum.elim (fun i => SeededTree.external (n+1) (seedBasis i))
        (fun i => SeededTree.endogenous n (z₀ i))) := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simpa only [Sum.elim_inl,LinearIsometry.inner_map_map] using seedDirections_gram b hb i j
    | inr j =>
      simp only [Sum.elim_inl,Sum.elim_inr]
      rw [SeededTree.external_inner_endogenous n (seedBasis i) (z₀ j)]
      have ht := (Complex.continuous_conj.tendsto _).comp (seedDirections_escape b hb _ (hz j) i)
      simpa only [Function.comp_def,map_zero,inner_conj_symm,modeFock.inner_map_map] using ht
  | inr i =>
    cases j with
    | inl j =>
      simp only [Sum.elim_inl,Sum.elim_inr]
      have hh : ⟪SeededTree.endogenous n (z₀ i),SeededTree.external (n+1) (seedBasis j)⟫_ℂ=0 := by
        rw [←inner_conj_symm,SeededTree.external_inner_endogenous,map_zero]
      rw [hh]
      simpa only [modeFock.inner_map_map] using seedDirections_escape b hb _ (hz i) j
    | inr j =>
      simpa only [Sum.elim_inr,LinearIsometry.inner_map_map,Submodule.coe_inner,
        modeFock.inner_map_map] using (hm i).inner (hm j) hg

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree
variable {E F G α ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [Fintype ι] [Fintype κ] {l : Filter α}

@[simp] theorem combination_map (T : F →ₗᵢ[ℂ] G) (d : ι → F) (c : ι → ℂ) :
    combination (fun i => T (d i)) c=T (combination d c) := by
  simp only [combination,map_sum,map_smul]

@[simp] theorem combination_sum_zero (d : ι → E) (e : κ → E) (c : ι → ℂ) :
    combination (Sum.elim d e) (Sum.elim c 0)=combination d c := by
  simp [combination,Fintype.sum_sum_type]

namespace PacketMatch
variable {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}

 

theorem model_map (hx : PacketMatch l d d₀ x x₀) (T : F →ₗᵢ[ℂ] G) :
    PacketMatch l d (fun i => T (d₀ i)) x (spinMap (gammaEmbedding T) x₀) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  refine ⟨n,a,a₀,c,hx,?_,ha⟩
  rw [hx₀,spinMap_spinPacket]
  simp only [combination_map]

 

theorem weaken (hx : PacketMatch l d d₀ x x₀) (e : α → κ → E) (e₀ : κ → F) :
    PacketMatch l (fun q => Sum.elim (d q) (e q)) (Sum.elim d₀ e₀) x x₀ := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  refine ⟨n,a,a₀,fun i => Sum.elim (c i) 0,?_,?_,ha⟩
  · simpa only [combination_sum_zero] using hx
  · simpa only [combination_sum_zero] using hx₀

 
theorem reindex (hx : PacketMatch l d d₀ x x₀) (e : κ ≃ ι) :
    PacketMatch l (fun q j => d q (e j)) (fun j => d₀ (e j)) x x₀ := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  have hc (q : α) (i : Fin n) : combination (fun j => d q (e j)) (fun j => c i (e j))=
      combination (d q) (c i) := e.sum_comp (fun j => c i j • d q j)
  have hc₀ (i : Fin n) : combination (fun j => d₀ (e j)) (fun j => c i (e j))=
      combination d₀ (c i) := e.sum_comp (fun j => c i j • d₀ j)
  exact ⟨n,a,a₀,fun i j => c i (e j),by simpa only [hc] using hx,
    by simpa only [hc₀] using hx₀,ha⟩

end PacketMatch
namespace ApproxMatch
variable {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}

theorem model_map (hx : ApproxMatch l d d₀ x x₀) (T : F →ₗᵢ[ℂ] G) :
    ApproxMatch l d (fun i => T (d₀ i)) x (spinMap (gammaEmbedding T) x₀) := by
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨y,hy.model_map T,he⟩

theorem weaken (hx : ApproxMatch l d d₀ x x₀) (e : α → κ → E) (e₀ : κ → F) :
    ApproxMatch l (fun q => Sum.elim (d q) (e q)) (Sum.elim d₀ e₀) x x₀ := by
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨y,hy.weaken e e₀,he⟩

theorem reindex (hx : ApproxMatch l d d₀ x x₀) (e : κ ≃ ι) :
    ApproxMatch l (fun q j => d q (e j)) (fun j => d₀ (e j)) x x₀ := by
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨y,hy.reindex e,he⟩

end ApproxMatch
namespace GramConverges
variable {d : α → ι → E} {d₀ : ι → F}

omit [Fintype ι] in
theorem model_map (hg : GramConverges l d d₀) (T : F →ₗᵢ[ℂ] G) :
    GramConverges l d (fun i => T (d₀ i)) := by
  intro i j
  simpa only [T.inner_map_map] using hg i j

omit [Fintype ι] [Fintype κ] in
theorem reindex (hg : GramConverges l d d₀) (e : κ → ι) :
    GramConverges l (fun q j => d q (e j)) (fun j => d₀ (e j)) := fun i j => hg (e i) (e j)

end GramConverges
end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock PointedTree GramCalculus

 

structure CausalFrame (b : ℝ) (n : ℕ) (κ : Type*) [Fintype κ] where
  actual : ℝ → κ → ModeInfinity
  formal : κ → SeededTree.Mode n
  gram : GramConverges atTop
    (fun T => Sum.elim (seedDirections b T) (actual T))
    (Sum.elim (fun i => SeededTree.external (n+1) (seedBasis i))
      (fun i => SeededTree.endogenous n (formal i)))
  bounded : ∀i,ApproxPacket atTop (fun T => modeFock (actual T i))
  packet : ∀i,ApproxMatch atTop
    (fun T => Sum.elim (seedDirections b T) (actual T))
    (Sum.elim (fun i => SeededTree.external (n+1) (seedBasis i))
      (fun i => SeededTree.endogenous n (formal i)))
    (fun T => modeFock (actual T i))
    ((SeededTree.empty n).toLinearIsometry (formal i : SeededTree.Level n))

namespace CausalFrame
variable {b : ℝ} {n : ℕ} {κ : Type*} [Fintype κ]

def directions (f : CausalFrame b n κ) (T : ℝ) : Fin 2 ⊕ κ → ModeInfinity :=
  Sum.elim (seedDirections b T) (f.actual T)

def model (f : CausalFrame b n κ) : Fin 2 ⊕ κ → SeededTree.TopMode (n+1) :=
  Sum.elim (fun i => SeededTree.external (n+1) (seedBasis i))
    (fun i => SeededTree.endogenous n (f.formal i))

def initial (b : ℝ) (hb : 0<b) : CausalFrame b 0 PEmpty where
  actual _ := PEmpty.elim
  formal := PEmpty.elim
  gram := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa only [Sum.elim_inl,LinearIsometry.inner_map_map] using seedDirections_gram b hb i j
      | inr j => exact j.elim
    | inr i => exact i.elim
  bounded i := i.elim
  packet i := i.elim

 

def append (f : CausalFrame b n κ) (hb : 0<b)
    (z : ℝ → ModeInfinity) (z₀ : SeededTree.Mode (n+1))
    (hz : ApproxPacket atTop (fun T => modeFock (z T)))
    (hm : ApproxMatch atTop f.directions f.model (fun T => modeFock (z T))
      (z₀ : SeededTree.Level (n+1))) : CausalFrame b (n+1) (κ ⊕ Unit) where
  actual T := Sum.elim (f.actual T) (fun _ => z T)
  formal := Sum.elim (fun i => centeredMap (SeededTree.empty n) (f.formal i)) (fun _ => z₀)
  gram := by
    apply extend_dictionary b hb (n+1) f.directions f.model f.gram
    · intro i
      cases i with
      | inl i => exact f.bounded i
      | inr i => exact hz
    · intro i
      cases i with
      | inl i => exact f.packet i
      | inr i => exact hm
  bounded i := by
    cases i with
    | inl i => exact f.bounded i
    | inr i => exact hz
  packet i := by
    let old : Fin 2 ⊕ κ → SeededTree.TopMode (n+2) := fun j => SeededTree.topStep (n+1) (f.model j)
    let extra : Unit → SeededTree.TopMode (n+2) := fun _ => SeededTree.endogenous (n+1) z₀
    let e : Fin 2 ⊕ (κ ⊕ Unit) ≃ (Fin 2 ⊕ κ) ⊕ Unit := (Equiv.sumAssoc _ _ _).symm
    have ha (T : ℝ) : (fun j => Sum.elim (f.directions T) (fun _ : Unit => z T) (e j))=
        Sum.elim (seedDirections b T) (Sum.elim (f.actual T) (fun _ => z T)) := by
      funext j
      rcases j with j|j
      · rfl
      · rcases j with j|j <;> rfl
    have hf : (fun j => Sum.elim old extra (e j))=
        Sum.elim (fun j => SeededTree.external (n+1+1) (seedBasis j))
          (fun j => SeededTree.endogenous (n+1)
            (Sum.elim (fun i => centeredMap (SeededTree.empty n) (f.formal i)) (fun _ => z₀) j)) := by
      funext j
      rcases j with j|j
      · exact SeededTree.topStep_external (n+1) (seedBasis j)
      · rcases j with j|j
        · exact SeededTree.topStep_endogenous n (f.formal j)
        · rfl
    have transport (x : ℝ → SpinSpace ModeInfinity) (x₀ : SeededTree.Level (n+1))
        (hx : ApproxMatch atTop f.directions f.model x x₀) :
        ApproxMatch atTop
          (fun T => Sum.elim (seedDirections b T) (Sum.elim (f.actual T) (fun _ : Unit => z T)))
          (Sum.elim (fun j => SeededTree.external (n+1+1) (seedBasis j))
            (fun j => SeededTree.endogenous (n+1)
              (Sum.elim (fun i => centeredMap (SeededTree.empty n) (f.formal i)) (fun _ : Unit => z₀) j)))
          x ((SeededTree.empty (n+1)).toLinearIsometry x₀) := by
      have hh := (((hx.model_map (SeededTree.topStep (n+1))).weaken
        (fun T (_ : Unit) => z T) extra).reindex e)
      change ApproxMatch atTop (fun T j => Sum.elim (f.directions T) (fun _ : Unit => z T) (e j))
        (fun j => Sum.elim old extra (e j)) x _ at hh
      have hfun : (fun T j => Sum.elim (f.directions T) (fun _ : Unit => z T) (e j))=
          (fun T => Sum.elim (seedDirections b T) (Sum.elim (f.actual T) (fun _ => z T))) := by
        funext T; exact ha T
      rw [hfun,hf] at hh
      rw [SeededTree.empty_apply]
      exact hh
    cases i with
    | inl i => exact transport _ _ (f.packet i)
    | inr i => exact transport _ _ hm

end CausalFrame
end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock

 

@[simp] theorem modeFock_shift (d : ModeInfinity) :
    modeFock (shiftInfinity d)=plusEmbedding (creationVacuum d) := by
  have hc : Continuous (fun d : ModeInfinity => plusEmbedding (creationVacuum d)) :=
    plusEmbedding.continuous.comp creationEmbedding.continuous
  have he := (HilbertChain.denseRange_embed ModeSpace modeStep).equalizer
    (modeFock.continuous.comp shiftInfinity.continuous) hc
  apply congrFun (he ?_) d
  funext z
  rcases z with ⟨n,x⟩
  change modeFock (shiftInfinity (modeEmbed n x))=plusEmbedding (creationVacuum (modeEmbed n x))
  rw [shiftInfinity_embed]
  change unfoldTree (modeInWhole (modeEmbed (n+1) (rootShift n x)))=_
  rw [modeInWhole_embed,unfoldTree_embed_succ,rootShift_coe]
  change spinMap (gammaEmbedding (modeEmbed n)) (plusEmbedding (creationVacuum x))=_
  rw [spinMap_plusEmbedding]
  congr 1
  exact Gamma_creationVacuum (modeEmbed n) x

 theorem energyInfinity_fock (d : ModeInfinity) :
    energyInfinity d=(⟪modeFock d,plusEmbedding (creationVacuum d)⟫_ℂ).re := by
  rw [←modeFock_shift,modeFock.inner_map_map]
  rfl

end PointedTree

end

end OAI
