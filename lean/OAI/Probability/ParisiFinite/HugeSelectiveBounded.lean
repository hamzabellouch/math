import Mathlib
import OAI.Probability.ParisiFinite.RotationAccuracy

namespace OAI

/-! Huge Selective Bounded. -/

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
namespace PointedTree
open CoherentFock RootSpin
local instance hpsRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance hpsRealSMul : SMul ℝ ModeInfinity := hpsRealModule.toDistribMulAction.toSMul

 

theorem huge_selective_bounded {α κ : Type*} [Fintype κ] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (t : ℝ) (ht : t≠0)
    (o s xp xm : α → SpinSpace ModeInfinity)
    (hxp : BoundedPacket l xp) (hxm : BoundedPacket l xm)
    (d : κ → α → ModeInfinity) (spin : κ → Fin 2)
    (hs : PacketExpansion (l:=l) S r d spin s)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (c y : κ → ℝ) (hc : ∀i,c i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0≤r q)
    (hS : Tendsto S l atTop) (hscale : ∀ᶠ q in l,S q*r q=1)
    (hψ : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=o q+s q)
    (ho : Tendsto (fun q => S q*‖o q-(spinW ((S q:ℂ) • ((-t) • insertionInfinity (w q))) (xp q)+
      spinW ((S q:ℂ) • (t • insertionInfinity (w q))) (xm q))‖) l (𝓝 0))
    (hop : ∀q,SpinOperators.act Z (xp q)=xp q)
    (hom : ∀q,SpinOperators.act Z (xm q)= -xm q)
    (hZ : ∀i,Tendsto (fun q => (⟪insertionInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (c i)))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (y i))) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀ (b : ℝ) z,BoundedPacket l z →
        Tendsto (fun q => S q*‖probeGain (r q) (w q) a K
          (spinW ((S q:ℂ) • (b • insertionInfinity (w q))) (z q))-
            spinW ((S q:ℂ) • (b • insertionInfinity (w q))) (z q)‖) l (𝓝 0)) ∧
      (∀ z,PacketExpansion (l:=l) S r d spin z →
        Tendsto (fun q => S q*‖probeGain (r q) (w q) a K (z q)-
          SpinOperators.act (R θ) (z q)‖) l (𝓝 0)) := by
  classical
  obtain ⟨τ,hτ,_,hsp⟩ := hs
  let tails : (Fin 2 ⊕ κ) → α → SpinSpace ModeInfinity := Sum.elim (fun i => if i=0 then xp else xm) τ
  have htails : ∀i,BoundedPacket l (tails i) := by
    intro i
    cases i with
    | inl i => fin_cases i <;> simpa [tails] using (show BoundedPacket l _ from by assumption)
    | inr i => exact hτ i
  obtain ⟨p,B,A,hB,hA,heq,hbd⟩ := BoundedPacket.finite_uniform tails htails
  let pp := p (Sum.inl 0)
  let pm := p (Sum.inl 1)
  let z (i : κ) := p (Sum.inr i)
  have hpp : ∀q,xp q=spinCoe (pp q) := by simpa [tails,pp] using heq (Sum.inl 0)
  have hpm : ∀q,xm q=spinCoe (pm q) := by simpa [tails,pm] using heq (Sum.inl 1)
  have hz : ∀i q,τ i q=spinCoe (z i q) := fun i q => heq (Sum.inr i) q
  let op (q : α) := actualPacket (S q) ((-t) • insertionInfinity (w q)) (pp q)
  let om (q : α) := actualPacket (S q) (t • insertionInfinity (w q)) (pm q)
  let xs (i : κ) (q : α) := (r q:ℂ) • z i q
  let sp (q : α) := ∑i,actualPacket (S q) (d i q) (xs i q)
  let ρ (q : α) := (o q-(op q+om q))+(s q-sp q)
  have ho' : Tendsto (fun q => S q*‖o q-(op q+om q)‖) l (𝓝 0) := by
    simpa only [op,om,actualPacket,hpp,hpm,Complex.coe_smul] using ho
  have hsp' : Tendsto (fun q => S q*‖s q-sp q‖) l (𝓝 0) := by
    have hh (q : α) : sp q=∑i,(r q:ℂ) • actualPacket (S q) (d i q) (z i q) := by
      simp only [sp,xs,actualPacket_smul]
    simpa only [hh,actualPacket,hz,Complex.coe_smul] using hsp
  have hS0 : ∀ᶠ q in l,0≤S q := hS.eventually (eventually_ge_atTop 0)
  have hscl : ∀ᶠ q in l,0≤S q ∧ 0≤r q ∧ S q*r q=1 := by
    filter_upwards [hS0,hp,hscale] with q hq hpq he
    exact ⟨hq,hpq,he⟩
  have hρ : Tendsto (fun q => S q*‖ρ q‖) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [add_zero] using ho'.add hsp')
    · filter_upwards [hS0] with q hq
      exact mul_nonneg hq (norm_nonneg _)
    · filter_upwards [hS0] with q hq
      simpa only [ρ,mul_add] using mul_le_mul_of_nonneg_left
        (norm_add_le (o q-(op q+om q)) (s q-sp q)) hq
  have hxs : ∀i,∀ᶠ q in l,SpinRadiusLE (xs i q) B ∧ spinMass (xs i q)≤A := by
    intro i
    filter_upwards [hbd,hp,hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with q hq hpq hu
    refine ⟨(hq (Sum.inr i)).1.smul _,?_⟩
    simp only [xs,spinMass_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpq]
    exact (mul_le_mul_of_nonneg_left (hq (Sum.inr i)).2 hpq).trans (mul_le_of_le_one_left hA hu.le)
  have hnorm : ∀ᶠ q in l,‖∑i,actualPacket (S q) (d i q) (z i q)‖≤Fintype.card κ*A := by
    filter_upwards [hbd] with q hq
    calc
      _ ≤ ∑i,‖actualPacket (S q) (d i q) (z i q)‖ := norm_sum_le _ _
      _ ≤ ∑_i : κ,A := Finset.sum_le_sum (fun i _ => (norm_actualPacket_le_mass ..).trans (hq (Sum.inr i)).2)
      _ = _ := by simp
  have hssq := ForwardControl.scaled_square_small_amplitude S r
    (fun q => ∑i,actualPacket (S q) (d i q) (z i q)) (Fintype.card κ*A) (by positivity) hr hscl hnorm
  have hvac : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=op q+om q+sp q+ρ q := by
    filter_upwards [hψ] with q hq
    rw [hq]
    dsimp only [ρ]
    abel
  have hopp : ∀ᶠ q in l,SpinOperators.act Z (op q)=op q := Eventually.of_forall fun q => by
    simp only [op,actualPacket,←spinW_root,←hpp,hop]
  have homm : ∀ᶠ q in l,SpinOperators.act Z (om q)= -om q := Eventually.of_forall fun q => by
    simp only [om,actualPacket,←spinW_root,←hpm,hom,map_neg]
  obtain ⟨K,a,hoi,hsi⟩ := huge_selective_accuracy r S w t ht d pp pm xs ρ B A hB hA c y hc θ
    hr hp hS hscale (hbd.mono fun _ hq => hq (Sum.inl 0)) (hbd.mono fun _ hq => hq (Sum.inl 1))
    hxs hZ hvac hopp homm hρ (by simpa only [sp,xs,actualPacket_smul,←Finset.smul_sum] using hssq)
  refine ⟨K,a,?_,?_⟩
  · intro b u hu
    obtain ⟨p',B',A',hB',hA',hu,hp'⟩ := hu
    simpa only [hu,actualPacket,Complex.coe_smul] using hoi b p' B' A' hB' hA' hp'
  · intro u hu
    apply hu.rotation_accuracy (fun q => probeGain (r q) (w q) a K) θ hS0
      (by filter_upwards [hp,hscale] with q hq he; exact ⟨hq,he⟩)
    intro i u' hu'
    obtain ⟨p',B',A',hB',hA',hu',hp'⟩ := hu'
    have hZ' : Tendsto (fun q => -2*(⟪insertionInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (-2*c i)) :=
      (hZ i).const_mul _
    simpa only [hu',actualPacket,Complex.coe_smul] using
      hsi i (d i) p' C B' A' hC hB' hA' (hd i) hp' hZ' (hY i)

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
open RootSpin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem real_neg_div_scale (r t : ℝ) (v : E) :
    -(t/r) • v = ((r⁻¹:ℝ):ℂ) • ((-t) • v) := by
  rw [Complex.coe_smul,smul_smul]
  congr 1
  ring

theorem real_div_scale (r t : ℝ) (v : E) :
    (t/r) • v = ((r⁻¹:ℝ):ℂ) • (t • v) := by
  rw [Complex.coe_smul,smul_smul]
  congr 1
  ring

theorem complex_neg_real_smul (t : ℝ) (v : E) : -(t:ℂ) • v=(-t) • v := by
  rw [←Complex.ofReal_neg,Complex.coe_smul]

theorem WZ_split_two (v : E) (x : SpinSpace E) :
    WZ v x=spinW v (projectSpin 0 x)+spinW (-v) (projectSpin 1 x) := by
  conv_lhs => rw [←projectSpin_sum x,map_sum]
  simp only [Fin.sum_univ_two,WZ_project,signedMode,ite_true]
  rfl

theorem rootZ_project_zero (x : SpinSpace E) :
    SpinOperators.act Z (projectSpin 0 x)=projectSpin 0 x := by
  ext i
  fin_cases i <;> simp [SpinOperators.act_apply,Z,projectSpin_apply]

theorem rootZ_project_one (x : SpinSpace E) :
    SpinOperators.act Z (projectSpin 1 x)= -projectSpin 1 x := by
  ext i
  fin_cases i <;> simp [SpinOperators.act_apply,Z,projectSpin_apply]

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance hsRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance hsRealSMul : SMul ℝ ModeInfinity := hsRealModule.toDistribMulAction.toSMul

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

def forwardWord (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (t : ℝ) (q : α) : List Gate :=
  .cost (t/r q)::st.word q

def forwardVector (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (t : ℝ) (q : α) : ModeInfinity :=
  -(t/r q) • insertionInfinity (st.word q)

def forwardCenter (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (t : ℝ) (i : κ) (q : α) : ModeInfinity :=
  d i q+signedMode (spin i) ((-t) • insertionInfinity (st.word q))

theorem forwardVector_scale (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (t : ℝ) (q : α) :
    st.forwardVector t q=(((r q)⁻¹:ℝ):ℂ) • ((-t) • insertionInfinity (st.word q)) := by
  apply real_neg_div_scale

theorem forward_special_packets (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (t : ℝ)
    (x : α → SpinSpace ModeInfinity) (hx : BoundedPacket l x) :
    PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin
      (fun q => WZ (st.forwardVector t q) (st.special q (x q))) := by
  have hh := (st.special_packets x hx).huge_cost (fun q => (-t) • insertionInfinity (st.word q))
  change PacketExpansion (l:=l) (fun q => (r q)⁻¹) r
    (fun i q => d i q+signedMode (spin i) ((-t) • insertionInfinity (st.word q))) spin _
  simpa only [forwardVector_scale] using hh

 

theorem exists_huge_selector (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (ht : t≠0) (θ : ℝ) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖st.forwardCenter t i q‖≤C)
    (c y : κ → ℝ) (hc : ∀i,c i≠0)
    (hZ : ∀i,Tendsto (fun q => (⟪insertionInfinity (st.forwardWord t q),st.forwardCenter t i q⟫_ℂ).im) l (𝓝 (c i)))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (st.forwardWord t q),st.forwardCenter t i q⟫_ℂ).im) l (𝓝 (y i))) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀x,BoundedPacket l x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
          (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0)) ∧
      (∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin x →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (x q)-
          SpinOperators.act (R θ) (x q)‖) l (𝓝 0)) := by
  let low (q : α) := st.phase q • st.low.op q (vacuum ModeInfinity)
  let xp (q : α) := projectSpin 0 (low q)
  let xm (q : α) := projectSpin 1 (low q)
  let o (q : α) := WZ (st.forwardVector t q) (st.ordinary q (vacuum ModeInfinity))
  let s (q : α) := WZ (st.forwardVector t q) (st.special q (vacuum ModeInfinity))
  have hlow : BoundedPacket l low := st.low_bounded _ BoundedPacket.vacuum
  have hfw (q : α) : insertionInfinity (st.forwardWord t q)=insertionInfinity (st.word q) :=
    insertionInfinity_cost _ _
  have hsplit (q : α) (x : SpinSpace ModeInfinity) :
      WZ (st.forwardVector t q) x=
        spinW ((((r q)⁻¹:ℝ):ℂ) • ((-t) • insertionInfinity (st.forwardWord t q))) (projectSpin 0 x)+
        spinW ((((r q)⁻¹:ℝ):ℂ) • (t • insertionInfinity (st.forwardWord t q))) (projectSpin 1 x) := by
    rw [WZ_split_two,forwardVector_scale,hfw]
    simp only [neg_smul,smul_neg,neg_neg]
  have hψ : ∀ᶠ q in l,ordinaryLocal (st.forwardWord t q) (vacuum ModeInfinity)=o q+s q := by
    exact Eventually.of_forall fun q => by
      change ordinaryLocal (.cost (t/r q)::st.word q) (vacuum ModeInfinity)=_
      rw [ordinaryLocal_cost,st.split,map_add]
      simp only [o,s,forwardVector,complex_neg_real_smul]
  have ho : Tendsto (fun q => (r q)⁻¹*‖o q-(
      spinW ((((r q)⁻¹:ℝ):ℂ) • ((-t) • insertionInfinity (st.forwardWord t q))) (xp q)+
      spinW ((((r q)⁻¹:ℝ):ℂ) • (t • insertionInfinity (st.forwardWord t q))) (xm q))‖) l (𝓝 0) := by
    simpa only [xp,xm,←hsplit,o,low,←map_sub,norm_WZ] using st.ordinary_low _ BoundedPacket.vacuum
  have hS : Tendsto (fun q => (r q)⁻¹) l atTop := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hr,hp⟩)
  obtain ⟨K,a,hord,hsp⟩ := huge_selective_bounded r (fun q => (r q)⁻¹) (st.forwardWord t) t ht
    o s xp xm (hlow.project 0) (hlow.project 1) (st.forwardCenter t) spin
    (st.forward_special_packets t _ BoundedPacket.vacuum) C hC hd c y hc θ hr
    (hp.mono fun _ hq => hq.le) hS (hp.mono fun _ hq => inv_mul_cancel₀ hq.ne') hψ ho
    (fun q => rootZ_project_zero (low q)) (fun q => rootZ_project_one (low q)) hZ hY
  refine ⟨K,a,?_,hsp⟩
  intro x hx
  have h1 := hord (-t) _ (hx.project 0)
  have h2 := hord t _ (hx.project 1)
  have hh := ForwardControl.scaled_identity_add (fun q => probeGain (r q) (st.forwardWord t q) a K)
    (fun q => (r q)⁻¹) _ _ (hp.mono fun _ hq => (inv_pos.mpr hq).le) h1 h2
  simpa only [hsplit] using hh

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance heRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance heRealSMul : SMul ℝ ModeInfinity := heRealModule.toDistribMulAction.toSMul

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

def halfEchoWord (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) : List Gate :=
  .cost (-(t/r q))::probePrefix (r q) (st.forwardWord t q) a K

def reverseVector (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) : ModeInfinity :=
  (t/r q) • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)

def halfEchoResidual (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) : ModeInfinity :=
  (t/r q) • (insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)-insertionInfinity (st.word q))

def halfEchoPhase (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) : ℂ :=
  CoherentFock.phase (st.reverseVector t a K q) (st.forwardVector t q)

def halfEchoCenter (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (i : κ) (q : α) : ModeInfinity :=
  st.forwardCenter t i q+signedMode (1-spin i)
    (t • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K))

def halfEchoGain (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) :
    SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  wordGain (st.word q) (st.halfEchoWord t a K q)

theorem halfEchoGain_apply (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) (x : SpinSpace ModeInfinity) :
    st.halfEchoGain t a K q x=WZ (st.reverseVector t a K q)
      (probeGain (r q) (st.forwardWord t q) a K (WZ (st.forwardVector t q) x)) := by
  rw [halfEchoGain,wordGain_apply,halfEchoWord,ordinaryLocal_cost,←probeGain_on_local,
    forwardWord,ordinaryLocal_cost]
  simp only [LinearIsometryEquiv.apply_symm_apply,Complex.ofReal_neg,neg_neg]
  simp only [reverseVector,forwardVector,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_neg]
  rfl

theorem halfEcho_identity_exact (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) (x : SpinSpace ModeInfinity) :
    WZ (st.reverseVector t a K q) (WZ (st.forwardVector t q) x)=
      st.halfEchoPhase t a K q • WZ (st.halfEchoResidual t a K q) x := by
  rw [←ContinuousLinearMap.comp_apply,WZ_mul]
  have he : st.reverseVector t a K q+st.forwardVector t q=st.halfEchoResidual t a K q := by
    simp only [reverseVector,forwardVector,halfEchoResidual,neg_smul,sub_eq_add_neg,smul_add,smul_neg]
  rw [he]
  rfl

theorem reverseVector_scale (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) :
    st.reverseVector t a K q=(((r q)⁻¹:ℝ):ℂ) •
      (t • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K)) := by
  apply real_div_scale

 

def halfEcho (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (G : ℝ) (hG : 0≤G)
    (hg : ∀ᶠ q in l,‖st.halfEchoResidual t a K q‖≤G)
    (hp : ∀ᶠ q in l,0<r q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
        (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0))
    (hs : ∀x,BoundedPacket l x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
        (WZ (st.forwardVector t q) (st.special q (x q)))-
        SpinOperators.act (R (Real.pi/2)) (WZ (st.forwardVector t q) (st.special q (x q)))‖) l (𝓝 0)) :
    PacketStage l r (fun q => (r q)⁻¹) (st.halfEchoCenter t a K) (fun i => 1-spin i) where
  word := st.halfEchoWord t a K
  ordinary q := (st.halfEchoGain t a K q).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.ordinary q)
  special q := (st.halfEchoGain t a K q).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.special q)
  split q x := by
    change ordinaryLocal (st.halfEchoWord t a K q) x=st.halfEchoGain t a K q (st.ordinary q x)+st.halfEchoGain t a K q (st.special q x)
    rw [←map_add,←st.split]
    simp only [halfEchoGain,wordGain_apply,LinearIsometryEquiv.symm_apply_apply]
  special_norm := by
    filter_upwards [st.special_norm] with q hq x
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.norm_map] using hq x
  low := st.low.trans (PacketUnitaryFamily.pulse (st.halfEchoResidual t a K) G hG hg)
  phase q := st.halfEchoPhase t a K q*st.phase q
  phase_norm q := by rw [norm_mul,halfEchoPhase,norm_phase,st.phase_norm,mul_one]
  ordinary_low x hx := by
    let low (q : α) := st.phase q • st.low.op q (x q)
    have hp0 : ∀ᶠ q in l,0≤(r q)⁻¹ := hp.mono fun _ hq => (inv_pos.mpr hq).le
    have h1 : Tendsto (fun q => (r q)⁻¹*‖st.halfEchoGain t a K q (st.ordinary q (x q))-
        st.halfEchoGain t a K q (low q)‖) l (𝓝 0) := by
      simpa only [←map_sub,LinearIsometryEquiv.norm_map] using st.ordinary_low x hx
    have h2 : Tendsto (fun q => (r q)⁻¹*‖st.halfEchoGain t a K q (low q)-
        st.halfEchoPhase t a K q • WZ (st.halfEchoResidual t a K q) (low q)‖) l (𝓝 0) := by
      simpa only [halfEchoGain_apply,←halfEcho_identity_exact,←map_sub,norm_WZ] using
        ho low (st.low_bounded x hx)
    have hh := ForwardControl.scaled_triangle (fun q => (r q)⁻¹) _ _ _ hp0 h1 h2
    change Tendsto (fun q => (r q)⁻¹*‖st.halfEchoGain t a K q (st.ordinary q (x q))-
      (st.halfEchoPhase t a K q*st.phase q) • WZ (st.halfEchoResidual t a K q) (st.low.op q (x q))‖) l (𝓝 0)
    simpa only [low,map_smul,smul_smul] using hh
  special_packets x hx := by
    have hS : ∀ᶠ q in l,0≤(r q)⁻¹ := hp.mono fun _ hq => (inv_pos.mpr hq).le
    have hu := ((st.forward_special_packets t x hx).half_mixer).close hS (hs x hx)
    have hh := hu.huge_cost (fun q => t • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K))
    change PacketExpansion (l:=l) (fun q => (r q)⁻¹) r
      (fun i q => st.forwardCenter t i q+signedMode (1-spin i)
        (t • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K))) (fun i => 1-spin i)
      (fun q => st.halfEchoGain t a K q (st.special q (x q)))
    simpa only [halfEchoGain_apply,reverseVector_scale] using hh

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance hcRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance hcRealSMul : SMul ℝ ModeInfinity := hcRealModule.toDistribMulAction.toSMul

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem forward_four (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t θ : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (hp : ∀ᶠ q in l,0<r q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
        (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0))
    (hs : ∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (x q)-
        SpinOperators.act (R θ) (x q)‖) l (𝓝 0)) :
    let o := fun q => WZ (st.forwardVector t q) (st.ordinary q (vacuum ModeInfinity))
    let s := fun q => WZ (st.forwardVector t q) (st.special q (vacuum ModeInfinity))
    Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (o q)-o q‖) l (𝓝 0) ∧
    Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (s q)-SpinOperators.act (R θ) (s q)‖) l (𝓝 0) ∧
    Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (SpinOperators.act Z (o q))-
      SpinOperators.act Z (o q)‖) l (𝓝 0) ∧
    Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (SpinOperators.act Z (s q))-
      SpinOperators.act (R θ) (SpinOperators.act Z (s q))‖) l (𝓝 0) := by
  dsimp only
  let low (q : α) := st.phase q • st.low.op q (vacuum ModeInfinity)
  let V (q : α) := probeGain (r q) (st.forwardWord t q) a K
  have hlow : BoundedPacket l low := st.low_bounded _ BoundedPacket.vacuum
  have hS : ∀ᶠ q in l,0≤(r q)⁻¹ := hp.mono fun _ hq => (inv_pos.mpr hq).le
  have he : Tendsto (fun q => (r q)⁻¹*‖WZ (st.forwardVector t q) (st.ordinary q (vacuum ModeInfinity))-
      WZ (st.forwardVector t q) (low q)‖) l (𝓝 0) := by
    simpa only [←map_sub,norm_WZ] using st.ordinary_low _ BoundedPacket.vacuum
  have h1 := ForwardControl.scaled_identity_transfer V (fun q => (r q)⁻¹) _ _ hS (ho low hlow) he
  have heZ : Tendsto (fun q => (r q)⁻¹*‖SpinOperators.act Z
      (WZ (st.forwardVector t q) (st.ordinary q (vacuum ModeInfinity)))-
      SpinOperators.act Z (WZ (st.forwardVector t q) (low q))‖) l (𝓝 0) := by
    simpa only [←map_sub,SpinOperators.norm_act Z_unitary] using he
  have hZlow : Tendsto (fun q => (r q)⁻¹*‖V q (SpinOperators.act Z (WZ (st.forwardVector t q) (low q)))-
      SpinOperators.act Z (WZ (st.forwardVector t q) (low q))‖) l (𝓝 0) := by
    simpa only [WZ_rootZ_apply,V] using ho _ (hlow.root Z)
  have h3 := ForwardControl.scaled_identity_transfer V (fun q => (r q)⁻¹) _ _ hS hZlow heZ
  have hpack := st.forward_special_packets t _ BoundedPacket.vacuum
  exact ⟨h1,hs _ hpack,h3,hs _ hpack.rootZ⟩

 

theorem halfEchoResidual_tendsto (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (address : α → ModeInfinity) (ht : st.Transported (fun q => modeFock (address q)))
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (hp : ∀ᶠ q in l,0<r q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
        (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0))
    (hs : ∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (x q)-
        SpinOperators.act (R (Real.pi/2)) (x q)‖) l (𝓝 0)) :
    Tendsto (fun q => ‖st.halfEchoResidual t a K q-(-2*t) • address q‖) l (𝓝 0) := by
  let o (q : α) := WZ (st.forwardVector t q) (st.ordinary q (vacuum ModeInfinity))
  let s (q : α) := WZ (st.forwardVector t q) (st.special q (vacuum ModeInfinity))
  obtain ⟨h1,h2,h3,h4⟩ := st.forward_four t (Real.pi/2) a K hp ho hs
  have hx (q : α) : ordinaryLocal (st.forwardWord t q) (vacuum ModeInfinity)=o q+s q := by
    simp only [forwardWord,ordinaryLocal_cost,st.split,map_add,o,s,forwardVector,complex_neg_real_smul]
  have htc : Tendsto (fun q => ‖(r q)⁻¹ • (ordinaryLocal (st.forwardWord t q)).symm
      (SpinOperators.act Z (s q))-modeFock (address q)‖) l (𝓝 0) := by
    have he (q : α) : (ordinaryLocal (st.forwardWord t q)).symm (SpinOperators.act Z (s q))=
        (ordinaryLocal (st.word q)).symm (SpinOperators.act Z (st.special q (vacuum ModeInfinity))) := by
      simpa only [forwardWord,s,forwardVector,complex_neg_real_smul] using
        cost_transport_exact (st.word q) (t/r q) (st.special q (vacuum ModeInfinity))
    simpa only [he,Complex.coe_smul,Transported] using ht
  have hh := actual_flip_mode_tendsto r (st.forwardWord t) a K o s address
    (SpinOperators.act (R (Real.pi/2))) half_mixer_anticommutes hx t hp h1 h2 h3 h4 htc
  simpa only [halfEchoResidual,forwardWord,insertionInfinity_cost] using hh

 

theorem halfEchoResidual_bounded (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (address : α → ModeInfinity) (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ)
    (A : ℝ) (_hA : 0≤A) (ha : ∀ᶠ q in l,‖address q‖≤A)
    (he : Tendsto (fun q => ‖st.halfEchoResidual t a K q-(-2*t) • address q‖) l (𝓝 0)) :
    ∀ᶠ q in l,‖st.halfEchoResidual t a K q‖≤1+2*|t| * A := by
  filter_upwards [ha,he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with q haq heq
  have hn := norm_le_norm_sub_add (st.halfEchoResidual t a K q) ((-2*t) • address q)
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_neg] at hn
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hn
  nlinarith [abs_nonneg t]

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
open RootSpin
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

def preProject (i : Fin 2) (x : PreSpin E) : PreSpin E := fun j => if j=i then x j else 0

@[simp] theorem spinCoe_preProject (i : Fin 2) (x : PreSpin E) :
    spinCoe (preProject i x)=projectSpin i (spinCoe x) := by
  ext j
  simp only [spinCoe_apply,preProject,projectSpin_apply]
  split_ifs <;> rfl

omit [InnerProductSpace ℂ E] in
theorem preProject_radius (i : Fin 2) (x : PreSpin E) (B : ℝ) (hx : SpinRadiusLE x B) :
    SpinRadiusLE (preProject i x) B := by
  intro j
  simp only [preProject]
  split_ifs
  · exact hx j
  · exact RadiusLE.zero B

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem preProject_mass (i : Fin 2) (x : PreSpin E) : spinMass (preProject i x) ≤ spinMass x := by
  apply Finset.sum_le_sum
  intro j _
  simp only [preProject]
  split_ifs
  · exact le_rfl
  · simpa only [mass_zero] using mass_nonneg (x j)

 

theorem transverse_WZ_bounded (R : α → ℝ) (v : α → E)
    (x y : α → SpinSpace E) (hx : BoundedPacket l x) (hy : BoundedPacket l y)
    (hR : Tendsto R l atTop) (δ : ℝ) (hδ : 0<δ)
    (hsep : ∀ᶠ q in l,δ≤‖v q-(-v q)‖) :
    Tendsto (fun q => ⟪SpinOperators.act Y (WZ ((R q:ℂ) • v q) (x q)),
      WZ ((R q:ℂ) • v q) (y q)⟫_ℂ) l (𝓝 0) := by
  let z : Fin 2 → α → SpinSpace E := ![x,y]
  have hz : ∀i,BoundedPacket l (z i) := by intro i; fin_cases i <;> assumption
  obtain ⟨p,B,A,hB,hA,hp,hbd⟩ := BoundedPacket.finite_uniform z hz
  let tail (i j : Fin 2) (q : α) := preProject j (p i q)
  have ht (i j : Fin 2) : ∀ᶠ q in l,SpinRadiusLE (tail i j q) B ∧ spinMass (tail i j q)≤A := by
    filter_upwards [hbd] with q hq
    exact ⟨preProject_radius j _ B (hq i).1,(preProject_mass j _).trans (hq i).2⟩
  have hs : ∀ᶠ q in l,tail 0 0 q 1=0 ∧ tail 0 1 q 0=0 ∧ tail 1 0 q 1=0 ∧ tail 1 1 q 0=0 :=
    Eventually.of_forall fun q => by simp [tail,preProject]
  have hh := tendsto_inner_rootY_hugePacket R v (fun q => -v q)
    (tail 0 0) (tail 0 1) (tail 1 0) (tail 1 1) hR B A δ hA hδ
    (ht 0 0) (ht 0 1) (ht 1 0) (ht 1 1) hs hsep
  have he (i : Fin 2) (q : α) : hugePacket (R q) (v q) (-v q) (tail i 0 q) (tail i 1 q)=
      WZ ((R q:ℂ) • v q) (z i q) := by
    simp only [hugePacket,tail,spinCoe_preProject]
    rw [←hp i q,WZ_split_two]
    simp only [smul_neg,Complex.coe_smul]
  simpa only [he,z,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using hh

theorem unit_opposite_separation (v : E) (hv : ‖v‖=1) (t : ℝ) :
    ‖(-t) • v-(-((-t) • v))‖=2*|t| := by
  have hn : -((-t) • v)=t • v := by simp
  rw [hn,←sub_smul,norm_smul,Real.norm_eq_abs,hv,mul_one]
  have he : -t-t=-(2*t) := by ring
  rw [he,abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance htRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance htRealSMul : SMul ℝ ModeInfinity := htRealModule.toDistribMulAction.toSMul
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem actual_low_norm (st : PacketStage l r S d spin)
    (hr : Tendsto r l (𝓝 0)) (hS : ∀ᶠ q in l,1≤S q)
    (x : α → SpinSpace ModeInfinity) (hx : BoundedPacket l x) :
    Tendsto (fun q => ‖ordinaryLocal (st.word q) (x q)-st.phase q • st.low.op q (x q)‖) l (𝓝 0) := by
  have ho := PacketGeometry.tendsto_of_scaled S _ hS
    (Eventually.of_forall fun q => norm_nonneg _) (st.ordinary_low x hx)
  obtain ⟨C,hC,hxC⟩ := hx.norm_bounded
  have hs : Tendsto (fun q => ‖st.special q (x q)‖) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _
      (by simpa only [zero_mul] using hr.mul_const C)
    filter_upwards [st.special_norm,hxC] with q hq hxq
    have hrq : 0≤r q := by
      have hh := hq (vacuum ModeInfinity)
      rw [norm_vacuum,mul_one] at hh
      exact hh ▸ norm_nonneg _
    rw [hq]
    exact mul_le_mul_of_nonneg_left hxq hrq
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _
    (by simpa only [add_zero] using ho.add hs)
  exact Eventually.of_forall fun q => by
    rw [st.split]
    have he : st.ordinary q (x q)+st.special q (x q)-st.phase q • st.low.op q (x q)=
        (st.ordinary q (x q)-st.phase q • st.low.op q (x q))+st.special q (x q) := by abel
    rw [he]
    exact norm_add_le _ _

 

theorem huge_transverse_bounded (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (ht : t≠0) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (η : α → SpinSpace ModeInfinity) (hη : BoundedPacket l η) :
    Tendsto (fun q => ⟪modeFock (insertionYInfinity (st.forwardWord t q)),η q⟫_ℂ) l (𝓝 0) := by
  have hR : Tendsto (fun q => (r q)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hr,hp⟩)
  let x (q : α) := st.phase q • st.low.op q (vacuum ModeInfinity)
  let y (q : α) := st.phase q • st.low.op q (η q)
  let v (q : α) : ModeInfinity := (-t) • insertionInfinity (st.word q)
  let U (q : α) := ordinaryLocal (st.forwardWord t q)
  let P (q : α) := WZ (st.forwardVector t q) (x q)
  let Q (q : α) := WZ (st.forwardVector t q) (y q)
  have hδ : 0<2*|t| := mul_pos (by norm_num) (abs_pos.mpr ht)
  have hsep : ∀ᶠ q in l,2*|t|≤‖v q-(-v q)‖ := Eventually.of_forall fun q => by
    exact (unit_opposite_separation _ (norm_insertionInfinity _) t).ge
  have hPQ : Tendsto (fun q => ⟪SpinOperators.act Y (P q),Q q⟫_ℂ) l (𝓝 0) := by
    simpa only [P,Q,forwardVector_scale,v] using transverse_WZ_bounded
      (fun q => (r q)⁻¹) v x y (st.low_bounded _ BoundedPacket.vacuum)
      (st.low_bounded _ hη) hR (2*|t|) hδ hsep
  have hΩ : Tendsto (fun q => ‖U q (vacuum ModeInfinity)-P q‖) l (𝓝 0) := by
    simpa only [U,P,x,forwardWord,ordinaryLocal_cost,forwardVector,complex_neg_real_smul,
      ←map_sub,norm_WZ] using st.actual_low_norm hr (hR.eventually (eventually_ge_atTop 1)) _ BoundedPacket.vacuum
  have hη' : Tendsto (fun q => ‖U q (η q)-Q q‖) l (𝓝 0) := by
    simpa only [U,Q,y,forwardWord,ordinaryLocal_cost,forwardVector,complex_neg_real_smul,
      ←map_sub,norm_WZ] using st.actual_low_norm hr (hR.eventually (eventually_ge_atTop 1)) _ hη
  obtain ⟨C,hC,hηC⟩ := hη.norm_bounded
  have hPn (q : α) : ‖P q‖=1 := by
    simp only [P,x,norm_WZ,norm_smul,st.phase_norm,LinearIsometryEquiv.norm_map,norm_vacuum,mul_one]
  have herr : Tendsto (fun q => ⟪SpinOperators.act Y (U q (vacuum ModeInfinity)),U q (η q)⟫_ℂ-
      ⟪SpinOperators.act Y (P q),Q q⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _
      (by simpa only [zero_mul,add_zero] using (hΩ.mul_const C).add hη')
    filter_upwards [hηC] with q hq
    exact (inner_rootY_error_bound _ _ _ _).trans (by
      rw [LinearIsometryEquiv.norm_map,hPn,one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hq (norm_nonneg (U q (vacuum ModeInfinity)-P q))) le_rfl)
  have hh := herr.add hPQ
  simp only [sub_add_cancel,add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [modeFock_insertionY]
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (U q).inner_map_map ((U q).symm (SpinOperators.act Y (U q (vacuum ModeInfinity)))) (η q)

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 

def ApproxPacket (l : Filter α) (x : α → SpinSpace E) : Prop :=
  ∃y,BoundedPacket l y ∧ Tendsto (fun q => ‖x q-y q‖) l (𝓝 0)

theorem BoundedPacket.approx {x : α → SpinSpace E} (hx : BoundedPacket l x) : ApproxPacket l x :=
  ⟨x,hx,by simpa only [sub_self,norm_zero] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))⟩

namespace ApproxPacket

theorem close {x y : α → SpinSpace E} (hy : ApproxPacket l y)
    (he : Tendsto (fun q => ‖x q-y q‖) l (𝓝 0)) : ApproxPacket l x := by
  obtain ⟨z,hz,hyz⟩ := hy
  refine ⟨z,hz,?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using he.add hyz)
  exact Eventually.of_forall fun q => by simpa only [dist_eq_norm] using dist_triangle (x q) (y q) (z q)

theorem add {x y : α → SpinSpace E} (hx : ApproxPacket l x) (hy : ApproxPacket l y) :
    ApproxPacket l (fun q => x q+y q) := by
  obtain ⟨x',hx',hex⟩ := hx
  obtain ⟨y',hy',hey⟩ := hy
  refine ⟨fun q => x' q+y' q,hx'.add hy',?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using hex.add hey)
  exact Eventually.of_forall fun q => by
    have he : x q+y q-(x' q+y' q)=(x q-x' q)+(y q-y' q) := by abel
    rw [he]
    exact norm_add_le _ _

theorem smul {x : α → SpinSpace E} (hx : ApproxPacket l x) (c : ℂ) :
    ApproxPacket l (fun q => c • x q) := by
  obtain ⟨y,hy,he⟩ := hx
  refine ⟨fun q => c • y q,hy.smul (fun _ => c) ‖c‖ (norm_nonneg _) (Eventually.of_forall fun _ => le_rfl),?_⟩
  simpa only [←smul_sub,norm_smul,mul_zero] using he.const_mul ‖c‖

theorem neg {x : α → SpinSpace E} (hx : ApproxPacket l x) : ApproxPacket l (fun q => -x q) := by
  simpa only [neg_one_smul] using hx.smul (-1)

theorem sub {x y : α → SpinSpace E} (hx : ApproxPacket l x) (hy : ApproxPacket l y) :
    ApproxPacket l (fun q => x q-y q) := by simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem norm_bounded {x : α → SpinSpace E} (hx : ApproxPacket l x) :
    ∃C : ℝ,0≤C ∧ ∀ᶠ q in l,‖x q‖≤C := by
  obtain ⟨y,hy,he⟩ := hx
  obtain ⟨C,hC,hCy⟩ := hy.norm_bounded
  refine ⟨1+C,by linarith,?_⟩
  filter_upwards [hCy,he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with q hq heq
  exact (norm_le_norm_sub_add (x q) (y q)).trans (by linarith)

end ApproxPacket
end CoherentFock

end

end OAI
