import Mathlib
import OAI.Probability.ParisiFinite.SpinCoeAdd

namespace OAI

/-! Rotation Accuracy. -/

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
namespace CoherentFock
open RootSpin
variable {E α κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype κ]
  {l : Filter α}

 

theorem PacketExpansion.rotation_accuracy
    {r S : α → ℝ} {d : κ → α → E} {spin : κ → Fin 2}
    {u : α → SpinSpace E} (hu : PacketExpansion (l:=l) S r d spin u)
    (V : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E) (θ : ℝ)
    (hS : ∀ᶠ q in l,0≤S q) (hscale : ∀ᶠ q in l,0≤r q ∧ S q*r q=1)
    (hv : ∀i (x : α → SpinSpace E),BoundedPacket l x →
      Tendsto (fun q => ‖V q (spinW ((S q:ℂ) • d i q) (x q))-
        SpinOperators.act (R θ) (spinW ((S q:ℂ) • d i q) (x q))‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖V q (u q)-SpinOperators.act (R θ) (u q)‖) l (𝓝 0) := by
  obtain ⟨τ,hτ,_,he⟩ := hu
  let F := SpinOperators.act (R θ) (H:=Space E)
  have hF : ∀x,‖F x‖≤‖x‖ := fun x => (SpinOperators.norm_act (R_unitary _) x).le
  apply ForwardControl.scaled_difference_transfer V F hF S u
    (fun q => ∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q)) hS _ he
  exact ForwardControl.scaled_amplitude_finSum V F hF r S
    (fun q i => spinW ((S q:ℂ) • d i q) (τ i q)) hS hscale (fun i => hv i (τ i) (hτ i))

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance psRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance psRealSMul : SMul ℝ ModeInfinity := psRealModule.toDistribMulAction.toSMul
local instance psRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := psRealModule.toDistribMulAction.smul_zero }

 

theorem standard_selective_bounded {α κ : Type*} [Fintype κ] {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (x s ρ : α → SpinSpace ModeInfinity)
    (hx : BoundedPacket l x) (d : κ → α → ModeInfinity) (spin : κ → Fin 2)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (hψ : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=x q+s q+ρ q)
    (hs : Tendsto (fun q => ‖s q‖) l (𝓝 0)) (hρ : Tendsto (fun q => ‖ρ q‖) l (𝓝 0))
    (hZ : ∀i,Tendsto (fun q => -2*(⟪insertionInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀z,BoundedPacket l z →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (z q)-z q‖) l (𝓝 0)) ∧
      (∀z,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r d spin z →
        Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (z q)-
          SpinOperators.act (R θ) (z q)‖) l (𝓝 0)) := by
  obtain ⟨p,B,A,hB,hA,hx,hpb⟩ := hx
  have hψ' : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=spinCoe (p q)+s q+ρ q := by
    simpa only [hx] using hψ
  obtain ⟨K,a,ho,hsp⟩ := standard_selective_accuracy r w p s ρ B A hB hA v hv θ hr hp hpb hψ' hs hρ
  obtain ⟨_,hscale⟩ := reciprocal_scale_eventually r hr hp
  refine ⟨K,a,?_,?_⟩
  · intro z hz
    obtain ⟨p',B',A',hB',hA',hz,hpb'⟩ := hz
    simpa only [hz] using ho p' B' A' hB' hA' hpb'
  · intro z hz
    apply hz.rotation_accuracy (fun q => probeGain (r q) (w q) a K) θ
      (hscale.mono (fun _ h => h.2.1)) (hscale.mono (fun _ h => ⟨h.1,h.2.2⟩))
    intro i τ hτ
    obtain ⟨p',B',A',hB',hA',hτ,hpb'⟩ := hτ
    simpa only [hτ,actualPacket,Complex.coe_smul] using
      hsp i (d i) p' C B' A' hC hB' hA' (hd i) hpb' (hZ i) (hY i)

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
local instance addressRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance addressRealSMul : SMul ℝ ModeInfinity := addressRealModule.toDistribMulAction.toSMul
local instance addressRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := addressRealModule.toDistribMulAction.smul_zero }

section Naturality
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

 theorem spinMap_initial (T : E →ₗᵢ[ℂ] F) (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    spinMap (gammaEmbedding T) (initialMap γ δ β v e x)=
      initialMap γ δ β (T v) (T e) (spinMap (gammaEmbedding T) x) := by
  simp only [initialMap_apply_complex,spinMap_root,spinMap_cost,map_smul]

 theorem spinMap_special (T : E →ₗᵢ[ℂ] F) (γ β : ℝ) (v e : E) (x : SpinSpace E) :
    spinMap (gammaEmbedding T) (specialMap γ β v e x)=
      specialMap γ β (T v) (T e) (spinMap (gammaEmbedding T) x) := by
  simp only [specialMap_apply,←Complex.coe_smul,spinMap_root,spinMap_cost,map_smul,map_add]

 theorem specialPhase_map (T : E →ₗᵢ[ℂ] F) (γ : ℝ) (v e : E) :
    specialPhase γ (T v) (T e)=specialPhase γ v e := by
  unfold specialPhase
  simp only [←Complex.coe_smul,←map_smul,phase_map]

 theorem spinMap_address (T : E →ₗᵢ[ℂ] F) (γ δ : ℝ) (v e : E) :
    spinMap (gammaEmbedding T) (address γ δ v e)=address γ δ (T v) (T e) := by
  apply (initialMap γ δ (Real.pi/4) (T v) (T e)).injective
  rw [←spinMap_initial,address,LinearIsometryEquiv.apply_symm_apply]
  rw [spinMap_root,map_smul,spinMap_special,spinMap_vacuum]
  rw [address,LinearIsometryEquiv.apply_symm_apply,specialPhase_map]

end Naturality

 

def addressInfinity (b T : ℝ) : ModeInfinity := modeEmbed 4 (addressMode 2 b T)

@[simp] theorem norm_addressInfinity (b T : ℝ) : ‖addressInfinity b T‖=1 := by
  rw [addressInfinity,(modeEmbed 4).norm_map,norm_addressMode]

 theorem modeFock_embed_address (n : ℕ) (b T : ℝ) :
    modeFock (modeEmbed (n+2) (addressMode n b T))=
      address (gamma b T) (delta T) (modeEmbed (n+1) (actualV n b T))
        (modeEmbed (n+1) (initialDirection (n+1))) := by
  change unfoldTree (modeInWhole (modeEmbed (n+2) (addressMode n b T)))=_
  rw [modeInWhole_embed,unfoldTree_embed_succ]
  simp only [addressMode,actualAddress,topFockMap]
  apply spinMap_address

 theorem modeFock_addressInfinity (b T : ℝ) :
    modeFock (addressInfinity b T)=address (gamma b T) (delta T) (vInfinity b T) eInfinity := by
  rw [addressInfinity,modeFock_embed_address,embed_initialDirection,←vInfinity_embed]

 theorem addressInfinity_exact (b : ℝ) {T : ℝ} (hT : 1≤T) :
    (amplitude T : ℂ) • modeFock (addressInfinity b T)=
      (ordinaryLocal (wordInfinity b T)).symm
        (SpinOperators.act Z (specialPartInfinity b T (vacuum ModeInfinity))) := by
  rw [modeFock_addressInfinity,←sin_delta hT]
  have hm : ordinaryLocal (wordInfinity b T)=
      initialMap (gamma b T) (delta T) (Real.pi/4) (vInfinity b T) eInfinity :=
    LinearIsometryEquiv.ext (ordinaryLocal_initialization b T)
  rw [hm,specialPartInfinity_apply]
  exact address_exact_normalization _ _ _ _

 theorem addressInfinity_escapes (b : ℝ) (hb : 0<b) (x : ℝ → SpinSpace ModeInfinity)
    (hx : BoundedPacket atTop x) :
    Tendsto (fun T => ⟪x T,modeFock (addressInfinity b T)⟫_ℂ) atTop (𝓝 0) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  have hl : Tendsto (fun T => ⟪spinCoe (p T),leading (gamma b T) (vInfinity b T)⟫_ℂ)
      atTop (𝓝 0) :=
    tendsto_inner_spinCoe_rootZ_uniform _ p
      (tendsto_norm_scaled_unit (gamma b) (vInfinity b) (tendsto_gamma b hb)
        (norm_vInfinity b)) B A hB hbound
  have hs : Tendsto (fun T => |Real.sin (delta T)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sin_zero,abs_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp tendsto_delta).abs
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [mul_zero,norm_zero,add_zero] using (hs.const_mul A).add hl.norm)
  filter_upwards [hbound] with T hT
  rw [modeFock_addressInfinity,hp]
  have hh := norm_inner_address_bound (gamma b T) (delta T) (vInfinity b T) eInfinity (spinCoe (p T))
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_right ((norm_spinCoe_le_mass _).trans hT.2) (abs_nonneg _))
    (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)))

 theorem highInfinity_lift (γ : ℝ) : highInfinity γ=modeEmbed 4 (highDirection 3 γ) := by
  have h := modeEmbed_step 3 (highDirection 2 γ)
  rw [show modeStep 3 (highDirection 2 γ)=highDirection 3 γ from highDirection_empty 2 γ] at h
  exact h.symm

 theorem high_addressInfinity_orthogonal (b : ℝ) (hb : 0<b) :
    Tendsto (fun T => ⟪highInfinity (gamma b T),addressInfinity b T⟫_ℂ) atTop (𝓝 0) := by
  simp only [highInfinity_lift,addressInfinity,(modeEmbed 4).inner_map_map]
  exact tendsto_high_address_inner 2 b hb

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin

 

structure PacketStage {α κ : Type*} [Fintype κ] (l : Filter α)
    (r S : α → ℝ) (d : κ → α → ModeInfinity) (spin : κ → Fin 2) where
  word : α → List Gate
  ordinary : α → SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity
  special : α → SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity
  split : ∀q x,ordinaryLocal (word q) x=ordinary q x+special q x
  special_norm : ∀ᶠ q in l,∀x,‖special q x‖=r q*‖x‖
  low : PacketUnitaryFamily (E:=ModeInfinity) l
  phase : α → ℂ
  phase_norm : ∀q,‖phase q‖=1
  ordinary_low : ∀x,BoundedPacket l x →
    Tendsto (fun q => S q*‖ordinary q (x q)-phase q • low.op q (x q)‖) l (𝓝 0)
  special_packets : ∀x,BoundedPacket l x →
    PacketExpansion (l:=l) S r d spin (fun q => special q (x q))

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

theorem special_vacuum_zero (st : PacketStage l r S d spin) (hr : Tendsto r l (𝓝 0)) :
    Tendsto (fun q => ‖st.special q (vacuum ModeInfinity)‖) l (𝓝 0) := by
  apply hr.congr'
  filter_upwards [st.special_norm] with q hq
  rw [hq,norm_vacuum,mul_one]

 

theorem low_bounded (st : PacketStage l r S d spin) (x : α → SpinSpace ModeInfinity)
    (hx : BoundedPacket l x) :
    BoundedPacket l (fun q => st.phase q • st.low.op q (x q)) :=
  (st.low.forward x hx).smul st.phase 1 (by norm_num)
    (Eventually.of_forall fun q => (st.phase_norm q).le)

 

theorem insertion_bound (st : PacketStage l r S d spin)
    (hscale : ∀ᶠ q in l,0≤r q ∧ 0≤S q ∧ S q*r q=1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    ∀ᶠ q in l,S q*‖(ordinaryLocal (st.word q)).symm
      (SpinOperators.act P (ordinaryLocal (st.word q) (vacuum ModeInfinity)))-
      (st.low.op q).symm (SpinOperators.act P (st.low.op q (vacuum ModeInfinity)))‖≤4 :=
  low_insertion_scaled_bound (fun q => ordinaryLocal (st.word q)) st.low st.ordinary st.special
    st.phase r S P hP hscale (Eventually.of_forall st.split)
    (st.special_norm.mono fun _ hq x => (hq x).le) st.ordinary_low

 

def cost (st : PacketStage l r S d spin) (c : ℝ) : PacketStage l r S d spin where
  word q := .cost c::st.word q
  ordinary q := (WZ (-(c:ℂ) • insertionInfinity (st.word q))).comp (st.ordinary q)
  special q := (WZ (-(c:ℂ) • insertionInfinity (st.word q))).comp (st.special q)
  split q x := by simp only [ordinaryLocal_cost,st.split,map_add,ContinuousLinearMap.comp_apply]
  special_norm := by
    filter_upwards [st.special_norm] with q hq x
    simpa only [ContinuousLinearMap.comp_apply,norm_WZ] using hq x
  low := st.low.trans (PacketUnitaryFamily.pulse
    (fun q => -(c:ℂ) • insertionInfinity (st.word q)) |c| (abs_nonneg _)
    (Eventually.of_forall fun q => by simp only [norm_smul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,norm_insertionInfinity,mul_one,le_refl]))
  phase := st.phase
  phase_norm := st.phase_norm
  ordinary_low x hx := by
    have h := st.ordinary_low x hx
    simpa only [PacketUnitaryFamily.trans,PacketUnitaryFamily.pulse,LinearIsometryEquiv.trans_apply,
      costEquiv_apply,ContinuousLinearMap.comp_apply,←map_smul,←map_sub,norm_WZ] using h
  special_packets x hx := (st.special_packets x hx).bounded_cost
    (fun q => -(c:ℂ) • insertionInfinity (st.word q)) |c| (abs_nonneg _)
    (Eventually.of_forall fun q => by simp only [norm_smul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,norm_insertionInfinity,mul_one,le_refl])

end PacketStage
end PointedTree

namespace SeedInitialization
open CoherentFock RootSpin PointedTree

 

def initialStage (b : ℝ) :
    PacketStage (atTop : Filter ℝ) amplitude id
      (fun i : Fin 2×Fin 2 => fun _ => initialCenter b i.1) Prod.snd where
  word := wordInfinity b
  ordinary := ordinaryPartInfinity b
  special := specialPartInfinity b
  split := exact_splitInfinity b
  special_norm := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT x
    exact norm_specialPartInfinity b hT x
  low := lowInfinity b
  phase := phaseInfinity b
  phase_norm := norm_phaseInfinity b
  ordinary_low := lowInfinity_accuracy b
  special_packets x hx := by
    refine ⟨fun i T => initialTail b T i.1 i.2 (x T),
      fun i => initialTail_bounded b x hx i.1 i.2,fun i T => initialTail_sector b T i.1 i.2 (x T),?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have h := initial_special_packets b hT (x T)
    simp only [id_eq,Fintype.sum_prod_type,←Finset.smul_sum,←h,sub_self,norm_zero,mul_zero]

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
open RootSpin
variable {E α κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype κ]
  {l : Filter α}

theorem projectSpin_rootZ (i : Fin 2) (x : SpinSpace E) :
    projectSpin i (SpinOperators.act Z x)=SpinOperators.act Z (projectSpin i x) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [projectSpin_apply,SpinOperators.act_apply,Z,Fin.sum_univ_two]

theorem PacketExpansion.rootZ {r S : α → ℝ} {d : κ → α → E} {spin : κ → Fin 2}
    {u : α → SpinSpace E} (hu : PacketExpansion (l:=l) S r d spin u) :
    PacketExpansion (l:=l) S r d spin (fun q => SpinOperators.act Z (u q)) := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  refine ⟨fun i q => SpinOperators.act Z (τ i q),fun i => (hτ i).root Z,?_,?_⟩
  · intro i q
    rw [projectSpin_rootZ,hspin]
  · have hsum (q : α) : SpinOperators.act Z (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))=
        ∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (SpinOperators.act Z (τ i q)) := by
      simp only [map_sum,map_smul,spinW_root]
    simpa only [←hsum,←map_sub,SpinOperators.norm_act Z_unitary] using he

 

theorem compensated_error (θ : ℝ) (x y : SpinSpace E) :
    ‖SpinOperators.act (R θ) x-y‖=‖x-SpinOperators.act (R (-θ)) y‖ := by
  have hcancel : SpinOperators.act (R θ) (SpinOperators.act (R (-θ)) y)=y := by
    rw [←ContinuousLinearMap.comp_apply,←SpinOperators.act_mul,R_add,add_neg_cancel,R_zero,SpinOperators.act_one]
    rfl
  conv_lhs => rw [←hcancel]
  rw [←map_sub,SpinOperators.norm_act (R_unitary _)]

end CoherentFock

namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

omit [InnerProductSpace ℂ H] in
theorem scaled_triangle (S : α → ℝ) (x y z : α → H) (hS : ∀ᶠ q in l,0≤S q)
    (hxy : Tendsto (fun q => S q*‖x q-y q‖) l (𝓝 0))
    (hyz : Tendsto (fun q => S q*‖y q-z q‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖x q-z q‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [add_zero] using hxy.add hyz)
  · filter_upwards [hS] with q hq
    exact mul_nonneg hq (norm_nonneg _)
  · filter_upwards [hS] with q hq
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub (x q) (y q) (z q)) hq

 

theorem preserve_transport_bound (V : H ≃ₗᵢ[ℂ] H) (Z : H →L[ℂ] H)
    (hZ : ∀x,‖Z x‖≤‖x‖) (s : H) :
    ‖V.symm (Z (V s))-Z s‖≤‖V s-s‖+‖V (Z s)-Z s‖ := by
  rw [←V.norm_map, map_sub, V.apply_symm_apply]
  have h := norm_sub_le_norm_sub_add_norm_sub (Z (V s)) (Z s) (V (Z s))
  rw [←map_sub,norm_sub_rev (Z s)] at h
  exact h.trans (add_le_add (hZ _) le_rfl)

end ForwardControl

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin

 
def compensatedGain (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (K : ℕ) (θ : ℝ) :
    SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  (probeGain r w a K).trans (SpinOperators.actEquiv (R θ) (R_unitary θ))

@[simp] theorem compensatedGain_apply (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (θ : ℝ) (x : SpinSpace ModeInfinity) :
    compensatedGain r w a K θ x=SpinOperators.act (R θ) (probeGain r w a K x) := rfl

@[simp] theorem compensatedGain_local (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (θ : ℝ) (x : SpinSpace ModeInfinity) :
    compensatedGain r w a K θ (ordinaryLocal w x)=ordinaryLocal (.mixer θ::probePrefix r w a K) x := by
  simp only [compensatedGain_apply,probeGain_on_local,ordinaryLocal_mixer]

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 

def compensated (st : PacketStage l r S d spin) (θ : ℝ) (a : ℕ → ShortPulse) (K : ℕ)
    (hS : ∀ᶠ q in l,0≤S q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (x q)-x q‖) l (𝓝 0))
    (hs : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (st.special q (x q))-
        SpinOperators.act (R (-θ)) (st.special q (x q))‖) l (𝓝 0)) :
    PacketStage l r S d spin where
  word q := .mixer θ::probePrefix (r q) (st.word q) a K
  ordinary q := (compensatedGain (r q) (st.word q) a K θ).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.ordinary q)
  special q := (compensatedGain (r q) (st.word q) a K θ).toContinuousLinearEquiv.toContinuousLinearMap.comp (st.special q)
  split q x := by
    rw [←compensatedGain_local,st.split,map_add]
    rfl
  special_norm := by
    filter_upwards [st.special_norm] with q hq x
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.norm_map] using hq x
  low := st.low.trans (PacketUnitaryFamily.root (R θ) (R_unitary θ))
  phase := st.phase
  phase_norm := st.phase_norm
  ordinary_low x hx := by
    have he := st.ordinary_low x hx
    have hp := ho (fun q => st.phase q • st.low.op q (x q)) (st.low_bounded x hx)
    have ht := ForwardControl.scaled_identity_transfer
      (fun q => probeGain (r q) (st.word q) a K) S
      (fun q => st.ordinary q (x q)) (fun q => st.phase q • st.low.op q (x q)) hS hp he
    have hall := ForwardControl.scaled_triangle S
      (fun q => probeGain (r q) (st.word q) a K (st.ordinary q (x q)))
      (fun q => st.ordinary q (x q)) (fun q => st.phase q • st.low.op q (x q)) hS ht he
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,compensatedGain_apply,PacketUnitaryFamily.trans,PacketUnitaryFamily.root,
      LinearIsometryEquiv.trans_apply,SpinOperators.actEquiv_apply,←map_smul,←map_sub,
      SpinOperators.norm_act (R_unitary _)] using hall
  special_packets x hx := by
    apply (st.special_packets x hx).close hS
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,compensatedGain_apply,compensated_error] using hs x hx

 

theorem exists_compensated {r : α → ℝ}
    (st : PacketStage l r (fun q => (r q)⁻¹) d spin) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (C : ℝ) (hC : 0≤C) (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0)
    (hZ : ∀i,Tendsto (fun q => -2*(⟪insertionInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (st.word q),d i q⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (st' : PacketStage l r (fun q => (r q)⁻¹) d spin),
      (∀q,st'.word q=.mixer θ::probePrefix (r q) (st.word q) a K) ∧
      (∀q x,st'.low.op q x=SpinOperators.act (R θ) (st.low.op q x)) ∧
      (∀x,BoundedPacket l x → Tendsto (fun q => (r q)⁻¹*‖
        st'.special q (x q)-st.special q (x q)‖) l (𝓝 0)) := by
  let o (q : α) := st.ordinary q (vacuum ModeInfinity)
  let y (q : α) := st.phase q • st.low.op q (vacuum ModeInfinity)
  let s (q : α) := st.special q (vacuum ModeInfinity)
  obtain ⟨hS,hscale⟩ := reciprocal_scale_eventually r hr hp
  have hS0 := hscale.mono (fun _ h => h.2.1)
  have he : Tendsto (fun q => ‖o q-y q‖) l (𝓝 0) :=
    PacketGeometry.tendsto_of_scaled (fun q => (r q)⁻¹) _ hS
      (Eventually.of_forall fun _ => norm_nonneg _) (st.ordinary_low _ BoundedPacket.vacuum)
  have hψ : ∀ᶠ q in l,ordinaryLocal (st.word q) (vacuum ModeInfinity)=y q+s q+(o q-y q) := by
    exact Eventually.of_forall fun q => by dsimp only [o,s]; rw [st.split]; abel
  obtain ⟨K,a,ho,hsp⟩ := standard_selective_bounded r st.word y s (fun q => o q-y q)
    (st.low_bounded _ BoundedPacket.vacuum) d spin C hC hd v hv (-θ) hr hp hψ
    (st.special_vacuum_zero hr) he hZ hY
  have hs := fun x hx => hsp _ (st.special_packets x hx)
  let st' := st.compensated θ a K hS0 ho hs
  refine ⟨K,a,st',fun _ => rfl,fun _ _ => rfl,?_⟩
  intro x hx
  change Tendsto (fun q => (r q)⁻¹*‖compensatedGain (r q) (st.word q) a K θ
    (st.special q (x q))-st.special q (x q)‖) l (𝓝 0)
  simpa only [compensatedGain_apply,compensated_error] using hs x hx

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

 

theorem scaled_preserve_transport (U V : α → H ≃ₗᵢ[ℂ] H) (Z : H →L[ℂ] H)
    (hZ : ∀x,‖Z x‖≤‖x‖) (s w : α → H) (S : α → ℝ)
    (hS : ∀ᶠ q in l,0≤S q)
    (h1 : Tendsto (fun q => S q*‖V q (s q)-s q‖) l (𝓝 0))
    (h2 : Tendsto (fun q => S q*‖V q (Z (s q))-Z (s q)‖) l (𝓝 0))
    (ht : Tendsto (fun q => ‖(S q:ℂ) • (U q).symm (Z (s q))-w q‖) l (𝓝 0)) :
    Tendsto (fun q => ‖(S q:ℂ) • (U q).symm ((V q).symm (Z (V q (s q))))-w q‖) l (𝓝 0) := by
  have he : Tendsto (fun q => S q*‖(V q).symm (Z (V q (s q)))-Z (s q)‖) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [add_zero] using h1.add h2)
    · filter_upwards [hS] with q hq
      exact mul_nonneg hq (norm_nonneg _)
    · filter_upwards [hS] with q hq
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (preserve_transport_bound (V q) Z hZ (s q)) hq
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using he.add ht)
  filter_upwards [hS] with q hq
  have heq : (S q:ℂ) • (U q).symm ((V q).symm (Z (V q (s q))))-w q=
      (S q:ℂ) • (U q).symm ((V q).symm (Z (V q (s q)))-Z (s q))+
        ((S q:ℂ) • (U q).symm (Z (s q))-w q) := by
    simp only [map_sub,smul_sub]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,(U q).symm.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]

end ForwardControl

namespace CoherentFock
open RootSpin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem WZ_rootZ_apply (d : E) (x : SpinSpace E) :
    WZ d (SpinOperators.act Z x)=SpinOperators.act Z (WZ d x) := by
  exact congrArg (fun F : SpinSpace E →L[ℂ] SpinSpace E => F x) (WZ_rootZ d)

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin

theorem local_symm_after_gain (w u : List Gate)
    (V : SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity)
    (h : ∀x,V (ordinaryLocal w x)=ordinaryLocal u x) (x : SpinSpace ModeInfinity) :
    (ordinaryLocal u).symm x=(ordinaryLocal w).symm (V.symm x) := by
  apply (ordinaryLocal u).injective
  rw [LinearIsometryEquiv.apply_symm_apply,←h,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

 

theorem cost_transport_exact (w : List Gate) (c : ℝ) (x : SpinSpace ModeInfinity) :
    (ordinaryLocal (.cost c::w)).symm
      (SpinOperators.act Z (WZ (-(c:ℂ) • insertionInfinity w) x))=
      (ordinaryLocal w).symm (SpinOperators.act Z x) := by
  apply (ordinaryLocal (.cost c::w)).injective
  rw [LinearIsometryEquiv.apply_symm_apply,ordinaryLocal_cost,LinearIsometryEquiv.apply_symm_apply,
    WZ_rootZ_apply]

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

 
def Transported (st : PacketStage l r S d spin) (a : α → SpinSpace ModeInfinity) : Prop :=
  Tendsto (fun q => ‖(S q:ℂ) • (ordinaryLocal (st.word q)).symm
    (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))-a q‖) l (𝓝 0)

theorem Transported.cost {st : PacketStage l r S d spin} {a : α → SpinSpace ModeInfinity}
    (ht : st.Transported a) (c : ℝ) : (st.cost c).Transported a := by
  unfold Transported at *
  simpa only [PacketStage.cost,ContinuousLinearMap.comp_apply,cost_transport_exact] using ht

theorem Transported.compensated {st : PacketStage l r S d spin} {address : α → SpinSpace ModeInfinity}
    (ht : st.Transported address) (θ : ℝ) (a : ℕ → ShortPulse) (K : ℕ)
    (hS : ∀ᶠ q in l,0≤S q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (x q)-x q‖) l (𝓝 0))
    (hs : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K (st.special q (x q))-
        SpinOperators.act (R (-θ)) (st.special q (x q))‖) l (𝓝 0))
    (hz : Tendsto (fun q => S q*‖probeGain (r q) (st.word q) a K
      (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))-
        SpinOperators.act (R (-θ)) (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))‖) l (𝓝 0)) :
    (st.compensated θ a K hS ho hs).Transported address := by
  let V (q : α) := compensatedGain (r q) (st.word q) a K θ
  have h1 : Tendsto (fun q => S q*‖V q (st.special q (vacuum ModeInfinity))-
      st.special q (vacuum ModeInfinity)‖) l (𝓝 0) := by
    simpa only [V,compensatedGain_apply,compensated_error] using hs _ BoundedPacket.vacuum
  have h2 : Tendsto (fun q => S q*‖V q (SpinOperators.act Z (st.special q (vacuum ModeInfinity)))-
      SpinOperators.act Z (st.special q (vacuum ModeInfinity))‖) l (𝓝 0) := by
    simpa only [V,compensatedGain_apply,compensated_error] using hz
  have h := ForwardControl.scaled_preserve_transport (fun q => ordinaryLocal (st.word q)) V
    (SpinOperators.act Z) (fun x => (SpinOperators.norm_act Z_unitary x).le)
    (fun q => st.special q (vacuum ModeInfinity)) address S hS h1 h2 ht
  unfold Transported
  have he (q : α) (x : SpinSpace ModeInfinity) :
      (ordinaryLocal (.mixer θ::probePrefix (r q) (st.word q) a K)).symm x=
        (ordinaryLocal (st.word q)).symm ((V q).symm x) :=
    local_symm_after_gain _ _ (V q) (compensatedGain_local _ _ _ _ _) x
  change Tendsto (fun q => ‖(S q:ℂ) •
    (ordinaryLocal (.mixer θ::probePrefix (r q) (st.word q) a K)).symm
      (SpinOperators.act Z (V q (st.special q (vacuum ModeInfinity))))-address q‖) l (𝓝 0)
  simpa only [he] using h

end PacketStage
end PointedTree

namespace SeedInitialization
open CoherentFock RootSpin PointedTree

theorem initialStage_transported (b : ℝ) :
    (initialStage b).Transported (fun T => modeFock (addressInfinity b T)) := by
  unfold PacketStage.Transported
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  change (0:ℝ)=‖(T:ℂ) • (ordinaryLocal (wordInfinity b T)).symm
    (SpinOperators.act Z (specialPartInfinity b T (vacuum ModeInfinity)))-modeFock (addressInfinity b T)‖
  rw [←addressInfinity_exact b hT,smul_smul]
  have hT0 : T≠0 := by linarith
  simp only [amplitude,Complex.ofReal_inv,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hT0),one_smul,
    sub_self,norm_zero]

end SeedInitialization

end

end OAI
