import Mathlib
import OAI.Probability.ParisiFinite.ActualCenterPhase

namespace OAI

/-! Spin W Zero Apply. -/

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
local instance selectionRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance selectionRealSMul : SMul ℝ ModeInfinity := selectionRealModule.toDistribMulAction.toSMul
local instance selectionRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := selectionRealModule.toDistribMulAction.smul_zero }

theorem spinW_zero_apply (x : SpinSpace ModeInfinity) : spinW 0 x=x := by
  ext i
  simp only [spinW_apply,W_zero,ContinuousLinearMap.id_apply]

 

theorem reciprocal_scale_eventually {α : Type*} {l : Filter α} (r : α → ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ t in l,0<r t) :
    (∀ᶠ t in l,1≤(r t)⁻¹) ∧
      (∀ᶠ t in l,0≤r t ∧ 0≤(r t)⁻¹ ∧ (r t)⁻¹*r t=1) := by
  constructor
  · filter_upwards [hp,hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht hu
    exact (le_inv_comm₀ (by norm_num) ht).mpr (by simpa using hu.le)
  · filter_upwards [hp] with t ht
    exact ⟨ht.le,inv_nonneg.mpr ht.le,inv_mul_cancel₀ ht.ne'⟩

 

theorem standard_selective_accuracy {α κ : Type*} [Fintype κ] {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (x : α → PreSpin ModeInfinity)
    (s ρ : α → SpinSpace ModeInfinity) (B A : ℝ) (hB : 0≤B) (hA : 0≤A)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ t in l,0<r t)
    (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=spinCoe (x t)+s t+ρ t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀ (z : α → PreSpin ModeInfinity) (B' A' : ℝ),0≤B' → 0≤A' →
        (∀ᶠ t in l,SpinRadiusLE (z t) B' ∧ spinMass (z t)≤A') →
        Tendsto (fun t => (r t)⁻¹*‖probeGain (r t) (w t) a K (spinCoe (z t))-spinCoe (z t)‖) l (𝓝 0)) ∧
      (∀ (i : κ) (e : α → ModeInfinity) (z : α → PreSpin ModeInfinity) (C B' A' : ℝ),
        0≤C → 0≤B' → 0≤A' → (∀ᶠ t in l,‖e t‖≤C) →
        (∀ᶠ t in l,SpinRadiusLE (z t) B' ∧ spinMass (z t)≤A') →
        Tendsto (fun t => -2*(⟪insertionInfinity (w t),e t⟫_ℂ).im) l (𝓝 (v i).1) →
        Tendsto (fun t => -2*(⟪insertionYInfinity (w t),e t⟫_ℂ).im) l (𝓝 (v i).2) →
        Tendsto (fun t => ‖probeGain (r t) (w t) a K (actualPacket ((r t)⁻¹) (e t) (z t))-
          SpinOperators.act (R θ) (actualPacket ((r t)⁻¹) (e t) (z t))‖) l (𝓝 0)) := by
  obtain ⟨hS,hscale⟩ := reciprocal_scale_eventually r hr hp
  have hvac : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      (∑ _ : Unit,actualPacket ((r t)⁻¹) 0 (x t))+s t+ρ t := by
    simpa only [actualPacket,smul_zero,spinW_zero_apply,Fintype.sum_unique] using hψ
  obtain ⟨K,a,T,hT,ha,h⟩ := selective_packet_accuracy r (fun t => (r t)⁻¹) w
    (fun (_ : Unit) _ => 0) (fun _ => x) s ρ B A hB hA v hv θ hr hS hscale
    (fun _ => hx) hvac hs hρ
  have hzphase : ∀j<K,Tendsto (fun t => (r t)⁻¹*|-2*(⟪actualDisplacement (r t) (w t) a j,
      (r t)⁻¹ • (0:ModeInfinity)⟫_ℂ).im|) l (𝓝 0) := by
    intro j hj
    simpa only [standard_center_phase] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  obtain ⟨ho,hs⟩ := h (fun _ => hzphase)
  refine ⟨K,a,?_,?_⟩
  · intro z B' A' hB' hA' hz
    simpa only [actualPacket,smul_zero,spinW_zero_apply] using
      ho (fun _ => 0) z B' A' hB' hA' hz hzphase
  · intro i e z C B' A' hC hB' hA' he hz hZ hY
    have hh := hs i e z C B' A' hC hB' hA' he hz hZ hY
    apply hh.congr'
    exact Eventually.of_forall (fun t => by
      exact centered_rotation_error ((r t)⁻¹ • e t) (R θ)
        (probeGain (r t) (w t) a K).toLinearEquiv.toLinearMap (spinCoe (z t)))

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance selectHugeRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance selectHugeRealSMul : SMul ℝ ModeInfinity := selectHugeRealModule.toDistribMulAction.toSMul

 

theorem huge_selective_accuracy {α κ : Type*} [Fintype κ] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (t : ℝ) (ht : t≠0)
    (d : κ → α → ModeInfinity) (xp xm : α → PreSpin ModeInfinity)
    (xs : κ → α → PreSpin ModeInfinity) (ρ : α → SpinSpace ModeInfinity)
    (B A : ℝ) (hB : 0≤B) (hA : 0≤A) (c y : κ → ℝ) (hc : ∀i,c i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hpos : ∀ᶠ q in l,0≤r q)
    (hS : Tendsto S l atTop) (hscale : ∀ᶠ q in l,S q*r q=1)
    (hxp : ∀ᶠ q in l,SpinRadiusLE (xp q) B ∧ spinMass (xp q)≤A)
    (hxm : ∀ᶠ q in l,SpinRadiusLE (xm q) B ∧ spinMass (xm q)≤A)
    (hxs : ∀i,∀ᶠ q in l,SpinRadiusLE (xs i q) B ∧ spinMass (xs i q)≤A)
    (hvis : ∀i,Tendsto (fun q => (⟪insertionInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (c i)))
    (hψ : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=
      actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q)+
      actualPacket (S q) (t • insertionInfinity (w q)) (xm q)+
      (∑i,actualPacket (S q) (d i q) (xs i q))+ρ q)
    (hop : ∀ᶠ q in l,SpinOperators.act Z
      (actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))=
      actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))
    (hom : ∀ᶠ q in l,SpinOperators.act Z
      (actualPacket (S q) (t • insertionInfinity (w q)) (xm q))=
      -actualPacket (S q) (t • insertionInfinity (w q)) (xm q))
    (hρ : Tendsto (fun q => S q*‖ρ q‖) l (𝓝 0))
    (hs : Tendsto (fun q => S q*‖∑i,actualPacket (S q) (d i q) (xs i q)‖^2) l (𝓝 0)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      (∀ (b : ℝ) (z : α → PreSpin ModeInfinity) (B' A' : ℝ),0≤B' → 0≤A' →
        (∀ᶠ q in l,SpinRadiusLE (z q) B' ∧ spinMass (z q)≤A') →
        Tendsto (fun q => S q*‖probeGain (r q) (w q) a K
          (actualPacket (S q) (b • insertionInfinity (w q)) (z q))-
          actualPacket (S q) (b • insertionInfinity (w q)) (z q)‖) l (𝓝 0)) ∧
      (∀ (i : κ) (e : α → ModeInfinity) (z : α → PreSpin ModeInfinity) (C B' A' : ℝ),
        0≤C → 0≤B' → 0≤A' → (∀ᶠ q in l,‖e q‖≤C) →
        (∀ᶠ q in l,SpinRadiusLE (z q) B' ∧ spinMass (z q)≤A') →
        Tendsto (fun q => -2*(⟪insertionInfinity (w q),e q⟫_ℂ).im) l (𝓝 (-2*c i)) →
        Tendsto (fun q => -2*(⟪insertionYInfinity (w q),e q⟫_ℂ).im) l (𝓝 (y i)) →
        Tendsto (fun q => ‖probeGain (r q) (w q) a K (actualPacket (S q) (e q) (z q))-
          SpinOperators.act (R θ) (actualPacket (S q) (e q) (z q))‖) l (𝓝 0)) := by
  have hS1 : ∀ᶠ q in l,1≤S q := hS.eventually (eventually_ge_atTop 1)
  have hscale' : ∀ᶠ q in l,0≤r q ∧ 0≤S q ∧ S q*r q=1 := by
    filter_upwards [hpos,hS1,hscale] with q hq hsq he
    exact ⟨hq,by linarith,he⟩
  have hρ0 := PacketGeometry.tendsto_of_scaled S (fun q => ‖ρ q‖) hS1
    (Eventually.of_forall (fun _ => norm_nonneg _)) hρ
  have hs2 := PacketGeometry.tendsto_of_scaled S
    (fun q => ‖∑i,actualPacket (S q) (d i q) (xs i q)‖^2) hS1
    (Eventually.of_forall (fun _ => sq_nonneg _)) hs
  have hs0 : Tendsto (fun q => ‖∑i,actualPacket (S q) (d i q) (xs i q)‖) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs2
  let ds : Fin 2 → α → ModeInfinity := fun i q => if i=0 then (-t) • insertionInfinity (w q) else t • insertionInfinity (w q)
  let xo : Fin 2 → α → PreSpin ModeInfinity := fun i => if i=0 then xp else xm
  have hxo : ∀i,∀ᶠ q in l,SpinRadiusLE (xo i q) B ∧ spinMass (xo i q)≤A := by
    intro i
    fin_cases i
    · simpa [xo] using hxp
    · simpa [xo] using hxm
  have hψ' : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=
      (∑i,actualPacket (S q) (ds i q) (xo i q))+
      (∑i,actualPacket (S q) (d i q) (xs i q))+ρ q := by
    simpa [Fin.sum_univ_two,ds,xo] using hψ
  have hv : ∀i,(-2*c i,y i)≠(0:ℝ×ℝ) := by
    intro i hi
    have hi' := congrArg Prod.fst hi
    change -2*c i=0 at hi'
    exact hc i ((mul_eq_zero.mp hi').resolve_left (by norm_num))
  obtain ⟨K,a,T,hT,ha,hacc⟩ := selective_packet_accuracy r S w ds xo
    (fun q => ∑i,actualPacket (S q) (d i q) (xs i q)) ρ B A hB hA
    (fun i => (-2*c i,y i)) hv θ hr hS1 hscale' hxo hψ' hs0 hρ0
  have hr1 : ∀ᶠ q in l,|r q|≤1 := by
    filter_upwards [hpos,hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with q hq hu
    simpa only [abs_of_nonneg hq] using hu.le
  have hph := huge_ordinary_scaled_phases r S w a K t ht d c xp xm xs ρ hS B A T hA hT ha hr1
    (hscale.mono (fun _ h => by rwa [mul_comm])) hxp hxm hxs hc hvis hψ hop hom hρ hs
  have hph' : ∀i,∀j<K,Tendsto (fun q => S q*|-2*(⟪actualDisplacement (r q) (w q) a j,S q • ds i q⟫_ℂ).im|) l (𝓝 0) := by
    intro i j hj
    fin_cases i
    · simpa [ds] using hph j hj (-t)
    · simpa [ds] using hph j hj t
  obtain ⟨ho,hsp⟩ := hacc hph'
  refine ⟨K,a,?_,?_⟩
  · intro b z B' A' hB' hA' hz
    exact ho (fun q => b • insertionInfinity (w q)) z B' A' hB' hA' hz (fun j hj => hph j hj b)
  · intro i e z C B' A' hC hB' hA' he hz hZ hY
    have h := hsp i e z C B' A' hC hB' hA' he hz hZ hY
    apply h.congr'
    exact Eventually.of_forall (fun q => centered_rotation_error (S q • e q) (R θ)
      (probeGain (r q) (w q) a K).toLinearEquiv.toLinearMap (spinCoe (z q)))

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

 

theorem scaled_difference_transfer (V : α → H ≃ₗᵢ[ℂ] H) (F : H →L[ℂ] H)
    (hF : ∀x,‖F x‖≤‖x‖) (S : α → ℝ) (x y : α → H)
    (hS : ∀ᶠ t in l,0≤S t)
    (hy : Tendsto (fun t => S t*‖V t (y t)-F (y t)‖) l (𝓝 0))
    (hxy : Tendsto (fun t => S t*‖x t-y t‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t (x t)-F (x t)‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [zero_mul,add_zero] using hy.add (hxy.mul_const 2))
  · filter_upwards [hS] with t ht
    exact mul_nonneg ht (norm_nonneg _)
  · filter_upwards [hS] with t ht
    have he : V t (x t)-F (x t)=(V t (y t)-F (y t))+V t (x t-y t)-F (x t-y t) := by
      simp only [map_sub]
      abel
    have hn : ‖V t (x t)-F (x t)‖≤‖V t (y t)-F (y t)‖+2*‖x t-y t‖ := by
      rw [he]
      have h := (norm_sub_le (V t (y t)-F (y t)+V t (x t-y t)) (F (x t-y t))).trans
        (add_le_add (norm_add_le (V t (y t)-F (y t)) (V t (x t-y t))) (hF _))
      rw [(V t).norm_map] at h
      linarith
    nlinarith

 
theorem scaled_map_difference (F : H →L[ℂ] H) (hF : ∀x,‖F x‖≤‖x‖)
    (S : α → ℝ) (x y : α → H) (hS : ∀ᶠ t in l,0≤S t)
    (hxy : Tendsto (fun t => S t*‖x t-y t‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖F (x t)-F (y t)‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ hxy
  · filter_upwards [hS] with t ht
    exact mul_nonneg ht (norm_nonneg _)
  · filter_upwards [hS] with t ht
    rw [←map_sub]
    exact mul_le_mul_of_nonneg_left (hF _) ht

 

theorem scaled_amplitude_finSum {ι : Type*} [Fintype ι]
    (V : α → H ≃ₗᵢ[ℂ] H) (F : H →L[ℂ] H) (hF : ∀x,‖F x‖≤‖x‖)
    (r S : α → ℝ) (x : α → ι → H)
    (hS : ∀ᶠ t in l,0≤S t) (hscale : ∀ᶠ t in l,0≤r t ∧ S t*r t=1)
    (hx : ∀i,Tendsto (fun t => ‖V t (x t i)-F (x t i)‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t (∑i,(r t:ℂ) • x t i)-F (∑i,(r t:ℂ) • x t i)‖) l (𝓝 0) := by
  have h := scaled_difference_finSum_tendsto V F hF S (fun t i => (r t:ℂ) • x t i)
    (fun _ => 0) hS (fun i => scaled_amplitude_error V F r S (fun t => x t i) hscale (hx i))
    (by simpa only [norm_zero,mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0)))
  simpa only [add_zero] using h

 
theorem four_forward_transfer (V : α → H ≃ₗᵢ[ℂ] H) (F Z : H →L[ℂ] H)
    (hF : ∀x,‖F x‖≤‖x‖) (hZ : ∀x,‖Z x‖≤‖x‖)
    (S : α → ℝ) (o s y q : α → H) (hS : ∀ᶠ t in l,0≤S t)
    (ho : Tendsto (fun t => S t*‖o t-y t‖) l (𝓝 0))
    (hs : Tendsto (fun t => S t*‖s t-q t‖) l (𝓝 0))
    (h1 : Tendsto (fun t => S t*‖V t (y t)-y t‖) l (𝓝 0))
    (h2 : Tendsto (fun t => S t*‖V t (q t)-F (q t)‖) l (𝓝 0))
    (h3 : Tendsto (fun t => S t*‖V t (Z (y t))-Z (y t)‖) l (𝓝 0))
    (h4 : Tendsto (fun t => S t*‖V t (Z (q t))-F (Z (q t))‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t (o t)-o t‖) l (𝓝 0) ∧
    Tendsto (fun t => S t*‖V t (s t)-F (s t)‖) l (𝓝 0) ∧
    Tendsto (fun t => S t*‖V t (Z (o t))-Z (o t)‖) l (𝓝 0) ∧
    Tendsto (fun t => S t*‖V t (Z (s t))-F (Z (s t))‖) l (𝓝 0) := by
  exact ⟨scaled_identity_transfer V S o y hS h1 ho,
    scaled_difference_transfer V F hF S s q hS h2 hs,
    scaled_identity_transfer V S (fun t => Z (o t)) (fun t => Z (y t)) hS h3
      (scaled_map_difference Z hZ S o y hS ho),
    scaled_difference_transfer V F hF S (fun t => Z (s t)) (fun t => Z (q t)) hS h4
      (scaled_map_difference Z hZ S s q hS hs)⟩

end ForwardControl

namespace CoherentFock
open RootSpin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 
theorem half_mixer_anticommutes (x : SpinSpace E) :
    SpinOperators.act Z (SpinOperators.act (R (Real.pi/2)) x)=
      -SpinOperators.act (R (Real.pi/2)) (SpinOperators.act Z x) := by
  ext i
  fin_cases i <;>
    simp [SpinOperators.act_apply,Fin.sum_univ_two,RootSpin.R,RootSpin.Z,RootSpin.X,
      Real.cos_pi_div_two,Real.sin_pi_div_two]

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin

 

theorem standard_four_forward_errors {α κ : Type*} [Fintype κ] {l : Filter α}
    (r : α → ℝ) (w : α → List Gate)
    (o s : α → SpinSpace ModeInfinity) (x : α → PreSpin ModeInfinity)
    (d : κ → α → ModeInfinity) (z : κ → α → PreSpin ModeInfinity)
    (B A C : ℝ) (hB : 0≤B) (hA : 0≤A) (hC : 0≤C)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ t in l,0<r t)
    (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hz : ∀i,∀ᶠ t in l,SpinRadiusLE (z i t) B ∧ spinMass (z i t)≤A)
    (hd : ∀i,∀ᶠ t in l,‖d i t‖≤C)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=o t+s t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0))
    (ho : Tendsto (fun t => (r t)⁻¹*‖o t-spinCoe (x t)‖) l (𝓝 0))
    (hsp : Tendsto (fun t => (r t)⁻¹*‖s t-
      (∑i,(r t:ℂ) • actualPacket ((r t)⁻¹) (d i t) (z i t))‖) l (𝓝 0))
    (hZ : ∀i,Tendsto (fun t => -2*(⟪insertionInfinity (w t),d i t⟫_ℂ).im) l (𝓝 (v i).1))
    (hY : ∀i,Tendsto (fun t => -2*(⟪insertionYInfinity (w t),d i t⟫_ℂ).im) l (𝓝 (v i).2)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      Tendsto (fun t => (r t)⁻¹*‖probeGain (r t) (w t) a K (o t)-o t‖) l (𝓝 0) ∧
      Tendsto (fun t => (r t)⁻¹*‖probeGain (r t) (w t) a K (s t)-SpinOperators.act (R θ) (s t)‖) l (𝓝 0) ∧
      Tendsto (fun t => (r t)⁻¹*‖probeGain (r t) (w t) a K (SpinOperators.act Z (o t))-
        SpinOperators.act Z (o t)‖) l (𝓝 0) ∧
      Tendsto (fun t => (r t)⁻¹*‖probeGain (r t) (w t) a K (SpinOperators.act Z (s t))-
        SpinOperators.act (R θ) (SpinOperators.act Z (s t))‖) l (𝓝 0) := by
  classical
  obtain ⟨hS,hscale⟩ := reciprocal_scale_eventually r hr hp
  have hS0 : ∀ᶠ t in l,0≤(r t)⁻¹ := hscale.mono (fun _ h => h.2.1)
  have he0 := PacketGeometry.tendsto_of_scaled (fun t => (r t)⁻¹)
    (fun t => ‖o t-spinCoe (x t)‖) hS (Eventually.of_forall (fun _ => norm_nonneg _)) ho
  have hvac : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      spinCoe (x t)+s t+(o t-spinCoe (x t)) := by
    filter_upwards [hψ] with t ht
    rw [ht]
    abel
  obtain ⟨K,a,ordinary,special⟩ := standard_selective_accuracy r w x s
    (fun t => o t-spinCoe (x t)) B A hB hA v hv θ hr hp hx hvac hs he0
  let V (t : α) := probeGain (r t) (w t) a K
  let F := SpinOperators.act (R θ) (H:=Space ModeInfinity)
  have hF : ∀q,‖F q‖≤‖q‖ := fun q => (SpinOperators.norm_act (R_unitary _) q).le
  have hZc : ∀q : SpinSpace ModeInfinity,‖SpinOperators.act Z q‖≤‖q‖ :=
    fun q => (SpinOperators.norm_act Z_unitary q).le
  have hzZ : ∀i,∀ᶠ t in l,SpinRadiusLE (preRoot Z (z i t)) B ∧ spinMass (preRoot Z (z i t))≤2*A := by
    intro i
    filter_upwards [hz i] with t ht
    exact ⟨ht.1.preRoot Z,(spinMass_preRoot Z _).trans (by rw [matrixMass_Z]; linarith [ht.2])⟩
  have hxZ : ∀ᶠ t in l,SpinRadiusLE (preRoot Z (x t)) B ∧ spinMass (preRoot Z (x t))≤2*A := by
    filter_upwards [hx] with t ht
    exact ⟨ht.1.preRoot Z,(spinMass_preRoot Z _).trans (by rw [matrixMass_Z]; linarith [ht.2])⟩
  have hsum := ForwardControl.scaled_amplitude_finSum V F hF r (fun t => (r t)⁻¹)
    (fun t i => actualPacket ((r t)⁻¹) (d i t) (z i t)) hS0
    (hscale.mono (fun _ h => ⟨h.1,h.2.2⟩))
    (fun i => special i (d i) (z i) C B A hC hB hA (hd i) (hz i) (hZ i) (hY i))
  have hsumZ := ForwardControl.scaled_amplitude_finSum V F hF r (fun t => (r t)⁻¹)
    (fun t i => actualPacket ((r t)⁻¹) (d i t) (preRoot Z (z i t))) hS0
    (hscale.mono (fun _ h => ⟨h.1,h.2.2⟩))
    (fun i => special i (d i) (fun t => preRoot Z (z i t)) C B (2*A) hC hB (by positivity)
      (hd i) (hzZ i) (hZ i) (hY i))
  refine ⟨K,a,?_⟩
  apply ForwardControl.four_forward_transfer V F (SpinOperators.act Z) hF hZc
    (fun t => (r t)⁻¹) o s (fun t => spinCoe (x t))
    (fun t => ∑i,(r t:ℂ) • actualPacket ((r t)⁻¹) (d i t) (z i t)) hS0 ho hsp
    (ordinary x B A hB hA hx) hsum
  · simpa only [spinCoe_preRoot] using ordinary (fun t => preRoot Z (x t)) B (2*A) hB (by positivity) hxZ
  · simpa only [map_sum,map_smul,actualPacket_root] using hsumZ

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem spinCoe_smul (c : ℂ) (x : PreSpin E) : spinCoe (c • x)=c • spinCoe x := by
  ext i
  simp only [spinCoe_apply,Pi.smul_apply,UniformSpace.Completion.coe_smul,PiLp.smul_apply]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
@[simp] theorem spinMass_smul (c : ℂ) (x : PreSpin E) : spinMass (c • x)=‖c‖*spinMass x := by
  simp only [spinMass,Pi.smul_apply,mass_smul,Finset.mul_sum]

omit [InnerProductSpace ℂ E] in
theorem SpinRadiusLE.smul {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B) (c : ℂ) :
    SpinRadiusLE (c • x) B := fun i => (hx i).smul c

end CoherentFock

namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {l : Filter α}

 
theorem scaled_identity_add (V : α → H ≃ₗᵢ[ℂ] H) (S : α → ℝ) (x y : α → H)
    (hS : ∀ᶠ q in l,0≤S q)
    (hx : Tendsto (fun q => S q*‖V q (x q)-x q‖) l (𝓝 0))
    (hy : Tendsto (fun q => S q*‖V q (y q)-y q‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖V q (x q+y q)-(x q+y q)‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [add_zero] using hx.add hy)
  · filter_upwards [hS] with q hq
    exact mul_nonneg hq (norm_nonneg _)
  · filter_upwards [hS] with q hq
    have he : V q (x q+y q)-(x q+y q)=(V q (x q)-x q)+(V q (y q)-y q) := by
      rw [map_add]; abel
    rw [he,←mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hq

theorem scaled_identity_sub (V : α → H ≃ₗᵢ[ℂ] H) (S : α → ℝ) (x y : α → H)
    (hS : ∀ᶠ q in l,0≤S q)
    (hx : Tendsto (fun q => S q*‖V q (x q)-x q‖) l (𝓝 0))
    (hy : Tendsto (fun q => S q*‖V q (y q)-y q‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖V q (x q-y q)-(x q-y q)‖) l (𝓝 0) := by
  have hn : Tendsto (fun q => S q*‖V q (-y q)-(-y q)‖) l (𝓝 0) := by
    simpa only [map_neg,neg_sub_neg,norm_sub_rev] using hy
  simpa only [sub_eq_add_neg] using scaled_identity_add V S x (fun q => -y q) hS hx hn

 

theorem scaled_square_small_amplitude (S r : α → ℝ) (x : α → H) (C : ℝ) (hC : 0≤C)
    (hr : Tendsto r l (𝓝 0)) (hs : ∀ᶠ q in l,0≤S q ∧ 0≤r q ∧ S q*r q=1)
    (hx : ∀ᶠ q in l,‖x q‖≤C) :
    Tendsto (fun q => S q*‖(r q:ℂ) • x q‖^2) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa using hr.mul_const (C^2))
  · filter_upwards [hs] with q hq
    exact mul_nonneg hq.1 (sq_nonneg _)
  · filter_upwards [hs,hx] with q hq hb
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq.2.1]
    calc
      S q*(r q*‖x q‖)^2 = (S q*r q)*r q*‖x q‖^2 := by ring
      _ = r q*‖x q‖^2 := by rw [hq.2.2,one_mul]
      _ ≤ r q*C^2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hC |>.mpr hb) hq.2.1

end ForwardControl

namespace PointedTree
open CoherentFock RootSpin
local instance hugeFlipRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance hugeFlipRealSMul : SMul ℝ ModeInfinity := hugeFlipRealModule.toDistribMulAction.toSMul

@[simp] theorem actualPacket_smul (S : ℝ) (d : ModeInfinity) (c : ℂ) (x : PreSpin ModeInfinity) :
    actualPacket S d (c • x)=c • actualPacket S d x := by
  simp only [actualPacket,spinCoe_smul,map_smul]

theorem norm_actualPacket_le_mass (S : ℝ) (d : ModeInfinity) (x : PreSpin ModeInfinity) :
    ‖actualPacket S d x‖ ≤ spinMass x := by
  simpa only [actualPacket,norm_spinW] using norm_spinCoe_le_mass x

 

theorem huge_four_forward_errors {α κ : Type*} [Fintype κ] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (t : ℝ) (ht : t≠0)
    (o s : α → SpinSpace ModeInfinity) (xp xm : α → PreSpin ModeInfinity)
    (d : κ → α → ModeInfinity) (z : κ → α → PreSpin ModeInfinity)
    (B A C : ℝ) (hB : 0≤B) (hA : 0≤A) (hC : 0≤C)
    (c y : κ → ℝ) (hc : ∀i,c i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0≤r q)
    (hS : Tendsto S l atTop) (hscale : ∀ᶠ q in l,S q*r q=1)
    (hxp : ∀ᶠ q in l,SpinRadiusLE (xp q) B ∧ spinMass (xp q)≤A)
    (hxm : ∀ᶠ q in l,SpinRadiusLE (xm q) B ∧ spinMass (xm q)≤A)
    (hz : ∀i,∀ᶠ q in l,SpinRadiusLE (z i q) B ∧ spinMass (z i q)≤A)
    (hd : ∀i,∀ᶠ q in l,‖d i q‖≤C)
    (hψ : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=o q+s q)
    (ho : Tendsto (fun q => S q*‖o q-(actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q)+
      actualPacket (S q) (t • insertionInfinity (w q)) (xm q))‖) l (𝓝 0))
    (hsp : Tendsto (fun q => S q*‖s q-(∑i,(r q:ℂ) • actualPacket (S q) (d i q) (z i q))‖) l (𝓝 0))
    (hop : ∀ᶠ q in l,SpinOperators.act Z (actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))=
      actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))
    (hom : ∀ᶠ q in l,SpinOperators.act Z (actualPacket (S q) (t • insertionInfinity (w q)) (xm q))=
      -actualPacket (S q) (t • insertionInfinity (w q)) (xm q))
    (hZ : ∀i,Tendsto (fun q => (⟪insertionInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (c i)))
    (hY : ∀i,Tendsto (fun q => -2*(⟪insertionYInfinity (w q),d i q⟫_ℂ).im) l (𝓝 (y i))) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse),
      Tendsto (fun q => S q*‖probeGain (r q) (w q) a K (o q)-o q‖) l (𝓝 0) ∧
      Tendsto (fun q => S q*‖probeGain (r q) (w q) a K (s q)-SpinOperators.act (R θ) (s q)‖) l (𝓝 0) ∧
      Tendsto (fun q => S q*‖probeGain (r q) (w q) a K (SpinOperators.act Z (o q))-
        SpinOperators.act Z (o q)‖) l (𝓝 0) ∧
      Tendsto (fun q => S q*‖probeGain (r q) (w q) a K (SpinOperators.act Z (s q))-
        SpinOperators.act (R θ) (SpinOperators.act Z (s q))‖) l (𝓝 0) := by
  classical
  let op (q : α) := actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q)
  let om (q : α) := actualPacket (S q) (t • insertionInfinity (w q)) (xm q)
  let xs (i : κ) (q : α) := (r q:ℂ) • z i q
  let sp (q : α) := ∑i,actualPacket (S q) (d i q) (xs i q)
  let ρ (q : α) := (o q-(op q+om q))+(s q-sp q)
  have hS0 : ∀ᶠ q in l,0≤S q := hS.eventually (eventually_ge_atTop 0)
  have hscl : ∀ᶠ q in l,0≤S q ∧ 0≤r q ∧ S q*r q=1 := by
    filter_upwards [hS0,hp,hscale] with q hq hpq he
    exact ⟨hq,hpq,he⟩
  have hρ : Tendsto (fun q => S q*‖ρ q‖) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [add_zero] using ho.add hsp)
    · filter_upwards [hS0] with q hq
      exact mul_nonneg hq (norm_nonneg _)
    · filter_upwards [hS0] with q hq
      simpa only [ρ,op,om,sp,xs,actualPacket_smul,mul_add] using
        mul_le_mul_of_nonneg_left (norm_add_le (o q-(op q+om q)) (s q-sp q)) hq
  have hxs : ∀i,∀ᶠ q in l,SpinRadiusLE (xs i q) B ∧ spinMass (xs i q)≤A := by
    intro i
    filter_upwards [hz i,hp,hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with q hq hpq hu
    refine ⟨hq.1.smul _,?_⟩
    simp only [xs,spinMass_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpq]
    exact (mul_le_mul_of_nonneg_left hq.2 hpq).trans (mul_le_of_le_one_left hA hu.le)
  have hnorm : ∀ᶠ q in l,‖∑i,actualPacket (S q) (d i q) (z i q)‖≤Fintype.card κ*A := by
    filter_upwards [eventually_all.mpr hz] with q hq
    calc
      _ ≤ ∑i,‖actualPacket (S q) (d i q) (z i q)‖ := norm_sum_le _ _
      _ ≤ ∑_i : κ,A := Finset.sum_le_sum (fun i _ => (norm_actualPacket_le_mass ..).trans (hq i).2)
      _ = _ := by simp
  have hssq := ForwardControl.scaled_square_small_amplitude S r
    (fun q => ∑i,actualPacket (S q) (d i q) (z i q)) (Fintype.card κ*A) (by positivity) hr hscl hnorm
  have hvac : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=op q+om q+sp q+ρ q := by
    filter_upwards [hψ] with q hq
    rw [hq]
    dsimp only [ρ]
    abel
  obtain ⟨K,a,ordinary,special⟩ := huge_selective_accuracy r S w t ht d xp xm xs ρ B A hB hA c y hc θ
    hr hp hS hscale hxp hxm hxs hZ hvac hop hom hρ
    (by simpa only [xs,actualPacket_smul,←Finset.smul_sum] using hssq)
  let V (q : α) := probeGain (r q) (w q) a K
  let F := SpinOperators.act (R θ) (H:=Space ModeInfinity)
  have hF : ∀q,‖F q‖≤‖q‖ := fun q => (SpinOperators.norm_act (R_unitary _) q).le
  have hZc : ∀q : SpinSpace ModeInfinity,‖SpinOperators.act Z q‖≤‖q‖ :=
    fun q => (SpinOperators.norm_act Z_unitary q).le
  have hzZ : ∀i,∀ᶠ q in l,SpinRadiusLE (preRoot Z (z i q)) B ∧ spinMass (preRoot Z (z i q))≤2*A := by
    intro i
    filter_upwards [hz i] with q hq
    exact ⟨hq.1.preRoot Z,(spinMass_preRoot Z _).trans (by rw [matrixMass_Z]; linarith [hq.2])⟩
  have hsum := ForwardControl.scaled_amplitude_finSum V F hF r S
    (fun q i => actualPacket (S q) (d i q) (z i q)) hS0
    (hscl.mono (fun _ h => ⟨h.2.1,h.2.2⟩))
    (fun i => special i (d i) (z i) C B A hC hB hA (hd i) (hz i) ((hZ i).const_mul (-2)) (hY i))
  have hsumZ := ForwardControl.scaled_amplitude_finSum V F hF r S
    (fun q i => actualPacket (S q) (d i q) (preRoot Z (z i q))) hS0
    (hscl.mono (fun _ h => ⟨h.2.1,h.2.2⟩))
    (fun i => special i (d i) (fun q => preRoot Z (z i q)) C B (2*A) hC hB (by positivity)
      (hd i) (hzZ i) ((hZ i).const_mul (-2)) (hY i))
  have hOrd := ForwardControl.scaled_identity_add V S op om hS0
    (ordinary (-t) xp B A hB hA hxp) (ordinary t xm B A hB hA hxm)
  have hOrdZ : Tendsto (fun q => S q*‖V q (SpinOperators.act Z (op q+om q))-
      SpinOperators.act Z (op q+om q)‖) l (𝓝 0) := by
    apply (ForwardControl.scaled_identity_sub V S op om hS0
      (ordinary (-t) xp B A hB hA hxp) (ordinary t xm B A hB hA hxm)).congr'
    filter_upwards [hop,hom] with q hpq hmq
    change S q*‖V q (op q-om q)-(op q-om q)‖=_
    rw [map_add,hpq,hmq,←sub_eq_add_neg]
  refine ⟨K,a,?_⟩
  apply ForwardControl.four_forward_transfer V F (SpinOperators.act Z) hF hZc S o s
    (fun q => op q+om q) (fun q => ∑i,(r q:ℂ) • actualPacket (S q) (d i q) (z i q))
    hS0 ho hsp hOrd hsum hOrdZ
  simpa only [map_sum,map_smul,actualPacket_root] using hsumZ

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 

def BoundedPacket (l : Filter α) (x : α → SpinSpace E) : Prop :=
  ∃ (p : α → PreSpin E) (B A : ℝ), 0≤B ∧ 0≤A ∧
    (∀q,x q=spinCoe (p q)) ∧
    (∀ᶠ q in l,SpinRadiusLE (p q) B ∧ spinMass (p q)≤A)

namespace BoundedPacket

theorem norm_bounded {x : α → SpinSpace E} (hx : BoundedPacket l x) :
    ∃C : ℝ,0≤C ∧ ∀ᶠ q in l,‖x q‖≤C := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  refine ⟨A,hA,?_⟩
  filter_upwards [hbound] with q hq
  rw [hp q]
  exact (norm_spinCoe_le_mass _).trans hq.2

theorem vacuum : BoundedPacket l (fun _ : α => PointedTree.vacuum E) := by
  refine ⟨fun _ => SeedInitialization.preVacuum E,0,2*‖PointedTree.spinCoefficient‖,
    le_rfl,by positivity,fun _ => SeedInitialization.spinCoe_preVacuum.symm,?_⟩
  exact Eventually.of_forall fun _ => ⟨SeedInitialization.radius_preVacuum,
    SeedInitialization.spinMass_preVacuum.le⟩

theorem root {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (P : Matrix (Fin 2) (Fin 2) ℂ) :
    BoundedPacket l (fun q => SpinOperators.act P (x q)) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  refine ⟨fun q => preRoot P (p q),B,matrixMass P*A,hB,
    mul_nonneg (matrixMass_nonneg _) hA,?_,?_⟩
  · exact fun q => by simp only [spinCoe_preRoot,hp]
  · filter_upwards [hbound] with q hq
    exact ⟨hq.1.preRoot P,(spinMass_preRoot _ _).trans
      (mul_le_mul_of_nonneg_left hq.2 (matrixMass_nonneg _))⟩

theorem pulse {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (d : α → E) (C : ℝ) (hC : 0≤C) (hd : ∀ᶠ q in l,‖d q‖≤C) :
    BoundedPacket l (fun q => WZ (d q) (x q)) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  refine ⟨fun q => preWZ (d q) (p q),C+B,A,add_nonneg hC hB,hA,?_,?_⟩
  · exact fun q => by simp only [spinCoe_preWZ,hp]
  · filter_upwards [hbound,hd] with q hq hdq
    exact ⟨fun i => (hq.1.preWZ (d q) i).mono (by linarith),
      (spinMass_preWZ _ _).trans hq.2⟩

theorem smul {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (c : α → ℂ) (C : ℝ) (hC : 0≤C) (hc : ∀ᶠ q in l,‖c q‖≤C) :
    BoundedPacket l (fun q => c q • x q) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  refine ⟨fun q => c q • p q,B,C*A,hB,mul_nonneg hC hA,?_,?_⟩
  · exact fun q => by simp only [spinCoe_smul,hp]
  · filter_upwards [hbound,hc] with q hq hcq
    refine ⟨hq.1.smul _,?_⟩
    rw [spinMass_smul]
    exact mul_le_mul hcq hq.2 (spinMass_nonneg _) hC

end BoundedPacket

 

structure PacketUnitaryFamily (l : Filter α) where
  op : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E
  forward : ∀x,BoundedPacket l x → BoundedPacket l (fun q => op q (x q))
  backward : ∀x,BoundedPacket l x → BoundedPacket l (fun q => (op q).symm (x q))

namespace PacketUnitaryFamily

def ident : PacketUnitaryFamily (E:=E) l where
  op _ := LinearIsometryEquiv.refl ℂ _
  forward _ hx := hx
  backward _ hx := hx

def root (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) : PacketUnitaryFamily (E:=E) l where
  op _ := SpinOperators.actEquiv P hP
  forward _ hx := hx.root P
  backward _ hx := by simpa only [SpinOperators.actEquiv_symm_apply] using hx.root P.conjTranspose

def pulse (d : α → E) (C : ℝ) (hC : 0≤C) (hd : ∀ᶠ q in l,‖d q‖≤C) :
    PacketUnitaryFamily (E:=E) l where
  op q := costEquiv (d q)
  forward _ hx := hx.pulse d C hC hd
  backward _ hx := by
    simpa only [costEquiv_symm_apply] using hx.pulse (fun q => -d q) C hC
      (hd.mono (fun q hq => by simpa only [norm_neg] using hq))

def trans (A B : PacketUnitaryFamily (E:=E) l) : PacketUnitaryFamily (E:=E) l where
  op q := (A.op q).trans (B.op q)
  forward x hx := B.forward _ (A.forward x hx)
  backward x hx := A.backward _ (B.backward x hx)

def symm (A : PacketUnitaryFamily (E:=E) l) : PacketUnitaryFamily (E:=E) l where
  op q := (A.op q).symm
  forward := A.backward
  backward := A.forward

 

theorem insertion_bounded (A : PacketUnitaryFamily (E:=E) l)
    (P : Matrix (Fin 2) (Fin 2) ℂ) :
    BoundedPacket l (fun q => (A.op q).symm (SpinOperators.act P (A.op q (PointedTree.vacuum E)))) :=
  A.backward _ ((A.forward _ BoundedPacket.vacuum).root P)

end PacketUnitaryFamily
end CoherentFock

end

end OAI
