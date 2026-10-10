import Mathlib
import OAI.Probability.ParisiFinite.UnitaryUp

namespace OAI

/-! Actual Displacement. -/

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
open scoped InnerProductSpace Topology
open Filter
namespace PointedTree
open CoherentFock RootSpin

local instance modeRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance modeRealSMul : SMul ℝ ModeInfinity := modeRealModule.toDistribMulAction.toSMul

def actualDisplacement (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) : ModeInfinity :=
  -((r*(a k).2 : ℝ):ℂ) • actualProbeDirection r w a k

@[simp] theorem norm_actualDisplacement (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    ‖actualDisplacement r w a k‖=|r| *|(a k).2| := by
  simp only [actualDisplacement,norm_smul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    norm_actualProbeDirection,mul_one,abs_mul]

def actualTail (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) : PreSpin ModeInfinity :=
  ProbeProduct.coreAct (fun j => preCenteredProbe (R (a j).1) (actualDisplacement r w a j) e)
    (List.range k).reverse x

 
theorem probeGain_packet (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) :
    probeGain r w a k (spinW e (spinCoe x))=spinW e (spinCoe (actualTail r w a k e x)) := by
  have h := spinCoe_coreCentered (List.range k).reverse (fun j => R (a j).1)
    (actualDisplacement r w a) e (fun j _ => R_unitary _) x
  change spinCoe (actualTail r w a k e x)=spinW (-e)
    (ProbeProduct.act (actualProbe r w a) (List.range k).reverse (spinW e (spinCoe x))) at h
  rw [probeGain_product,h,spinW_inv']

 
theorem spinMass_actualTail (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) :
    spinMass (actualTail r w a k e x)≤(4^4:ℝ)^k*spinMass x := by
  apply (spinMass_coreCentered (List.range k).reverse (fun j => R (a j).1)
    (actualDisplacement r w a) e 4 (by norm_num) (fun j _ => matrixMass_R_le _)
    (fun j _ => by rw [R_star]; exact matrixMass_R_le _) x).trans_eq
  simp only [List.length_reverse,List.length_range]

 
theorem spinMass_actualTail_le (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k K : ℕ)
    (hk : k≤K) (e : ModeInfinity) (x : PreSpin ModeInfinity) :
    spinMass (actualTail r w a k e x)≤(4^4:ℝ)^K*spinMass x := by
  exact (spinMass_actualTail r w a k e x).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (spinMass_nonneg _))

theorem radius_actualTail (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) (B T : ℝ)
    (hx : SpinRadiusLE x B) (hT : ∀j<k,|(a j).2|≤T) :
    SpinRadiusLE (actualTail r w a k e x) (B+k*(|r| *T)) := by
  have h := radius_coreCentered (List.range k).reverse (fun j => R (a j).1)
    (actualDisplacement r w a) e B (|r| *T) (by
      intro j hj
      rw [List.mem_reverse,List.mem_range] at hj
      rw [norm_actualDisplacement]
      exact mul_le_mul_of_nonneg_left (hT j hj) (abs_nonneg _)) x hx
  simpa only [actualTail,List.length_reverse,List.length_range] using h

theorem radius_actualTail_le (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k K : ℕ)
    (hk : k≤K) (e : ModeInfinity) (x : PreSpin ModeInfinity) (B T : ℝ)
    (hx : SpinRadiusLE x B) (hT0 : 0≤T) (hr : |r|≤1) (hT : ∀j<K,|(a j).2|≤T) :
    SpinRadiusLE (actualTail r w a k e x) (B+K*T) := by
  intro i
  apply (radius_actualTail r w a k e x B T hx (fun j hj => hT j (hj.trans_le hk)) i).mono
  have h1 : |r| *T≤T := by nlinarith [abs_nonneg r]
  have h2 : (k:ℝ)≤K := Nat.cast_le.mpr hk
  gcongr

 

theorem rapid_decay_actual_packets {α : Type*} {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k K : ℕ) (hk : k≤K)
    (d e : α → ModeInfinity) (x y : α → PreSpin ModeInfinity)
    (P : α → Matrix (Fin 2) (Fin 2) ℂ) (hR : Tendsto Rsc l atTop)
    (B A C δ T : ℝ) (hA : 0≤A) (hC : 0≤C) (hδ : 0<δ) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ t in l,|r t|≤1)
    (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hy : ∀ᶠ t in l,SpinRadiusLE (y t) B ∧ spinMass (y t)≤A)
    (hP : ∀ᶠ t in l,matrixMass (P t)≤C) (hsep : ∀ᶠ t in l,δ≤‖d t-e t‖) (M : ℕ) :
    Tendsto (fun t => (Rsc t)^M*
      ‖⟪SpinOperators.act (P t) (probeGain (r t) (w t) a k (spinW (Rsc t • d t : ModeInfinity) (spinCoe (x t)))),
        probeGain (r t) (w t) a k (spinW (Rsc t • e t : ModeInfinity) (spinCoe (y t)))⟫_ℂ‖) l (𝓝 0) := by
  let X (t : α) : PreSpin ModeInfinity := actualTail (r t) (w t) a k (Rsc t • d t : ModeInfinity) (x t)
  let Y (t : α) : PreSpin ModeInfinity := actualTail (r t) (w t) a k (Rsc t • e t : ModeInfinity) (y t)
  have hX : ∀ᶠ t in l,SpinRadiusLE (X t) (B+K*T) ∧ spinMass (X t)≤(4^4:ℝ)^K*A := by
    filter_upwards [hr,hx] with t hrt hxt
    exact ⟨radius_actualTail_le _ _ _ k K hk _ _ B T hxt.1 hT0 hrt hT,
      (spinMass_actualTail_le _ _ _ k K hk _ _).trans
        (mul_le_mul_of_nonneg_left hxt.2 (by positivity))⟩
  have hY : ∀ᶠ t in l,SpinRadiusLE (Y t) (B+K*T) ∧ spinMass (Y t)≤(4^4:ℝ)^K*A := by
    filter_upwards [hr,hy] with t hrt hyt
    exact ⟨radius_actualTail_le _ _ _ k K hk _ _ B T hyt.1 hT0 hrt hT,
      (spinMass_actualTail_le _ _ _ k K hk _ _).trans
        (mul_le_mul_of_nonneg_left hyt.2 (by positivity))⟩
  simpa only [probeGain_packet] using rapid_decay_spin_matrix Rsc d e X Y P hR
    (B+K*T) ((4^4:ℝ)^K*A) C δ (by positivity) hC hδ hX hY hP hsep M

end PointedTree

 

open scoped InnerProductSpace Topology
open Filter
namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem phaseZ_zero_apply (x : SpinSpace E) : phaseZ 0 x=x := by
  ext i
  simp [phaseZ_apply]

@[simp] theorem probePhase_zero_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A∈unitary _)
    (x : SpinSpace E) : probePhase A 0 x=x := by
  rw [probePhase_apply,phaseZ_zero_apply,root_left_inverse A hA]

theorem ProbeProduct.phase_zero {ι : Type*} (l : List ι) (A : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀j∈l,A j∈unitary _) (x : SpinSpace E) :
    ProbeProduct.act (fun j => probePhase (A j) 0) l x=x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [ProbeProduct.act_cons, ih (fun i hi => hA i (List.mem_cons_of_mem _ hi)),
      probePhase_zero_apply _ (hA j (List.mem_cons_self ..))]

 

theorem centered_product_forward_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (L M α : ℝ)
    (hL : 0≤L) (hM : 1≤M) (hα : 0≤α)
    (hA : ∀j∈l,A j∈unitary _) (hD : ∀j∈l,‖D j‖≤L)
    (hMass : ∀j∈l,matrixMass (A j)≤M) (hMS : ∀j∈l,matrixMass (A j).conjTranspose≤M)
    (hp : ∀j∈l,|(-2*(⟪D j,e⟫_ℂ).im)|≤α) (x : PreSpin E) :
    ‖spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e (spinCoe x)))-spinCoe x‖≤
      ((L^2+L)*M)*l.length*(M^2)^l.length*spinBound x+l.length*α*‖spinCoe x‖ := by
  have h := special_product_bound l A D e (fun _ => 0) L M α hL hM hα
    hA hD hMass hMS (by simpa only [sub_zero] using hp) x
  rwa [ProbeProduct.phase_zero l A hA] at h

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin

 
theorem actual_forward_bound (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) (T α : ℝ) (hT : 0≤T) (hα : 0≤α)
    (ha : ∀j<k,|(a j).2|≤T)
    (hp : ∀j<k,|(-2*(⟪actualDisplacement r w a j,e⟫_ℂ).im)|≤α) :
    ‖probeGain r w a k (spinW e (spinCoe x))-spinW e (spinCoe x)‖≤
      (((|r| *T)^2+|r| *T)*4)*k*(4^2:ℝ)^k*spinBound x+k*α*‖spinCoe x‖ := by
  have hn := norm_spinW (-e) (probeGain r w a k (spinW e (spinCoe x))-spinW e (spinCoe x))
  rw [map_sub,spinW_inv] at hn
  rw [←hn,probeGain_product]
  have h := centered_product_forward_bound (List.range k).reverse (fun j => R (a j).1)
    (actualDisplacement r w a) e (|r| *T) 4 α (mul_nonneg (abs_nonneg _) hT) (by norm_num) hα
    (fun j _ => R_unitary _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj
        rw [norm_actualDisplacement]; exact mul_le_mul_of_nonneg_left (ha j hj) (abs_nonneg _))
    (fun j _ => matrixMass_R_le _) (fun j _ => by rw [R_star]; exact matrixMass_R_le _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj; exact hp j hj) x
  have hfun : (fun j => probe (R (a j).1) (actualDisplacement r w a j))=actualProbe r w a := by
    funext j; rfl
  rw [hfun] at h
  simpa only [List.length_reverse,List.length_range] using h

 

theorem tendsto_actual_direction {α : Type*} {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (h0 : Tendsto (fun t =>
      ‖probeGain (r t) (w t) a k (ordinaryLocal (w t) (vacuum ModeInfinity))-
        ordinaryLocal (w t) (vacuum ModeInfinity)‖) l (𝓝 0))
    (hP : Tendsto (fun t =>
      ‖probeGain (r t) (w t) a k (SpinOperators.act ((R (a k).1).conjTranspose*Z*R (a k).1)
        (ordinaryLocal (w t) (vacuum ModeInfinity)))-
        SpinOperators.act ((R (a k).1).conjTranspose*Z*R (a k).1)
          (ordinaryLocal (w t) (vacuum ModeInfinity))‖) l (𝓝 0)) :
    Tendsto (fun t => ‖actualProbeDirection (r t) (w t) a k-
      insertionInfinity (.mixer (a k).1::w t)‖) l (𝓝 0) := by
  have h := h0.add hP
  simp only [add_zero] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => actual_direction_change_bound (r t) (w t) a k) h

end PointedTree

 

open scoped InnerProductSpace BigOperators
namespace PulseControl
variable {H : Type*} [AddCommGroup H] [Module ℝ H]

 
theorem two_axis_sum (w : List (Bool×ℝ)) (f : Bool → H) :
    (w.map (fun p => p.2 • f p.1)).sum=
      (((w.filter (fun p => decide (p.1=true))).map Prod.snd).sum) • f true+
      (((w.filter (fun p => decide (p.1=false))).map Prod.snd).sum) • f false := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rcases p with ⟨b,t⟩
    cases b <;> simp only [List.map_cons,List.sum_cons,ih,List.filter_cons,
      Bool.false_eq_true, Bool.true_eq_false,decide_false,decide_true,Bool.false_eq_true,
       ite_false,ite_true,List.map_cons,List.sum_cons,add_smul]
    all_goals abel

theorem two_axis_zero_clock (w : List (Bool×ℝ))
    (hw : ∀b,((w.filter (fun p => decide (p.1=b))).map Prod.snd).sum=0) (f : Bool → H) :
    (w.map (fun p => p.2 • f p.1)).sum=0 := by
  rw [two_axis_sum,hw true,hw false,zero_smul,zero_smul,add_zero]

end PulseControl

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem probeField_zero_two_clocks (w : List (Bool×ℝ))
    (hw : ∀b,((w.filter (fun p => decide (p.1=b))).map Prod.snd).sum=0)
    (A : Bool → Matrix (Fin 2) (Fin 2) ℂ) (v : Bool → E) (x : PreSpin E) :
    (w.map (fun p => Complex.I • probeField (A p.1) (-p.2 • v p.1) x)).sum=0 := by
  have h := PulseControl.two_axis_zero_clock w hw (fun b => -(Complex.I • probeField (A b) (v b) x))
  convert h using 2
  apply congrArg (fun f => List.map f w)
  funext p
  rw [probeField_real_smul]
  module

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance clockRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance clockRealDistrib : DistribSMul ℝ ModeInfinity := clockRealModule.toDistribMulAction.toDistribSMul
local instance clockRealMulAction : MulAction ℝ ModeInfinity := clockRealModule.toDistribMulAction.toMulAction
local instance clockRealSMul : SMul ℝ ModeInfinity := clockRealModule.toDistribMulAction.toSMul

def actualVelocity (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) : ModeInfinity :=
  -(a j).2 • actualProbeDirection r w a j

def startingVelocity (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) : ModeInfinity :=
  -(a j).2 • insertionInfinity (.mixer (a j).1::w)

@[simp] theorem norm_actualVelocity (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) :
    ‖actualVelocity r w a j‖=|(a j).2| := by
  simp only [actualVelocity,norm_smul,Real.norm_eq_abs,abs_neg,norm_actualProbeDirection,mul_one]

@[simp] theorem norm_startingVelocity (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) :
    ‖startingVelocity w a j‖=|(a j).2| := by
  simp only [startingVelocity,norm_smul,Real.norm_eq_abs,abs_neg,norm_insertionInfinity,mul_one]

theorem norm_velocity_difference (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) :
    ‖actualVelocity r w a j-startingVelocity w a j‖=
      |(a j).2| *‖actualProbeDirection r w a j-insertionInfinity (.mixer (a j).1::w)‖ := by
  rw [actualVelocity,startingVelocity,←smul_sub,norm_smul,Real.norm_eq_abs,abs_neg]

theorem actualDisplacement_eq_velocity (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (j : ℕ) :
    actualDisplacement r w a j=r • actualVelocity r w a j := by
  simp only [actualDisplacement,actualVelocity,smul_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),
    Complex.ofReal_mul,RCLike.ofReal_neg,mul_neg]
  rfl

 

theorem actual_zero_clock_bound (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : ModeInfinity) (x : PreSpin ModeInfinity) (T Δ α : ℝ)
    (hT : 0≤T) (hΔ : 0≤Δ) (hα : 0≤α)
    (ha : ∀j<k,|(a j).2|≤T)
    (hd : ∀j<k,‖actualProbeDirection r w a j-insertionInfinity (.mixer (a j).1::w)‖≤Δ)
    (hp : ∀j<k,|(-2*(⟪actualDisplacement r w a j,e⟫_ℂ).im)|≤α)
    (hclock : ((List.range k).reverse.map (fun j => Complex.I •
      probeField (R (a j).1) (startingVelocity w a j) x)).sum=0) :
    ‖probeGain r w a k (spinW e (spinCoe x))-spinW e (spinCoe x)‖≤
      k*((r^2*T^2+|r| *(T*Δ))*4*spinBound x)+
      (k:ℝ)^2*|r| *(2*|r| *T^2*4^3*spinBound x)+k*α*‖spinCoe x‖ := by
  have hn := norm_spinW (-e) (probeGain r w a k (spinW e (spinCoe x))-spinW e (spinCoe x))
  rw [map_sub,spinW_inv] at hn
  rw [←hn,probeGain_product]
  have h := centered_zero_clock_bound (List.range k).reverse (fun j => R (a j).1)
    (actualVelocity r w a) (startingVelocity w a) r T 4 (T*Δ) α e x hT (by norm_num)
    (mul_nonneg hT hΔ) hα (fun j _ => R_unitary _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj; simpa only [norm_actualVelocity] using ha j hj)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj; simpa only [norm_startingVelocity] using ha j hj)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj
        rw [norm_velocity_difference]; exact mul_le_mul (ha j hj) (hd j hj) (norm_nonneg _) hT)
    (fun j _ => matrixMass_R_le _) (fun j _ => by rw [R_star]; exact matrixMass_R_le _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj
        rw [←actualDisplacement_eq_velocity]; exact hp j hj) hclock
  have hf : (fun j => probe (R (a j).1) (r • actualVelocity r w a j))=actualProbe r w a := by
    funext j
    rw [←actualDisplacement_eq_velocity]
    rfl
  rw [hf] at h
  simpa only [List.length_reverse,List.length_range] using h

end PointedTree

 

open scoped InnerProductSpace Topology
open Filter
namespace PacketGeometry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem tendsto_of_scaled {α : Type*} {l : Filter α} (R d : α → ℝ)
    (hR : ∀ᶠ t in l,1≤R t) (hd : ∀ᶠ t in l,0≤d t)
    (h : Tendsto (fun t => R t*d t) l (𝓝 0)) : Tendsto d l (𝓝 0) := by
  apply squeeze_zero' hd _ h
  filter_upwards [hR,hd] with t hRt hdt
  nlinarith

 

theorem huge_imaginary_scaled_tendsto {α : Type*} {l : Filter α}
    (P : α → H →ₗ[ℂ] H) (xp xm s z ρ σ : α → H) (R δ ε a : α → ℝ)
    (hP : ∀t x y,⟪P t x,y⟫_ℂ=⟪x,P t y⟫_ℂ) (hPN : ∀t x,‖P t x‖≤‖x‖)
    (hR : ∀ᶠ t in l,1≤R t) (hδ : ∀ᶠ t in l,0≤δ t) (ha : ∀ᶠ t in l,0≤a t)
    (hx : ∀ᶠ t in l,‖xp t+xm t+s t+ρ t‖≤1)
    (hy : ∀ᶠ t in l,‖xp t-xm t+z t+σ t‖≤1)
    (hρ : ∀ᶠ t in l,‖ρ t‖≤δ t) (hσ : ∀ᶠ t in l,‖σ t‖≤δ t)
    (hs : ∀ᶠ t in l,‖s t‖≤a t) (hz : ∀ᶠ t in l,‖z t‖≤a t)
    (h1 : ∀ᶠ t in l,‖⟪P t (xp t),xm t⟫_ℂ‖≤ε t)
    (h2 : ∀ᶠ t in l,‖⟪P t (xp t),z t⟫_ℂ‖≤ε t)
    (h3 : ∀ᶠ t in l,‖⟪P t (xm t),z t⟫_ℂ‖≤ε t)
    (h4 : ∀ᶠ t in l,‖⟪P t (s t),xp t⟫_ℂ‖≤ε t)
    (h5 : ∀ᶠ t in l,‖⟪P t (s t),xm t⟫_ℂ‖≤ε t)
    (he : Tendsto (fun t => R t*ε t) l (𝓝 0))
    (hd : Tendsto (fun t => R t*δ t) l (𝓝 0))
    (ha2 : Tendsto (fun t => R t*(a t)^2) l (𝓝 0)) :
    Tendsto (fun t => R t*|(⟪P t (xp t+xm t+s t+ρ t),xp t-xm t+z t+σ t⟫_ℂ).im|) l (𝓝 0) := by
  have hd0 := tendsto_of_scaled R δ hR hδ hd
  have hb := ((he.const_mul 6).add ha2).add (hd.mul (hd0.const_add 2))
  simp only [mul_zero,zero_mul,add_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [hR] with t ht
    exact mul_nonneg (by linarith) (abs_nonneg _)
  · filter_upwards [hR,hδ,ha,hx,hy,hρ,hσ,hs,hz,h1,h2,h3,h4,h5] with t hRt hδt hat hxt hyt hρt hσt hst hzt h1t h2t h3t h4t h5t
    have h := huge_imaginary_modulus (P t) (hP t) (hPN t) (xp t) (xm t) (s t) (z t) (ρ t) (σ t)
      (δ t) (ε t) (a t) hδt hat hxt hyt hρt hσt hst hzt h1t h2t h3t h4t h5t
    calc
      _ ≤ R t*(6*ε t+(a t)^2+δ t*(2+δ t)) := mul_le_mul_of_nonneg_left h (by linarith)
      _ = _ := by ring

end PacketGeometry

namespace RootSpin
open CoherentFock

def rotatedZ (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (R β).conjTranspose*Z*R β

@[simp] theorem rotatedZ_star (β : ℝ) : (rotatedZ β).conjTranspose=rotatedZ β := by
  simp only [rotatedZ,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Z_star,Matrix.mul_assoc]

theorem rotatedZ_unitary (β : ℝ) : rotatedZ β∈unitary _ :=
  mul_mem (mul_mem (root_adjoint_unitary _ (R_unitary _)) Z_unitary) (R_unitary _)

theorem rotatedZ_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (β : ℝ) (x y : SpinSpace E) :
    ⟪SpinOperators.act (rotatedZ β) x,y⟫_ℂ=⟪x,SpinOperators.act (rotatedZ β) y⟫_ℂ := by
  have h := (SpinOperators.act (rotatedZ β) : SpinSpace E →L[ℂ] SpinSpace E).adjoint_inner_right x y
  simpa only [SpinOperators.act_adjoint,rotatedZ_star] using h.symm

end RootSpin

namespace PointedTree
open CoherentFock RootSpin

 

theorem actual_huge_phase_modulus (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (op om s ρ : SpinSpace ModeInfinity) (δ ε A : ℝ) (hδ : 0≤δ) (hA : 0≤A)
    (hψ : ordinaryLocal w (vacuum ModeInfinity)=op+om+s+ρ)
    (hop : SpinOperators.act Z op=op) (hom : SpinOperators.act Z om= -om)
    (hρ : ‖ρ‖≤δ) (hs : ‖s‖≤A)
    (h1 : ‖⟪SpinOperators.act (rotatedZ (a k).1) (probeGain r w a k op),probeGain r w a k om⟫_ℂ‖≤ε)
    (h2 : ‖⟪SpinOperators.act (rotatedZ (a k).1) (probeGain r w a k op),probeGain r w a k (SpinOperators.act Z s)⟫_ℂ‖≤ε)
    (h3 : ‖⟪SpinOperators.act (rotatedZ (a k).1) (probeGain r w a k om),probeGain r w a k (SpinOperators.act Z s)⟫_ℂ‖≤ε)
    (h4 : ‖⟪SpinOperators.act (rotatedZ (a k).1) (probeGain r w a k s),probeGain r w a k op⟫_ℂ‖≤ε)
    (h5 : ‖⟪SpinOperators.act (rotatedZ (a k).1) (probeGain r w a k s),probeGain r w a k om⟫_ℂ‖≤ε) :
    |(⟪actualProbeDirection r w a k,insertionInfinity w⟫_ℂ).im|≤6*ε+A^2+δ*(2+δ) := by
  let V := probeGain r w a k
  let P := SpinOperators.act (rotatedZ (a k).1) (H:=Space ModeInfinity)
  have he : SpinOperators.act Z (ordinaryLocal w (vacuum ModeInfinity))=
      op-om+SpinOperators.act Z s+SpinOperators.act Z ρ := by
    rw [hψ,map_add,map_add,map_add,hop,hom]
    abel
  have hx : ‖V op+V om+V s+V ρ‖≤1 := by
    rw [←map_add,←map_add,←map_add,←hψ,V.norm_map,(ordinaryLocal w).norm_map,norm_vacuum]
  have hy : ‖V op-V om+V (SpinOperators.act Z s)+V (SpinOperators.act Z ρ)‖≤1 := by
    rw [←map_sub,←map_add,←map_add,←he,V.norm_map,
      SpinOperators.norm_act Z_unitary,(ordinaryLocal w).norm_map,norm_vacuum]
  rw [actual_hermitian_diagonal,he,hψ]
  simp only [map_add,map_sub]
  simpa only [P, V, rotatedZ, ContinuousLinearMap.coe_coe, map_add] using PacketGeometry.huge_imaginary_modulus P.toLinearMap
    (rotatedZ_symmetric (a k).1) (fun x => (SpinOperators.norm_act (rotatedZ_unitary _) x).le)
    (V op) (V om) (V s) (V (SpinOperators.act Z s)) (V ρ) (V (SpinOperators.act Z ρ)) δ ε A hδ hA hx hy
    (by simpa only [V.norm_map] using hρ)
    (by simpa only [V.norm_map,SpinOperators.norm_act Z_unitary] using hρ)
    (by simpa only [V.norm_map] using hs)
    (by simpa only [V.norm_map,SpinOperators.norm_act Z_unitary] using hs)
    h1 h2 h3 h4 h5

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PacketGeometry

 

theorem scaled_norm_sum_tendsto {α H ι : Type*} {l : Filter α}
    [SeminormedAddCommGroup H] [Fintype ι]
    (R : α → ℝ) (f : α → ι → H) (hR : ∀ᶠ t in l,0≤R t)
    (hf : ∀j,Tendsto (fun t => R t*‖f t j‖) l (𝓝 0)) :
    Tendsto (fun t => R t*‖∑j,f t j‖) l (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ => hf j)
  simp only [Finset.sum_const_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [hR] with t ht
    exact mul_nonneg ht (norm_nonneg _)
  · filter_upwards [hR] with t ht
    simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_sum_le _ _) ht

end PacketGeometry

namespace PointedTree
open CoherentFock RootSpin
local instance packetRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance packetRealSMul : SMul ℝ ModeInfinity := packetRealModule.toDistribMulAction.toSMul

def actualPacket (R : ℝ) (d : ModeInfinity) (x : PreSpin ModeInfinity) : SpinSpace ModeInfinity :=
  spinW (R • d) (spinCoe x)

@[simp] theorem actualPacket_root (P : Matrix (Fin 2) (Fin 2) ℂ) (R : ℝ)
    (d : ModeInfinity) (x : PreSpin ModeInfinity) :
    SpinOperators.act P (actualPacket R d x)=actualPacket R d (preRoot P x) := by
  simp only [actualPacket, spinCoe_preRoot, spinW_root]

 
def hugeCrossError (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (op om s : SpinSpace ModeInfinity) : ℝ :=
  let V := probeGain r w a k
  let P := SpinOperators.act (rotatedZ (a k).1) (H:=Space ModeInfinity)
  ‖⟪P (V op),V om⟫_ℂ‖+
  ‖⟪P (V op),V (SpinOperators.act Z s)⟫_ℂ‖+
  ‖⟪P (V om),V (SpinOperators.act Z s)⟫_ℂ‖+
  ‖⟪P (V s),V op⟫_ℂ‖+
  ‖⟪P (V s),V om⟫_ℂ‖

 

theorem actual_huge_phase_tendsto {α : Type*} {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (op om s ρ : α → SpinSpace ModeInfinity) (δ A : α → ℝ)
    (hR : ∀ᶠ t in l,1≤Rsc t) (hδ : ∀ᶠ t in l,0≤δ t) (hA : ∀ᶠ t in l,0≤A t)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=op t+om t+s t+ρ t)
    (hop : ∀ᶠ t in l,SpinOperators.act Z (op t)=op t)
    (hom : ∀ᶠ t in l,SpinOperators.act Z (om t)= -om t)
    (hρ : ∀ᶠ t in l,‖ρ t‖≤δ t) (hs : ∀ᶠ t in l,‖s t‖≤A t)
    (he : Tendsto (fun t => Rsc t*hugeCrossError (r t) (w t) a k (op t) (om t) (s t)) l (𝓝 0))
    (hd : Tendsto (fun t => Rsc t*δ t) l (𝓝 0))
    (ha : Tendsto (fun t => Rsc t*(A t)^2) l (𝓝 0)) :
    Tendsto (fun t => Rsc t*|(⟪actualProbeDirection (r t) (w t) a k,insertionInfinity (w t)⟫_ℂ).im|) l (𝓝 0) := by
  have hd0 := PacketGeometry.tendsto_of_scaled Rsc δ hR hδ hd
  have hb := ((he.const_mul 6).add ha).add (hd.mul (hd0.const_add 2))
  simp only [mul_zero,zero_mul,add_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards [hR] with t ht
    exact mul_nonneg (by linarith) (abs_nonneg _)
  · filter_upwards [hR,hδ,hA,hψ,hop,hom,hρ,hs] with t hRt hδt hAt hψt hopt homt hρt hst
    have ht := actual_huge_phase_modulus (r t) (w t) a k (op t) (om t) (s t) (ρ t)
      (δ t) (hugeCrossError (r t) (w t) a k (op t) (om t) (s t)) (A t)
      hδt hAt hψt hopt homt hρt hst
      (by apply le_of_sub_nonneg; dsimp only [hugeCrossError]; ring_nf; positivity)
      (by apply le_of_sub_nonneg; dsimp only [hugeCrossError]; ring_nf; positivity)
      (by apply le_of_sub_nonneg; dsimp only [hugeCrossError]; ring_nf; positivity)
      (by apply le_of_sub_nonneg; dsimp only [hugeCrossError]; ring_nf; positivity)
      (by apply le_of_sub_nonneg; dsimp only [hugeCrossError]; ring_nf; positivity)
    calc
      _ ≤ Rsc t*(6*hugeCrossError (r t) (w t) a k (op t) (om t) (s t)+(A t)^2+δ t*(2+δ t)) :=
        mul_le_mul_of_nonneg_left ht (by linarith)
      _ = _ := by ring

 

theorem rapid_actual_packet_sum_right {α ι : Type*} [Fintype ι] {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k K : ℕ) (hk : k≤K)
    (d : α → ModeInfinity) (e : ι → α → ModeInfinity)
    (x : α → PreSpin ModeInfinity) (y : ι → α → PreSpin ModeInfinity)
    (P : α → Matrix (Fin 2) (Fin 2) ℂ) (hR : Tendsto Rsc l atTop)
    (B A C δ T : ℝ) (hA : 0≤A) (hC : 0≤C) (hδ : 0<δ) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ t in l,|r t|≤1)
    (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hy : ∀j,∀ᶠ t in l,SpinRadiusLE (y j t) B ∧ spinMass (y j t)≤A)
    (hP : ∀ᶠ t in l,matrixMass (P t)≤C) (hsep : ∀j,∀ᶠ t in l,δ≤‖d t-e j t‖) :
    Tendsto (fun t => Rsc t*
      ‖⟪SpinOperators.act (P t) (probeGain (r t) (w t) a k (actualPacket (Rsc t) (d t) (x t))),
        probeGain (r t) (w t) a k (∑j,actualPacket (Rsc t) (e j t) (y j t))⟫_ℂ‖) l (𝓝 0) := by
  have h (j : ι) := rapid_decay_actual_packets r Rsc w a k K hk d (e j) x (y j) P hR
    B A C δ T hA hC hδ hT0 hT hr hx (hy j) hP (hsep j) 1
  simp only [pow_one] at h
  simpa only [actualPacket,map_sum,inner_sum] using PacketGeometry.scaled_norm_sum_tendsto Rsc
    (fun t j => ⟪SpinOperators.act (P t) (probeGain (r t) (w t) a k (actualPacket (Rsc t) (d t) (x t))),
      probeGain (r t) (w t) a k (actualPacket (Rsc t) (e j t) (y j t))⟫_ℂ)
    (hR.eventually (eventually_ge_atTop 0)) h

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace RootSpin
open CoherentFock

@[simp] theorem matrixMass_Z : matrixMass Z=2 := by
  norm_num [matrixMass,Z,Fin.sum_univ_two]

end RootSpin

namespace PointedTree
open CoherentFock RootSpin

 
theorem rapid_actual_packet_sum_left {α ι : Type*} [Fintype ι] {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k K : ℕ) (hk : k≤K)
    (d : ι → α → ModeInfinity) (e : α → ModeInfinity)
    (x : ι → α → PreSpin ModeInfinity) (y : α → PreSpin ModeInfinity)
    (P : α → Matrix (Fin 2) (Fin 2) ℂ) (hR : Tendsto Rsc l atTop)
    (B A C δ T : ℝ) (hA : 0≤A) (hC : 0≤C) (hδ : 0<δ) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ t in l,|r t|≤1)
    (hx : ∀j,∀ᶠ t in l,SpinRadiusLE (x j t) B ∧ spinMass (x j t)≤A)
    (hy : ∀ᶠ t in l,SpinRadiusLE (y t) B ∧ spinMass (y t)≤A)
    (hP : ∀ᶠ t in l,matrixMass (P t)≤C) (hsep : ∀j,∀ᶠ t in l,δ≤‖d j t-e t‖) :
    Tendsto (fun t => Rsc t*
      ‖⟪SpinOperators.act (P t) (probeGain (r t) (w t) a k (∑j,actualPacket (Rsc t) (d j t) (x j t))),
        probeGain (r t) (w t) a k (actualPacket (Rsc t) (e t) (y t))⟫_ℂ‖) l (𝓝 0) := by
  have h (j : ι) := rapid_decay_actual_packets r Rsc w a k K hk (d j) e (x j) y P hR
    B A C δ T hA hC hδ hT0 hT hr (hx j) hy hP (hsep j) 1
  simp only [pow_one] at h
  simpa only [actualPacket,map_sum,sum_inner] using PacketGeometry.scaled_norm_sum_tendsto Rsc
    (fun t j => ⟪SpinOperators.act (P t) (probeGain (r t) (w t) a k (actualPacket (Rsc t) (d j t) (x j t))),
      probeGain (r t) (w t) a k (actualPacket (Rsc t) (e t) (y t))⟫_ℂ)
    (hR.eventually (eventually_ge_atTop 0)) h

 

theorem hugeCrossError_packets_tendsto {α ι : Type*} [Fintype ι] {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k K : ℕ) (hk : k≤K)
    (dp dm : α → ModeInfinity) (ds : ι → α → ModeInfinity)
    (xp xm : α → PreSpin ModeInfinity) (xs : ι → α → PreSpin ModeInfinity)
    (hR : Tendsto Rsc l atTop) (B A δ T : ℝ) (hA : 0≤A) (hδ : 0<δ) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ t in l,|r t|≤1)
    (hxp : ∀ᶠ t in l,SpinRadiusLE (xp t) B ∧ spinMass (xp t)≤A)
    (hxm : ∀ᶠ t in l,SpinRadiusLE (xm t) B ∧ spinMass (xm t)≤A)
    (hxs : ∀j,∀ᶠ t in l,SpinRadiusLE (xs j t) B ∧ spinMass (xs j t)≤A)
    (hpm : ∀ᶠ t in l,δ≤‖dp t-dm t‖)
    (hps : ∀j,∀ᶠ t in l,δ≤‖dp t-ds j t‖)
    (hms : ∀j,∀ᶠ t in l,δ≤‖dm t-ds j t‖) :
    Tendsto (fun t => Rsc t*hugeCrossError (r t) (w t) a k
      (actualPacket (Rsc t) (dp t) (xp t)) (actualPacket (Rsc t) (dm t) (xm t))
      (∑j,actualPacket (Rsc t) (ds j t) (xs j t))) l (𝓝 0) := by
  let P := rotatedZ (a k).1
  let C := matrixMass P
  have hC : 0≤C := matrixMass_nonneg _
  have hP : ∀ᶠ t in l,matrixMass P≤C := Eventually.of_forall (fun _ => le_rfl)
  have hxp2 : ∀ᶠ t in l,SpinRadiusLE (xp t) B ∧ spinMass (xp t)≤2*A := by
    filter_upwards [hxp] with t ht
    exact ⟨ht.1,ht.2.trans (by linarith)⟩
  have hxm2 : ∀ᶠ t in l,SpinRadiusLE (xm t) B ∧ spinMass (xm t)≤2*A := by
    filter_upwards [hxm] with t ht
    exact ⟨ht.1,ht.2.trans (by linarith)⟩
  have hzs (j : ι) : ∀ᶠ t in l,SpinRadiusLE (preRoot Z (xs j t)) B ∧ spinMass (preRoot Z (xs j t))≤2*A := by
    filter_upwards [hxs j] with t ht
    exact ⟨ht.1.preRoot Z,(spinMass_preRoot Z _).trans (by rw [matrixMass_Z]; linarith [ht.2])⟩
  have hsp (j : ι) : ∀ᶠ t in l,δ≤‖ds j t-dp t‖ := by
    filter_upwards [hps j] with t ht
    exact ht.trans_eq (norm_sub_rev _ _)
  have hsm (j : ι) : ∀ᶠ t in l,δ≤‖ds j t-dm t‖ := by
    filter_upwards [hms j] with t ht
    exact ht.trans_eq (norm_sub_rev _ _)
  have h1 := rapid_decay_actual_packets r Rsc w a k K hk dp dm xp xm (fun _ => P) hR
    B A C δ T hA hC hδ hT0 hT hr hxp hxm hP hpm 1
  simp only [pow_one] at h1
  have h2 := rapid_actual_packet_sum_right r Rsc w a k K hk dp ds xp
    (fun j t => preRoot Z (xs j t)) (fun _ => P) hR B (2*A) C δ T (by positivity) hC hδ hT0 hT hr hxp2 hzs hP hps
  have h3 := rapid_actual_packet_sum_right r Rsc w a k K hk dm ds xm
    (fun j t => preRoot Z (xs j t)) (fun _ => P) hR B (2*A) C δ T (by positivity) hC hδ hT0 hT hr hxm2 hzs hP hms
  have h4 := rapid_actual_packet_sum_left r Rsc w a k K hk ds dp xs xp (fun _ => P) hR
    B A C δ T hA hC hδ hT0 hT hr hxs hxp hP hsp
  have h5 := rapid_actual_packet_sum_left r Rsc w a k K hk ds dm xs xm (fun _ => P) hR
    B A C δ T hA hC hδ hT0 hT hr hxs hxm hP hsm
  have h := (((h1.add h2).add h3).add h4).add h5
  simpa only [hugeCrossError,P,mul_add,map_sum,actualPacket_root,actualPacket,spinCoe_preRoot,spinW_root,zero_add] using h

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin

 

theorem actual_forward_tendsto {α : Type*} {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (phase : α → ℝ)
    (T B A : ℝ) (hT : 0≤T) (_hB : 0≤B) (_hA : 0≤A)
    (ha : ∀j<k,|(a j).2|≤T)
    (hr0 : Tendsto r l (𝓝 0)) (hp0 : Tendsto phase l (𝓝 0))
    (hpnonneg : ∀ᶠ t in l,0≤phase t)
    (hphase : ∀ᶠ t in l,∀j<k,|(-2*(⟪actualDisplacement (r t) (w t) a j,e t⟫_ℂ).im)|≤phase t)
    (hx : ∀ᶠ t in l,spinBound (x t)≤B ∧ ‖spinCoe (x t)‖≤A) :
    Tendsto (fun t => ‖probeGain (r t) (w t) a k (spinW (e t) (spinCoe (x t)))-
      spinW (e t) (spinCoe (x t))‖) l (𝓝 0) := by
  have habs : Tendsto (fun t => |r t|) l (𝓝 0) := by simpa only [abs_zero] using hr0.abs
  have hlim := ((((((habs.mul_const T).pow 2).add (habs.mul_const T)).mul_const 4).mul_const (k:ℝ)).mul_const ((4^2:ℝ)^k)).mul_const B
  have hlim' := hlim.add ((hp0.const_mul (k:ℝ)).mul_const A)
  simp only [zero_mul,zero_pow (by decide : 2≠0),add_zero,mul_zero] at hlim'
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim'
  filter_upwards [hpnonneg,hphase,hx] with t hpt hphaset hxt
  apply (actual_forward_bound (r t) (w t) a k (e t) (x t) T (phase t) hT hpt ha hphaset).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hxt.1 (by positivity))
    (mul_le_mul_of_nonneg_left hxt.2 (by positivity))

 

theorem actual_zero_clock_tendsto {α : Type*} {l : Filter α}
    (r Rsc : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (Δ phase : α → ℝ)
    (T B A : ℝ) (hT : 0≤T) (_hB : 0≤B) (_hA : 0≤A)
    (ha : ∀j<k,|(a j).2|≤T)
    (hr0 : Tendsto r l (𝓝 0)) (hΔ0 : Tendsto Δ l (𝓝 0))
    (hp0 : Tendsto (fun t => Rsc t*phase t) l (𝓝 0))
    (hscale : ∀ᶠ t in l,0≤r t ∧ 0≤Rsc t ∧ Rsc t*r t=1)
    (hnonneg : ∀ᶠ t in l,0≤Δ t ∧ 0≤phase t)
    (hd : ∀ᶠ t in l,∀j<k,‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖≤Δ t)
    (hp : ∀ᶠ t in l,∀j<k,|(-2*(⟪actualDisplacement (r t) (w t) a j,e t⟫_ℂ).im)|≤phase t)
    (hx : ∀ᶠ t in l,spinBound (x t)≤B ∧ ‖spinCoe (x t)‖≤A)
    (hclock : ∀ᶠ t in l,((List.range k).reverse.map (fun j => Complex.I •
      probeField (R (a j).1) (startingVelocity (w t) a j) (x t))).sum=0) :
    Tendsto (fun t => Rsc t*‖probeGain (r t) (w t) a k (spinW (e t) (spinCoe (x t)))-
      spinW (e t) (spinCoe (x t))‖) l (𝓝 0) := by
  have h1 := (((hr0.mul_const (T^2)).add (hΔ0.const_mul T)).mul_const (4*B)).const_mul (k:ℝ)
  have h2 := (hr0.mul_const (2*T^2*4^3*B)).const_mul ((k:ℝ)^2)
  have h3 := (hp0.mul_const A).const_mul (k:ℝ)
  have hl := (h1.add h2).add h3
  simp only [zero_mul,mul_zero,add_zero] at hl
  apply squeeze_zero' _ _ hl
  · filter_upwards [hscale] with t ht
    exact mul_nonneg ht.2.1 (norm_nonneg _)
  · filter_upwards [hscale,hnonneg,hd,hp,hx,hclock] with t ht hnt hdt hpt hxt hct
    have h := actual_zero_clock_bound (r t) (w t) a k (e t) (x t) T (Δ t) (phase t)
      hT hnt.1 hnt.2 ha hdt hpt hct
    have hb : ‖probeGain (r t) (w t) a k (spinW (e t) (spinCoe (x t)))-
        spinW (e t) (spinCoe (x t))‖≤
        k*((r t^2*T^2+|r t| *(T*Δ t))*4*B)+
        (k:ℝ)^2*|r t| *(2*|r t| *T^2*4^3*B)+k*phase t*A := by
      apply h.trans
      have hΔt := hnt.1
      have hphaset := hnt.2
      have hBt := hxt.1
      have hAt := hxt.2
      gcongr
    apply (mul_le_mul_of_nonneg_left hb ht.2.1).trans_eq
    rw [abs_of_nonneg ht.1]
    calc
      _ = (Rsc t*r t)*((k:ℝ)*(r t*T^2+T*Δ t)*(4*B)+(k:ℝ)^2*(r t*(2*T^2*4^3*B)))+
          (k:ℝ)*(Rsc t*phase t*A) := by ring
      _ = _ := by rw [ht.2.2,one_mul]; ring

end PointedTree

end

end OAI
