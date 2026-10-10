import Mathlib
import OAI.Probability.ParisiFinite.IdentityErrorFinSumTendsto

namespace OAI

/-! Actual Center Phase. -/

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
local instance phaseRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance phaseRealSMul : SMul ℝ ModeInfinity := phaseRealModule.toDistribMulAction.toSMul

 
theorem actual_center_phase (r S : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) (d : ModeInfinity) :
    -2*(⟪actualDisplacement r w a k,S • d⟫_ℂ).im=
      2*r*S*(a k).2*(⟪actualProbeDirection r w a k,d⟫_ℂ).im := by
  exact short_large_phase r S (a k).2 _ d

 

theorem scaled_huge_center_phase {α : Type*} {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ) (t : ℝ)
    (hscale : ∀ᶠ q in l,r q*S q=1)
    (hsmall : Tendsto (fun q => S q*|(⟪actualProbeDirection (r q) (w q) a k,insertionInfinity (w q)⟫_ℂ).im|) l (𝓝 0)) :
    Tendsto (fun q => S q*|(-2*(⟪actualDisplacement (r q) (w q) a k,
      S q • (t • insertionInfinity (w q))⟫_ℂ).im)|) l (𝓝 0) := by
  have h := hsmall.mul_const |2*(a k).2*t|
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [hscale] with q hq
  rw [actual_center_phase]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) t (insertionInfinity (w q)),inner_smul_real_right,
    Complex.smul_im,smul_eq_mul]
  have he : 2*r q*S q*(a k).2*(t*(⟪actualProbeDirection (r q) (w q) a k,insertionInfinity (w q)⟫_ℂ).im)=
      (2*(a k).2*t)*(⟪actualProbeDirection (r q) (w q) a k,insertionInfinity (w q)⟫_ℂ).im := by
    calc
      _ = (r q*S q)*((2*(a k).2*t)*(⟪actualProbeDirection (r q) (w q) a k,insertionInfinity (w q)⟫_ℂ).im) := by ring
      _ = _ := by rw [hq,one_mul]
  simp only [he,abs_mul]
  ring

 

theorem actual_special_phase_tendsto {α : Type*} {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (d : α → ModeInfinity) (C c : ℝ) (_hC : 0≤C)
    (hscale : ∀ᶠ q in l,r q*S q=1) (hd : ∀ᶠ q in l,‖d q‖≤C)
    (hchange : Tendsto (fun q => ‖actualProbeDirection (r q) (w q) a k-
      insertionInfinity (.mixer (a k).1::w q)‖) l (𝓝 0))
    (hstart : Tendsto (fun q => (⟪insertionInfinity (.mixer (a k).1::w q),d q⟫_ℂ).im) l (𝓝 c)) :
    Tendsto (fun q => -2*(⟪actualDisplacement (r q) (w q) a k,S q • d q⟫_ℂ).im)
      l (𝓝 (2*(a k).2*c)) := by
  have hdiff : Tendsto (fun q => (⟪actualProbeDirection (r q) (w q) a k,d q⟫_ℂ).im-
      (⟪insertionInfinity (.mixer (a k).1::w q),d q⟫_ℂ).im) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlo := hchange.mul_const C
    simp only [zero_mul] at hlo
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlo
    filter_upwards [hd] with q hq
    exact (imaginary_projection_difference _ _ _).trans
      (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
  have hsum := hdiff.add hstart
  simp only [sub_add_cancel,zero_add] at hsum
  have h := hsum.const_mul (2*(a k).2)
  apply h.congr'
  filter_upwards [hscale] with q hq
  rw [actual_center_phase]
  symm
  calc
    _ = (r q*S q)*((2*(a k).2)*(⟪actualProbeDirection (r q) (w q) a k,d q⟫_ℂ).im) := by ring
    _ = _ := by rw [hq,one_mul]

end PointedTree

 

open scoped InnerProductSpace Topology
open Filter
namespace PointedTree
open CoherentFock RootSpin

 

theorem rotated_imaginary (w : List Gate) (β : ℝ) (d : ModeInfinity) :
    -2*(⟪insertionInfinity (.mixer β::w),d⟫_ℂ).im=
      Real.cos (2*β)*(-2*(⟪insertionInfinity w,d⟫_ℂ).im)+
        Real.sin (2*β)*(-2*(⟪insertionYInfinity w,d⟫_ℂ).im) := by
  rw [rotated_insertion_eq,inner_add_left,inner_smul_left,inner_smul_left]
  simp only [Complex.add_im,Complex.conj_ofReal,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  ring

 

theorem rotated_projection_tendsto {α : Type*} {l : Filter α}
    (w : α → List Gate) (d : α → ModeInfinity) (v : ℝ×ℝ) (β : ℝ)
    (hZ : Tendsto (fun t => -2*(⟪insertionInfinity (w t),d t⟫_ℂ).im) l (𝓝 v.1))
    (hY : Tendsto (fun t => -2*(⟪insertionYInfinity (w t),d t⟫_ℂ).im) l (𝓝 v.2)) :
    Tendsto (fun t => (⟪insertionInfinity (.mixer β::w t),d t⟫_ℂ).im) l
      (𝓝 (-(Real.cos (2*β)*v.1+Real.sin (2*β)*v.2)/2)) := by
  have h := ((hZ.const_mul (Real.cos (2*β))).add (hY.const_mul (Real.sin (2*β)))).mul_const (-1/2)
  convert! h using 1
  · ext t
    have he := rotated_imaginary (w t) β (d t)
    linarith
  · congr 1
    ring

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin

 

theorem actual_special_packet_tendsto {α : Type*} {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (e : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (φ : ℕ → ℝ)
    (T B A : ℝ) (hT : 0≤T) (_hB : 0≤B) (_hA : 0≤A)
    (ha : ∀j<k,|(a j).2|≤T) (hr0 : Tendsto r l (𝓝 0))
    (hphase : ∀j<k,Tendsto (fun t => -2*(⟪actualDisplacement (r t) (w t) a j,e t⟫_ℂ).im) l (𝓝 (φ j)))
    (hx : ∀ᶠ t in l,spinBound (x t)≤B ∧ ‖spinCoe (x t)‖≤A) :
    Tendsto (fun t => ‖spinW (-e t) (probeGain (r t) (w t) a k (spinW (e t) (spinCoe (x t))))-
      ProbeProduct.act (fun j => probePhase (R (a j).1) (φ j)) (List.range k).reverse (spinCoe (x t))‖) l (𝓝 0) := by
  let err (t : α) (j : ℕ) := (-2*(⟪actualDisplacement (r t) (w t) a j,e t⟫_ℂ).im)-φ j
  let η (t : α) := FiniteError.envelope k (err t)
  have hη : Tendsto η l (𝓝 0) := FiniteError.envelope_tendsto_zero k err (by
    intro j hj
    simpa only [sub_self] using (hphase j hj).sub_const (φ j))
  have habs : Tendsto (fun t => |r t|) l (𝓝 0) := by simpa only [abs_zero] using hr0.abs
  have hlim := ((((((habs.mul_const T).pow 2).add (habs.mul_const T)).mul_const 4).mul_const (k:ℝ)).mul_const ((4^2:ℝ)^k)).mul_const B
  have hlim' := hlim.add ((hη.const_mul (k:ℝ)).mul_const A)
  simp only [zero_mul,zero_pow (by decide : 2≠0),add_zero,mul_zero] at hlim'
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim'
  filter_upwards [hx] with t hxt
  rw [probeGain_product]
  have hb := special_product_bound (List.range k).reverse (fun j => R (a j).1)
    (actualDisplacement (r t) (w t) a) (e t) φ (|r t| *T) 4 (η t)
    (by positivity) (by norm_num) (FiniteError.envelope_nonneg ..)
    (fun j _ => R_unitary _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj
        rw [norm_actualDisplacement]; exact mul_le_mul_of_nonneg_left (ha j hj) (abs_nonneg _))
    (fun j _ => matrixMass_R_le _) (fun j _ => by rw [R_star]; exact matrixMass_R_le _)
    (by intro j hj; rw [List.mem_reverse,List.mem_range] at hj; exact FiniteError.le_envelope k (err t) j hj) (x t)
  have hf : (fun j => probe (R (a j).1) (actualDisplacement (r t) (w t) a j))=actualProbe (r t) (w t) a := by
    funext j; rfl
  rw [hf] at hb
  simp only [List.length_reverse,List.length_range] at hb
  apply hb.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hxt.1 (by positivity))
    (mul_le_mul_of_nonneg_left hxt.2 (mul_nonneg (Nat.cast_nonneg _) (FiniteError.envelope_nonneg ..)))

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance selectRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance selectRealSMul : SMul ℝ ModeInfinity := selectRealModule.toDistribMulAction.toSMul

 

theorem actual_rotation_on_special {α : Type*} {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (d : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (v : ℝ×ℝ) (θ : ℝ)
    (C T B A : ℝ) (hC : 0≤C) (hT : 0≤T) (hB : 0≤B) (hA : 0≤A)
    (ha : ∀j<K,|(a j).2|≤T) (hr : Tendsto r l (𝓝 0))
    (hscale : ∀ᶠ t in l,r t*S t=1) (hd : ∀ᶠ t in l,‖d t‖≤C)
    (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hchange : ∀j<K,Tendsto (fun t => ‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖) l (𝓝 0))
    (hZ : Tendsto (fun t => -2*(⟪insertionInfinity (w t),d t⟫_ℂ).im) l (𝓝 v.1))
    (hY : Tendsto (fun t => -2*(⟪insertionYInfinity (w t),d t⟫_ℂ).im) l (𝓝 v.2))
    (hprod : ProbeProduct.act (fun j => probePhase (E:=ModeInfinity) (R (a j).1)
      (projectionPhase v (a j))) (List.range K).reverse=SpinOperators.act (R θ)) :
    Tendsto (fun t => ‖spinW (-(S t • d t))
      (probeGain (r t) (w t) a K (actualPacket (S t) (d t) (x t)))-
        SpinOperators.act (R θ) (spinCoe (x t))‖) l (𝓝 0) := by
  have hp : ∀j<K,Tendsto (fun t => -2*(⟪actualDisplacement (r t) (w t) a j,S t • d t⟫_ℂ).im)
      l (𝓝 (projectionPhase v (a j))) := by
    intro j hj
    have h := actual_special_phase_tendsto r S w a j d C
      (-(Real.cos (2*(a j).1)*v.1+Real.sin (2*(a j).1)*v.2)/2)
      hC hscale hd (hchange j hj) (rotated_projection_tendsto w d v (a j).1 hZ hY)
    convert! h using 1
    congr 1
    dsimp only [projectionPhase]
    ring
  have hx' : ∀ᶠ t in l,spinBound (x t)≤A*(1+2*B+12*B^2) ∧ ‖spinCoe (x t)‖≤A := by
    filter_upwards [hx] with t ht
    exact tail_bounds_of_radius_mass (x t) B A hB ht
  have h := actual_special_packet_tendsto r w a K (fun t => S t • d t) x
    (fun j => projectionPhase v (a j)) T (A*(1+2*B+12*B^2)) A hT (by positivity) hA
    ha hr hp hx'
  simpa only [hprod,actualPacket] using h

 

theorem selective_packet_accuracy {α ι κ : Type*} [Fintype ι] [Fintype κ] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate)
    (d : ι → α → ModeInfinity) (x : ι → α → PreSpin ModeInfinity)
    (s ρ : α → SpinSpace ModeInfinity) (B A : ℝ) (hB : 0≤B) (hA : 0≤A)
    (v : κ → ℝ×ℝ) (hv : ∀i,v i≠0) (θ : ℝ)
    (hr : Tendsto r l (𝓝 0)) (hS : ∀ᶠ t in l,1≤S t)
    (hscale : ∀ᶠ t in l,0≤r t ∧ 0≤S t ∧ S t*r t=1)
    (hx : ∀i,∀ᶠ t in l,SpinRadiusLE (x i t) B ∧ spinMass (x i t)≤A)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      (∑i,actualPacket (S t) (d i t) (x i t))+s t+ρ t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (T : ℝ),0≤T ∧ (∀j<K,|(a j).2|≤T) ∧
      ((∀i,∀j<K,Tendsto (fun t => S t*|-2*(⟪actualDisplacement (r t) (w t) a j,S t • d i t⟫_ℂ).im|) l (𝓝 0)) →
        (∀ (e : α → ModeInfinity) (z : α → PreSpin ModeInfinity) (B' A' : ℝ),0≤B' → 0≤A' →
          (∀ᶠ t in l,SpinRadiusLE (z t) B' ∧ spinMass (z t)≤A') →
          (∀j<K,Tendsto (fun t => S t*|-2*(⟪actualDisplacement (r t) (w t) a j,S t • e t⟫_ℂ).im|) l (𝓝 0)) →
          Tendsto (fun t => S t*‖probeGain (r t) (w t) a K (actualPacket (S t) (e t) (z t))-
            actualPacket (S t) (e t) (z t)‖) l (𝓝 0)) ∧
        (∀ (i : κ) (e : α → ModeInfinity) (z : α → PreSpin ModeInfinity) (C B' A' : ℝ),
          0≤C → 0≤B' → 0≤A' → (∀ᶠ t in l,‖e t‖≤C) →
          (∀ᶠ t in l,SpinRadiusLE (z t) B' ∧ spinMass (z t)≤A') →
          Tendsto (fun t => -2*(⟪insertionInfinity (w t),e t⟫_ℂ).im) l (𝓝 (v i).1) →
          Tendsto (fun t => -2*(⟪insertionYInfinity (w t),e t⟫_ℂ).im) l (𝓝 (v i).2) →
          Tendsto (fun t => ‖spinW (-(S t • e t))
            (probeGain (r t) (w t) a K (actualPacket (S t) (e t) (z t)))-
              SpinOperators.act (R θ) (spinCoe (z t))‖) l (𝓝 0))) := by
  obtain ⟨K,a,T,hT,ha,hclock,hprod⟩ := selective_phase_control v hv θ
  refine ⟨K,a,T,hT,ha,?_⟩
  intro hp
  have hΔ := packet_direction_envelope_tendsto r S w a K d x s ρ B A T hB hA hT ha hr hS hx hp hψ hs hρ
  have hc : ∀j<K,Tendsto (fun t => ‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖) l (𝓝 0) := by
    intro j hj
    apply squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hΔ
    simpa only [abs_norm] using FiniteError.le_envelope K
      (fun j => ‖actualProbeDirection (r t) (w t) a j-insertionInfinity (.mixer (a j).1::w t)‖) j hj
  constructor
  · intro e z B' A' hB' hA' hz he
    exact packet_zero_clock_from_vacuum r S w a K d x s ρ B A T hB hA hT ha hr hS
      hscale hx hp hψ hs hρ e z B' A' hB' hA' hz he
      (Eventually.of_forall (fun t => hclock (w t) (z t)))
  · intro i e z C B' A' hC hB' hA' he hz hZ hY
    exact actual_rotation_on_special r S w a K e z (v i) θ C T B' A' hC hT hB' hA'
      ha hr (hscale.mono (fun t ht => by rw [mul_comm]; exact ht.2.2)) he hz hc hZ hY (hprod i)

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem spinW_neg_cancel (d : E) (x : SpinSpace E) : spinW (-d) (spinW d x)=x := by
  ext i
  simp only [spinW_apply]
  exact W_neg_cancel_left d (x i)

 

theorem centered_rotation_error (d : E) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (V : SpinSpace E →ₗ[ℂ] SpinSpace E) (x : SpinSpace E) :
    ‖spinW (-d) (V (spinW d x))-SpinOperators.act A x‖=
      ‖V (spinW d x)-SpinOperators.act A (spinW d x)‖ := by
  rw [←spinW_neg_cancel d (SpinOperators.act A x),spinW_root d A x,
    ←map_sub,norm_spinW]

end CoherentFock

namespace ForwardControl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem difference_sum_remainder_bound {ι : Type*} [Fintype ι]
    (V : H ≃ₗᵢ[ℂ] H) (F : H →L[ℂ] H) (hF : ∀x,‖F x‖≤‖x‖)
    (x : ι → H) (ρ : H) :
    ‖V ((∑i,x i)+ρ)-F ((∑i,x i)+ρ)‖≤(∑i,‖V (x i)-F (x i)‖)+2*‖ρ‖ := by
  have he : V ((∑i,x i)+ρ)-F ((∑i,x i)+ρ)=
      (∑i,(V (x i)-F (x i)))+(V ρ-F ρ) := by
    simp only [map_add,map_sum,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_sum_le _ _)
  calc
    _ ≤ ‖V ρ‖+‖F ρ‖ := norm_sub_le _ _
    _ ≤ ‖ρ‖+‖ρ‖ := add_le_add (V.norm_map _).le (hF _)
    _ = _ := by ring

 

theorem scaled_difference_finSum_tendsto {α ι : Type*} [Fintype ι] {l : Filter α}
    (V : α → H ≃ₗᵢ[ℂ] H) (F : H →L[ℂ] H) (hF : ∀x,‖F x‖≤‖x‖)
    (S : α → ℝ) (x : α → ι → H) (ρ : α → H)
    (hS : ∀ᶠ t in l,0≤S t)
    (hx : ∀i,Tendsto (fun t => S t*‖V t (x t i)-F (x t i)‖) l (𝓝 0))
    (hρ : Tendsto (fun t => S t*‖ρ t‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t ((∑i,x t i)+ρ t)-F ((∑i,x t i)+ρ t)‖) l (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hx i)
  simp only [Finset.sum_const_zero] at hsum
  have h := hsum.add (hρ.mul_const 2)
  simp only [zero_mul,add_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [hS] with t ht
    exact mul_nonneg ht (norm_nonneg _)
  · filter_upwards [hS] with t ht
    have hb := mul_le_mul_of_nonneg_left (difference_sum_remainder_bound (V t) F hF (x t) (ρ t)) ht
    simpa only [mul_add,Finset.mul_sum,mul_left_comm (S t) 2,mul_comm 2 (S t*‖ρ t‖)] using hb

 
theorem scaled_amplitude_error {α : Type*} {l : Filter α}
    (V : α → H ≃ₗᵢ[ℂ] H) (F : H →L[ℂ] H) (r S : α → ℝ) (x : α → H)
    (hscale : ∀ᶠ t in l,0≤r t ∧ S t*r t=1)
    (hx : Tendsto (fun t => ‖V t (x t)-F (x t)‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t ((r t:ℂ) • x t)-F ((r t:ℂ) • x t)‖) l (𝓝 0) := by
  apply hx.congr'
  filter_upwards [hscale] with t ht
  simp only [map_smul,←smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht.1,←mul_assoc,ht.2,one_mul]

end ForwardControl

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

 

theorem scaled_special_transport (U V : α → H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x,‖Z x‖≤‖x‖) (hanti : ∀x,Z (F x)= -F (Z x))
    (s w : α → H) (S : α → ℝ) (hS : ∀ᶠ t in l,0≤S t)
    (h1 : Tendsto (fun t => S t*‖V t (s t)-F (s t)‖) l (𝓝 0))
    (h2 : Tendsto (fun t => S t*‖V t (Z (s t))-F (Z (s t))‖) l (𝓝 0))
    (ht : Tendsto (fun t => ‖(S t:ℂ) • (U t).symm (Z (s t))-w t‖) l (𝓝 0)) :
    Tendsto (fun t => ‖(S t:ℂ) • (U t).symm ((V t).symm (Z (V t (s t))))+w t‖) l (𝓝 0) := by
  have he : Tendsto (fun t => S t*‖(V t).symm (Z (V t (s t)))+Z (s t)‖) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [add_zero] using h1.add h2)
    · filter_upwards [hS] with t hst
      exact mul_nonneg hst (norm_nonneg _)
    · filter_upwards [hS] with t hst
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (special_transport_bound (V t) Z F hZ hanti (s t)) hst
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [add_zero] using he.add ht)
  filter_upwards [hS] with t hst
  have heq : (S t:ℂ) • (U t).symm ((V t).symm (Z (V t (s t))))+w t=
      (S t:ℂ) • (U t).symm ((V t).symm (Z (V t (s t)))+Z (s t))-
        ((S t:ℂ) • (U t).symm (Z (s t))-w t) := by
    simp only [map_add,smul_add]
    abel
  rw [heq]
  apply (norm_sub_le _ _).trans
  rw [norm_smul,(U t).symm.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hst]

end ForwardControl

namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 

theorem scaled_echo_ordinary (t : ℝ) (r S : α → ℝ) (v v' : α → E)
    (V₁ V₂ : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E) (x : α → SpinSpace E)
    (hS : ∀ᶠ q in l,0≤S q)
    (h1 : Tendsto (fun q => S q*‖V₁ q (WZ (-(t/r q) • v q) (x q))-
      WZ (-(t/r q) • v q) (x q)‖) l (𝓝 0))
    (h2 : Tendsto (fun q => S q*‖V₂ q (WZ ((t/r q) • v' q)
      (V₁ q (WZ (-(t/r q) • v q) (x q))))-
      WZ ((t/r q) • v' q) (V₁ q (WZ (-(t/r q) • v q) (x q)))‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖(phase ((t/r q) • v' q) (-(t/r q) • v q))⁻¹ •
      V₂ q (WZ ((t/r q) • v' q) (V₁ q (WZ (-(t/r q) • v q) (x q))))-
      WZ ((t/r q) • (v' q-v q)) (x q)‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [add_zero] using h1.add h2)
  · filter_upwards [hS] with q hq
    exact mul_nonneg hq (norm_nonneg _)
  · filter_upwards [hS] with q hq
    simpa only [mul_add] using mul_le_mul_of_nonneg_left
      (echo_ordinary_error t (r q) (v q) (v' q) (V₁ q) (V₂ q) (x q)) hq

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance wordRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance wordRealSMul : SMul ℝ ModeInfinity := wordRealModule.toDistribMulAction.toSMul

 
def wordGain (w u : List Gate) : SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  (ordinaryLocal w).symm.trans (ordinaryLocal u)

@[simp] theorem wordGain_apply (w u : List Gate) (x : SpinSpace ModeInfinity) :
    wordGain w u x=ordinaryLocal u ((ordinaryLocal w).symm x) := rfl

 

def echoWord (t r : ℝ) (w : List Gate) (a b : ℕ → ShortPulse) (K L : ℕ) : List Gate :=
  probePrefix r (.cost (-(t/r))::probePrefix r (.cost (t/r)::w) a K) b L

@[simp] theorem probeGain_on_local (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (x : SpinSpace ModeInfinity) :
    probeGain r w a K (ordinaryLocal w x)=ordinaryLocal (probePrefix r w a K) x := by
  simp only [probeGain_apply,LinearIsometryEquiv.symm_apply_apply]

 

theorem wordGain_echo (t r : ℝ) (w : List Gate) (a b : ℕ → ShortPulse) (K L : ℕ)
    (x : SpinSpace ModeInfinity) :
    wordGain w (echoWord t r w a b K L) x=
      probeGain r (.cost (-(t/r))::probePrefix r (.cost (t/r)::w) a K) b L
        (WZ ((t/r) • insertionInfinity (probePrefix r (.cost (t/r)::w) a K))
          (probeGain r (.cost (t/r)::w) a K
            (WZ (-(t/r) • insertionInfinity w) x))) := by
  rw [wordGain_apply,echoWord,←probeGain_on_local]
  rw [ordinaryLocal_cost,←probeGain_on_local,ordinaryLocal_cost]
  simp only [LinearIsometryEquiv.apply_symm_apply,Complex.ofReal_neg,neg_neg]
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.ofReal_neg]
  rfl

 
theorem actual_echo_ordinary_scaled {α : Type*} {l : Filter α}
    (t : ℝ) (r S : α → ℝ) (w : α → List Gate) (a b : ℕ → ShortPulse) (K L : ℕ)
    (x : α → SpinSpace ModeInfinity) (hS : ∀ᶠ q in l,0≤S q)
    (h1 : Tendsto (fun q => S q*‖probeGain (r q) (.cost (t/r q)::w q) a K
      (WZ (-(t/r q) • insertionInfinity (w q)) (x q))-
      WZ (-(t/r q) • insertionInfinity (w q)) (x q)‖) l (𝓝 0))
    (h2 : Tendsto (fun q => S q*‖probeGain (r q)
      (.cost (-(t/r q))::probePrefix (r q) (.cost (t/r q)::w q) a K) b L
      (WZ ((t/r q) • insertionInfinity (probePrefix (r q) (.cost (t/r q)::w q) a K))
        (probeGain (r q) (.cost (t/r q)::w q) a K
          (WZ (-(t/r q) • insertionInfinity (w q)) (x q))))-
      WZ ((t/r q) • insertionInfinity (probePrefix (r q) (.cost (t/r q)::w q) a K))
        (probeGain (r q) (.cost (t/r q)::w q) a K
          (WZ (-(t/r q) • insertionInfinity (w q)) (x q)))‖) l (𝓝 0)) :
    Tendsto (fun q => S q*‖(phase
      ((t/r q) • insertionInfinity (probePrefix (r q) (.cost (t/r q)::w q) a K))
      (-(t/r q) • insertionInfinity (w q)))⁻¹ •
      wordGain (w q) (echoWord t (r q) (w q) a b K L) (x q)-
      WZ ((t/r q) • (insertionInfinity (probePrefix (r q) (.cost (t/r q)::w q) a K)-
        insertionInfinity (w q))) (x q)‖) l (𝓝 0) := by
  simp_rw [wordGain_echo]
  exact scaled_echo_ordinary t r S (fun q => insertionInfinity (w q))
    (fun q => insertionInfinity (probePrefix (r q) (.cost (t/r q)::w q) a K))
    (fun q => probeGain (r q) (.cost (t/r q)::w q) a K)
    (fun q => probeGain (r q)
      (.cost (-(t/r q))::probePrefix (r q) (.cost (t/r q)::w q) a K) b L)
    x hS h1 h2

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PacketGeometry

 

theorem norm_tendsto_of_scaled_square {α H : Type*} [SeminormedAddCommGroup H]
    {l : Filter α} (S : α → ℝ) (x : α → H) (hS : ∀ᶠ t in l,1≤S t)
    (hx : Tendsto (fun t => S t*‖x t‖^2) l (𝓝 0)) :
    Tendsto (fun t => ‖x t‖) l (𝓝 0) := by
  have h2 := tendsto_of_scaled S (fun t => ‖x t‖^2) hS
    (Eventually.of_forall (fun _ => sq_nonneg _)) hx
  have h := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end PacketGeometry

namespace PointedTree
open CoherentFock RootSpin

 

theorem actual_huge_packet_phase {α ι : Type*} [Fintype ι] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k K : ℕ) (hk : k≤K)
    (dp dm : α → ModeInfinity) (ds : ι → α → ModeInfinity)
    (xp xm : α → PreSpin ModeInfinity) (xs : ι → α → PreSpin ModeInfinity)
    (ρ : α → SpinSpace ModeInfinity)
    (hS : Tendsto S l atTop) (B A δ T : ℝ) (hA : 0≤A) (hδ : 0<δ) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ t in l,|r t|≤1)
    (hxp : ∀ᶠ t in l,SpinRadiusLE (xp t) B ∧ spinMass (xp t)≤A)
    (hxm : ∀ᶠ t in l,SpinRadiusLE (xm t) B ∧ spinMass (xm t)≤A)
    (hxs : ∀j,∀ᶠ t in l,SpinRadiusLE (xs j t) B ∧ spinMass (xs j t)≤A)
    (hpm : ∀ᶠ t in l,δ≤‖dp t-dm t‖)
    (hps : ∀j,∀ᶠ t in l,δ≤‖dp t-ds j t‖)
    (hms : ∀j,∀ᶠ t in l,δ≤‖dm t-ds j t‖)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      actualPacket (S t) (dp t) (xp t)+actualPacket (S t) (dm t) (xm t)+
      (∑j,actualPacket (S t) (ds j t) (xs j t))+ρ t)
    (hop : ∀ᶠ t in l,SpinOperators.act Z (actualPacket (S t) (dp t) (xp t))=actualPacket (S t) (dp t) (xp t))
    (hom : ∀ᶠ t in l,SpinOperators.act Z (actualPacket (S t) (dm t) (xm t))= -actualPacket (S t) (dm t) (xm t))
    (hρ : Tendsto (fun t => S t*‖ρ t‖) l (𝓝 0))
    (hs : Tendsto (fun t => S t*‖∑j,actualPacket (S t) (ds j t) (xs j t)‖^2) l (𝓝 0)) :
    Tendsto (fun t => S t*|(⟪actualProbeDirection (r t) (w t) a k,insertionInfinity (w t)⟫_ℂ).im|) l (𝓝 0) := by
  have he := hugeCrossError_packets_tendsto r S w a k K hk dp dm ds xp xm xs hS
    B A δ T hA hδ hT0 hT hr hxp hxm hxs hpm hps hms
  exact actual_huge_phase_tendsto r S w a k
    (fun t => actualPacket (S t) (dp t) (xp t))
    (fun t => actualPacket (S t) (dm t) (xm t))
    (fun t => ∑j,actualPacket (S t) (ds j t) (xs j t)) ρ
    (fun t => ‖ρ t‖) (fun t => ‖∑j,actualPacket (S t) (ds j t) (xs j t)‖)
    (hS.eventually (eventually_ge_atTop 1))
    (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun _ => norm_nonneg _))
    hψ hop hom (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) he hρ hs

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PacketGeometry

lemma finite_positive_floor {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀i,0<c i) :
    ∃ δ : ℝ,0<δ ∧ ∀i,δ≤c i := by
  classical
  have h : ∀s : Finset ι,∃ δ : ℝ,0<δ ∧ ∀i∈s,δ≤c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨δ,hδ,hd⟩ := ih
      refine ⟨min δ (c i),lt_min hδ (hc i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hd j hj)
  simpa only [Finset.mem_univ,true_implies] using h Finset.univ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 

lemma imaginary_real_multiple (v : E) (a : ℝ) : (⟪v,a • v⟫_ℂ).im=0 := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),inner_smul_real_right]
  rw [Complex.smul_im]
  change a • RCLike.im (inner ℂ v v)=0
  rw [inner_self_im,smul_zero]

lemma projection_separation_bound (v d : E) (a : ℝ) (hv : ‖v‖≤1) :
    |(⟪v,d⟫_ℂ).im|≤‖a • v-d‖ := by
  have he : (⟪v,a • v-d⟫_ℂ).im= -(⟪v,d⟫_ℂ).im := by
    rw [inner_sub_right,Complex.sub_im,imaginary_real_multiple,zero_sub]
  calc
    _ = |(⟪v,a • v-d⟫_ℂ).im| := by rw [he,abs_neg]
    _ ≤ ‖⟪v,a • v-d⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖v‖*‖a • v-d‖ := norm_inner_le_norm _ _
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hv (norm_nonneg (a • v-d))

 

theorem finite_projection_separation {α ι : Type*} [Fintype ι] {l : Filter α}
    (v : α → E) (d : ι → α → E) (c : ι → ℝ) (a b : ℝ)
    (hc : ∀i,c i≠0) (hv : ∀ᶠ t in l,‖v t‖≤1)
    (hp : ∀i,Tendsto (fun t => (⟪v t,d i t⟫_ℂ).im) l (𝓝 (c i))) :
    ∃ δ : ℝ,0<δ ∧ (∀i,∀ᶠ t in l,δ≤‖a • v t-d i t‖) ∧
      (∀i,∀ᶠ t in l,δ≤‖b • v t-d i t‖) := by
  obtain ⟨δ,hδ,hd⟩ := finite_positive_floor (fun i => |c i|/2)
    (fun i => half_pos (abs_pos.mpr (hc i)))
  have h (q : ℝ) (i : ι) : ∀ᶠ t in l,δ≤‖q • v t-d i t‖ := by
    have hp' := (hp i).abs.eventually (eventually_gt_nhds (half_lt_self (abs_pos.mpr (hc i))))
    filter_upwards [hv,hp'] with t hvt hpt
    exact (hd i).trans (hpt.le.trans (projection_separation_bound (v t) (d i t) q hvt))
  exact ⟨δ,hδ,h a,h b⟩

end PacketGeometry

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance hugeRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance hugeRealSMul : SMul ℝ ModeInfinity := hugeRealModule.toDistribMulAction.toSMul
local instance hugeRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := hugeRealModule.toDistribMulAction.smul_zero }

 

theorem standard_center_phase (r S : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    S*|-2*(⟪actualDisplacement r w a k,S • (0:ModeInfinity)⟫_ℂ).im|=0 := by
  simp only [smul_zero,inner_zero_right,Complex.zero_im,mul_zero,abs_zero]

 

theorem huge_ordinary_scaled_phases {α ι : Type*} [Fintype ι] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (t : ℝ) (ht : t≠0) (ds : ι → α → ModeInfinity) (c : ι → ℝ)
    (xp xm : α → PreSpin ModeInfinity) (xs : ι → α → PreSpin ModeInfinity)
    (ρ : α → SpinSpace ModeInfinity)
    (hS : Tendsto S l atTop) (B A T : ℝ) (hA : 0≤A) (hT0 : 0≤T)
    (hT : ∀j<K,|(a j).2|≤T) (hr : ∀ᶠ q in l,|r q|≤1)
    (hscale : ∀ᶠ q in l,r q*S q=1)
    (hxp : ∀ᶠ q in l,SpinRadiusLE (xp q) B ∧ spinMass (xp q)≤A)
    (hxm : ∀ᶠ q in l,SpinRadiusLE (xm q) B ∧ spinMass (xm q)≤A)
    (hxs : ∀i,∀ᶠ q in l,SpinRadiusLE (xs i q) B ∧ spinMass (xs i q)≤A)
    (hc : ∀i,c i≠0)
    (hvis : ∀i,Tendsto (fun q => (⟪insertionInfinity (w q),ds i q⟫_ℂ).im) l (𝓝 (c i)))
    (hψ : ∀ᶠ q in l,ordinaryLocal (w q) (vacuum ModeInfinity)=
      actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q)+
      actualPacket (S q) (t • insertionInfinity (w q)) (xm q)+
      (∑i,actualPacket (S q) (ds i q) (xs i q))+ρ q)
    (hop : ∀ᶠ q in l,SpinOperators.act Z
      (actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))=
      actualPacket (S q) ((-t) • insertionInfinity (w q)) (xp q))
    (hom : ∀ᶠ q in l,SpinOperators.act Z
      (actualPacket (S q) (t • insertionInfinity (w q)) (xm q))=
      -actualPacket (S q) (t • insertionInfinity (w q)) (xm q))
    (hρ : Tendsto (fun q => S q*‖ρ q‖) l (𝓝 0))
    (hs : Tendsto (fun q => S q*‖∑i,actualPacket (S q) (ds i q) (xs i q)‖^2) l (𝓝 0)) :
    ∀j<K,∀b : ℝ,Tendsto (fun q => S q*|-2*(⟪actualDisplacement (r q) (w q) a j,
      S q • (b • insertionInfinity (w q))⟫_ℂ).im|) l (𝓝 0) := by
  obtain ⟨δ,hδ,hps,hms⟩ := PacketGeometry.finite_projection_separation
    (fun q => insertionInfinity (w q)) ds c (-t) t hc
    (Eventually.of_forall (fun q => (norm_insertionInfinity (w q)).le)) hvis
  let δ' := min δ (2*|t|)
  have hδ' : 0<δ' := lt_min hδ (mul_pos (by norm_num) (abs_pos.mpr ht))
  have hpm : ∀ᶠ q in l,δ'≤‖(-t) • insertionInfinity (w q)-t • insertionInfinity (w q)‖ := by
    apply Eventually.of_forall
    intro q
    rw [←sub_smul,norm_smul,norm_insertionInfinity,mul_one,Real.norm_eq_abs]
    have he : -t-t= -(2*t) := by ring
    rw [he,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact min_le_right _ _
  intro j hj b
  apply scaled_huge_center_phase r S w a j b hscale
  apply actual_huge_packet_phase r S w a j K hj.le
    (fun q => (-t) • insertionInfinity (w q)) (fun q => t • insertionInfinity (w q))
    ds xp xm xs ρ hS B A δ' T hA hδ' hT0 hT hr hxp hxm hxs hpm
    (fun i => (hps i).mono (fun q hq => (min_le_left _ _).trans hq))
    (fun i => (hms i).mono (fun q hq => (min_le_left _ _).trans hq))
    hψ hop hom hρ hs

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

 

theorem scaled_identity_transfer (V : α → H ≃ₗᵢ[ℂ] H) (S : α → ℝ)
    (x y : α → H) (hS : ∀ᶠ t in l,0≤S t)
    (hy : Tendsto (fun t => S t*‖V t (y t)-y t‖) l (𝓝 0))
    (hxy : Tendsto (fun t => S t*‖x t-y t‖) l (𝓝 0)) :
    Tendsto (fun t => S t*‖V t (x t)-x t‖) l (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [zero_mul,add_zero] using hy.add (hxy.mul_const 2))
  · filter_upwards [hS] with t ht
    exact mul_nonneg ht (norm_nonneg _)
  · filter_upwards [hS] with t ht
    have he : V t (x t)-x t=(V t (y t)-y t)+V t (x t-y t)-(x t-y t) := by
      simp only [map_sub]
      abel
    have hn : ‖V t (x t)-x t‖≤‖V t (y t)-y t‖+2*‖x t-y t‖ := by
      rw [he]
      have h := (norm_sub_le (V t (y t)-y t+V t (x t-y t)) (x t-y t)).trans
        (add_le_add (norm_add_le (V t (y t)-y t) (V t (x t-y t))) le_rfl)
      rw [(V t).norm_map] at h
      linarith
    nlinarith

end ForwardControl

end

end OAI
