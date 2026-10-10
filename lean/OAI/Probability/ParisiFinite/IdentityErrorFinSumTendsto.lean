import Mathlib
import OAI.Probability.ParisiFinite.ActualDisplacement

namespace OAI

/-! Identity Error Fin Sum Tendsto. -/

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
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem identity_error_finSum_tendsto {α ι : Type*} [Fintype ι] {l : Filter α}
    (V : α → H ≃ₗᵢ[ℂ] H) (x : α → ι → H)
    (hx : ∀j,Tendsto (fun t => ‖V t (x t j)-x t j‖) l (𝓝 0)) :
    Tendsto (fun t => ‖V t (∑j,x t j)-(∑j,x t j)‖) l (𝓝 0) := by
  have h := PacketGeometry.scaled_norm_sum_tendsto (fun _ : α => (1:ℝ))
    (fun t j => V t (x t j)-x t j) (Eventually.of_forall (fun _ => by norm_num))
    (by intro j; simpa only [one_mul] using hx j)
  simpa only [one_mul,Finset.sum_sub_distrib,map_sum] using h

 

theorem split_forward_tendsto {α : Type*} {l : Filter α}
    (V : α → H ≃ₗᵢ[ℂ] H) (o s ρ : α → H)
    (ho : Tendsto (fun t => ‖V t (o t)-o t‖) l (𝓝 0))
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    Tendsto (fun t => ‖V t (o t+s t+ρ t)-(o t+s t+ρ t)‖) l (𝓝 0) := by
  have h := (ho.add (hs.const_mul 2)).add (hρ.const_mul 2)
  simp only [mul_zero,add_zero] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => identity_error_split (V t) (o t) (s t) (ρ t)) h

end ForwardControl

namespace PointedTree
open CoherentFock RootSpin

 

theorem actual_direction_from_split {α : Type*} {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (o s ρ : α → SpinSpace ModeInfinity)
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=o t+s t+ρ t)
    (ho : Tendsto (fun t => ‖probeGain (r t) (w t) a k (o t)-o t‖) l (𝓝 0))
    (hoP : Tendsto (fun t => ‖probeGain (r t) (w t) a k (SpinOperators.act (rotatedZ (a k).1) (o t))-
      SpinOperators.act (rotatedZ (a k).1) (o t)‖) l (𝓝 0))
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    Tendsto (fun t => ‖actualProbeDirection (r t) (w t) a k-
      insertionInfinity (.mixer (a k).1::w t)‖) l (𝓝 0) := by
  have h := ((ho.add hoP).add (hs.const_mul 4)).add (hρ.const_mul 4)
  simp only [mul_zero,add_zero] at h
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ h
  filter_upwards [hψ] with t hψt
  apply (actual_direction_change_bound (r t) (w t) a k).trans
  rw [hψt]
  exact ForwardControl.conjugation_error_split (probeGain (r t) (w t) a k)
    (SpinOperators.act (rotatedZ (a k).1)) (fun x => (SpinOperators.norm_act (rotatedZ_unitary _) x).le)
    (o t) (s t) (ρ t)

end PointedTree

 

open scoped Topology BigOperators
open Filter
namespace FiniteError

def envelope (k : ℕ) (f : ℕ → ℝ) : ℝ := ∑j∈Finset.range k,|f j|

theorem envelope_nonneg (k : ℕ) (f : ℕ → ℝ) : 0≤envelope k f :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem le_envelope (k : ℕ) (f : ℕ → ℝ) (j : ℕ) (hj : j<k) : |f j|≤envelope k f :=
  Finset.single_le_sum (f := fun i => |f i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hj)

theorem envelope_tendsto_zero {α : Type*} {l : Filter α} (k : ℕ) (f : α → ℕ → ℝ)
    (hf : ∀j<k,Tendsto (fun t => f t j) l (𝓝 0)) :
    Tendsto (fun t => envelope k (f t)) l (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range k) (fun j hj => (hf j (Finset.mem_range.mp hj)).abs)
  simpa only [envelope,abs_zero,Finset.sum_const_zero] using h

theorem scaled_envelope_tendsto_zero {α : Type*} {l : Filter α}
    (k : ℕ) (S : α → ℝ) (f : α → ℕ → ℝ)
    (hf : ∀j<k,Tendsto (fun t => S t*|f t j|) l (𝓝 0)) :
    Tendsto (fun t => S t*envelope k (f t)) l (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range k) (fun j hj => hf j (Finset.mem_range.mp hj))
  simpa only [envelope,Finset.mul_sum,Finset.sum_const_zero] using h

end FiniteError

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 

theorem tail_bounds_of_radius_mass (x : PreSpin E) (B A : ℝ) (hB : 0≤B)
    (hx : SpinRadiusLE x B ∧ spinMass x≤A) :
    spinBound x≤A*(1+2*B+12*B^2) ∧ ‖spinCoe x‖≤A := by
  exact ⟨(spinBound_le_mass x hB hx.1).trans
    (mul_le_mul_of_nonneg_right hx.2 (by positivity)),(norm_spinCoe_le_mass x).trans hx.2⟩

end CoherentFock

namespace PointedTree
open CoherentFock RootSpin
local instance forwardRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance forwardRealSMul : SMul ℝ ModeInfinity := forwardRealModule.toDistribMulAction.toSMul

 

theorem packet_forward_of_phases {α : Type*} {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (d : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (B A T : ℝ)
    (hB : 0≤B) (hA : 0≤A) (hT : 0≤T) (ha : ∀j<k,|(a j).2|≤T)
    (hr : Tendsto r l (𝓝 0)) (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hp : ∀j<k,Tendsto (fun t => -2*(⟪actualDisplacement (r t) (w t) a j,S t • d t⟫_ℂ).im) l (𝓝 0)) :
    Tendsto (fun t => ‖probeGain (r t) (w t) a k (actualPacket (S t) (d t) (x t))-
      actualPacket (S t) (d t) (x t)‖) l (𝓝 0) := by
  let phase (t : α) := FiniteError.envelope k (fun j => -2*(⟪actualDisplacement (r t) (w t) a j,S t • d t⟫_ℂ).im)
  apply actual_forward_tendsto r w a k (fun t => S t • d t) x phase T
    (A*(1+2*B+12*B^2)) A hT (by positivity) hA ha hr
    (FiniteError.envelope_tendsto_zero k _ hp)
    (Eventually.of_forall (fun _ => FiniteError.envelope_nonneg ..))
    (Eventually.of_forall (fun t j hj => FiniteError.le_envelope k
      (fun q => -2*(⟪actualDisplacement (r t) (w t) a q,S t • d t⟫_ℂ).im) j hj))
  filter_upwards [hx] with t ht
  exact tail_bounds_of_radius_mass (x t) B A hB ht

 

theorem packet_root_forward_of_phases {α : Type*} {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (d : α → ModeInfinity) (x : α → PreSpin ModeInfinity) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (B A T : ℝ) (hB : 0≤B) (hA : 0≤A) (hT : 0≤T) (ha : ∀j<k,|(a j).2|≤T)
    (hr : Tendsto r l (𝓝 0)) (hx : ∀ᶠ t in l,SpinRadiusLE (x t) B ∧ spinMass (x t)≤A)
    (hp : ∀j<k,Tendsto (fun t => -2*(⟪actualDisplacement (r t) (w t) a j,S t • d t⟫_ℂ).im) l (𝓝 0)) :
    Tendsto (fun t => ‖probeGain (r t) (w t) a k (SpinOperators.act P (actualPacket (S t) (d t) (x t)))-
      SpinOperators.act P (actualPacket (S t) (d t) (x t))‖) l (𝓝 0) := by
  simp only [actualPacket_root]
  apply packet_forward_of_phases r S w a k d (fun t => preRoot P (x t)) B
    (matrixMass P*A) T hB (mul_nonneg (matrixMass_nonneg _) hA) hT ha hr _ hp
  filter_upwards [hx] with t ht
  exact ⟨ht.1.preRoot P,(spinMass_preRoot P _).trans
    (mul_le_mul_of_nonneg_left ht.2 (matrixMass_nonneg _))⟩

 

theorem packet_direction_tendsto {α ι : Type*} [Fintype ι] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (d : ι → α → ModeInfinity) (x : ι → α → PreSpin ModeInfinity)
    (s ρ : α → SpinSpace ModeInfinity) (B A T : ℝ)
    (hB : 0≤B) (hA : 0≤A) (hT : 0≤T) (ha : ∀j<k,|(a j).2|≤T)
    (hr : Tendsto r l (𝓝 0)) (hx : ∀i,∀ᶠ t in l,SpinRadiusLE (x i t) B ∧ spinMass (x i t)≤A)
    (hp : ∀i,∀j<k,Tendsto (fun t => -2*(⟪actualDisplacement (r t) (w t) a j,S t • d i t⟫_ℂ).im) l (𝓝 0))
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      (∑i,actualPacket (S t) (d i t) (x i t))+s t+ρ t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    Tendsto (fun t => ‖actualProbeDirection (r t) (w t) a k-
      insertionInfinity (.mixer (a k).1::w t)‖) l (𝓝 0) := by
  apply actual_direction_from_split r w a k _ s ρ hψ _ _ hs hρ
  · apply ForwardControl.identity_error_finSum_tendsto
    intro i
    exact packet_forward_of_phases r S w a k (d i) (x i) B A T hB hA hT ha hr (hx i) (hp i)
  · have ht := ForwardControl.identity_error_finSum_tendsto
      (fun t => probeGain (r t) (w t) a k)
      (fun t i => SpinOperators.act (rotatedZ (a k).1) (actualPacket (S t) (d i t) (x i t)))
      (fun i => packet_root_forward_of_phases r S w a k (d i) (x i) (rotatedZ (a k).1)
        B A T hB hA hT ha hr (hx i) (hp i))
    simpa only [map_sum] using ht

end PointedTree

 

open scoped BigOperators
namespace List
open scoped _root_.List

 

theorem range_map_getD_eq {α : Type*} (w : List α) (d : α) :
    (List.range w.length).map (fun j => w.getD j d)=w := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_map,List.getElem_range]
    exact (List.getElem_eq_getD d).symm

theorem reverse_range_map_getD_eq {α β : Type*} (w : List α) (d : α) (f : α → β) :
    (List.range w.length).reverse.map (fun j => f (w.getD j d))=w.reverse.map f := by
  have h := congrArg (fun q : List α => q.reverse.map f) (range_map_getD_eq w d)
  simpa only [List.map_reverse,List.map_map,Function.comp_def] using h

end List

namespace PointedTree
open CoherentFock RootSpin
local instance listclockRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance listclockRealSMul : SMul ℝ ModeInfinity := listclockRealModule.toDistribMulAction.toSMul

 

def pulseSequence (β : Bool → ℝ) (s : List (Bool×ℝ)) (j : ℕ) : ShortPulse :=
  (β (s.getD j (false,0)).1,(s.getD j (false,0)).2)

theorem pulseSequence_clocks (β : Bool → ℝ) (s : List (Bool×ℝ))
    (hs : ∀b,((s.filter (fun p => decide (p.1=b))).map Prod.snd).sum=0)
    (w : List Gate) (x : PreSpin ModeInfinity) :
    ((List.range s.length).reverse.map (fun j => Complex.I •
      probeField (R (pulseSequence β s j).1) (startingVelocity w (pulseSequence β s) j) x)).sum=0 := by
  have he : (fun j => Complex.I • probeField (R (pulseSequence β s j).1)
      (startingVelocity w (pulseSequence β s) j) x)=
      (fun j => (fun p : Bool×ℝ => Complex.I • probeField (R (β p.1))
        (-p.2 • insertionInfinity (.mixer (β p.1)::w)) x) (s.getD j (false,0))) := by rfl
  rw [he]
  have hh := List.reverse_range_map_getD_eq s (false,0)
    (fun p : Bool×ℝ => Complex.I • probeField (R (β p.1))
      (-p.2 • insertionInfinity (.mixer (β p.1)::w)) x)
  rw [hh,List.map_reverse,List.sum_reverse]
  exact probeField_zero_two_clocks s hs (fun b => R (β b))
    (fun b => insertionInfinity (.mixer (β b)::w)) x

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance cancelRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance cancelRealSMul : SMul ℝ ModeInfinity := cancelRealModule.toDistribMulAction.toSMul

 

theorem phase_tendsto_of_scaled {α : Type*} {l : Filter α} (S f : α → ℝ)
    (hS : ∀ᶠ t in l,1≤S t) (hf : Tendsto (fun t => S t*|f t|) l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using PacketGeometry.tendsto_of_scaled S (fun t => |f t|)
    hS (Eventually.of_forall (fun _ => abs_nonneg _)) hf

 

theorem packet_direction_envelope_tendsto {α ι : Type*} [Fintype ι] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (d : ι → α → ModeInfinity) (x : ι → α → PreSpin ModeInfinity)
    (s ρ : α → SpinSpace ModeInfinity) (B A T : ℝ)
    (hB : 0≤B) (hA : 0≤A) (hT : 0≤T) (ha : ∀j<K,|(a j).2|≤T)
    (hr : Tendsto r l (𝓝 0)) (hS : ∀ᶠ t in l,1≤S t)
    (hx : ∀i,∀ᶠ t in l,SpinRadiusLE (x i t) B ∧ spinMass (x i t)≤A)
    (hp : ∀i,∀j<K,Tendsto (fun t => S t*|-2*(⟪actualDisplacement (r t) (w t) a j,S t • d i t⟫_ℂ).im|) l (𝓝 0))
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      (∑i,actualPacket (S t) (d i t) (x i t))+s t+ρ t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0)) :
    Tendsto (fun t => FiniteError.envelope K (fun j => ‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖)) l (𝓝 0) := by
  apply FiniteError.envelope_tendsto_zero
  intro j hj
  apply packet_direction_tendsto r S w a j d x s ρ B A T hB hA hT
    (fun k hk => ha k (hk.trans hj)) hr hx _ hψ hs hρ
  intro i k hk
  exact phase_tendsto_of_scaled S _ hS (hp i k (hk.trans hj))

 

theorem packet_zero_clock_from_vacuum {α ι : Type*} [Fintype ι] {l : Filter α}
    (r S : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (d : ι → α → ModeInfinity) (x : ι → α → PreSpin ModeInfinity)
    (s ρ : α → SpinSpace ModeInfinity) (B A T : ℝ)
    (hB : 0≤B) (hA : 0≤A) (hT : 0≤T) (ha : ∀j<K,|(a j).2|≤T)
    (hr : Tendsto r l (𝓝 0)) (hS : ∀ᶠ t in l,1≤S t)
    (hscale : ∀ᶠ t in l,0≤r t ∧ 0≤S t ∧ S t*r t=1)
    (hx : ∀i,∀ᶠ t in l,SpinRadiusLE (x i t) B ∧ spinMass (x i t)≤A)
    (hp : ∀i,∀j<K,Tendsto (fun t => S t*|-2*(⟪actualDisplacement (r t) (w t) a j,S t • d i t⟫_ℂ).im|) l (𝓝 0))
    (hψ : ∀ᶠ t in l,ordinaryLocal (w t) (vacuum ModeInfinity)=
      (∑i,actualPacket (S t) (d i t) (x i t))+s t+ρ t)
    (hs : Tendsto (fun t => ‖s t‖) l (𝓝 0)) (hρ : Tendsto (fun t => ‖ρ t‖) l (𝓝 0))
    (e : α → ModeInfinity) (z : α → PreSpin ModeInfinity) (B' A' : ℝ)
    (hB' : 0≤B') (hA' : 0≤A')
    (hz : ∀ᶠ t in l,SpinRadiusLE (z t) B' ∧ spinMass (z t)≤A')
    (he : ∀j<K,Tendsto (fun t => S t*|-2*(⟪actualDisplacement (r t) (w t) a j,S t • e t⟫_ℂ).im|) l (𝓝 0))
    (hclock : ∀ᶠ t in l,((List.range K).reverse.map (fun j => Complex.I •
      probeField (R (a j).1) (startingVelocity (w t) a j) (z t))).sum=0) :
    Tendsto (fun t => S t*‖probeGain (r t) (w t) a K (actualPacket (S t) (e t) (z t))-
      actualPacket (S t) (e t) (z t)‖) l (𝓝 0) := by
  let Δ (t : α) := FiniteError.envelope K (fun j => ‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖)
  let phase (t : α) := FiniteError.envelope K
    (fun j => -2*(⟪actualDisplacement (r t) (w t) a j,S t • e t⟫_ℂ).im)
  have hΔ : Tendsto Δ l (𝓝 0) := packet_direction_envelope_tendsto r S w a K d x s ρ
    B A T hB hA hT ha hr hS hx hp hψ hs hρ
  have hd : ∀ᶠ t in l,∀j<K,‖actualProbeDirection (r t) (w t) a j-
      insertionInfinity (.mixer (a j).1::w t)‖≤Δ t := by
    exact Eventually.of_forall (fun t j hj => by
      simpa only [abs_norm] using FiniteError.le_envelope K
        (fun j => ‖actualProbeDirection (r t) (w t) a j-insertionInfinity (.mixer (a j).1::w t)‖) j hj)
  have hp' : ∀ᶠ t in l,∀j<K,|-2*(⟪actualDisplacement (r t) (w t) a j,S t • e t⟫_ℂ).im|≤phase t := by
    exact Eventually.of_forall (fun t j hj => FiniteError.le_envelope K
      (fun j => -2*(⟪actualDisplacement (r t) (w t) a j,S t • e t⟫_ℂ).im) j hj)
  have hx' : ∀ᶠ t in l,spinBound (z t)≤A'*(1+2*B'+12*B'^2) ∧ ‖spinCoe (z t)‖≤A' := by
    filter_upwards [hz] with t ht
    exact tail_bounds_of_radius_mass (z t) B' A' hB' ht
  exact actual_zero_clock_tendsto r S w a K (fun t => S t • e t) z Δ phase T
    (A'*(1+2*B'+12*B'^2)) A' hT (by positivity) hA' ha hr hΔ
    (FiniteError.scaled_envelope_tendsto_zero K S _ he) hscale
    (Eventually.of_forall (fun _ => ⟨FiniteError.envelope_nonneg ..,FiniteError.envelope_nonneg ..⟩))
    hd hp' hx' hclock

end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace ForwardControl
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {l : Filter α}

 

theorem scaled_flip_from_limits (U V : α → H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x,‖Z x‖≤‖x‖) (hanti : ∀x,Z (F x)= -F (Z x))
    (Ω : H) (o s w : α → H) (hx : ∀q,U q Ω=o q+s q)
    (r : α → ℝ) (t : ℝ) (hr : ∀ᶠ q in l,0<r q)
    (h1 : Tendsto (fun q => (r q)⁻¹*‖V q (o q)-o q‖) l (𝓝 0))
    (h2 : Tendsto (fun q => (r q)⁻¹*‖V q (s q)-F (s q)‖) l (𝓝 0))
    (h3 : Tendsto (fun q => (r q)⁻¹*‖V q (Z (o q))-Z (o q)‖) l (𝓝 0))
    (h4 : Tendsto (fun q => (r q)⁻¹*‖V q (Z (s q))-F (Z (s q))‖) l (𝓝 0))
    (ht : Tendsto (fun q => ‖(r q)⁻¹ • (U q).symm (Z (s q))-w q‖) l (𝓝 0)) :
    Tendsto (fun q => ‖(t/r q) • ((U q).symm ((V q).symm (Z (V q (U q Ω))))-
      (U q).symm (Z (U q Ω)))-(-2*t) • w q‖) l (𝓝 0) := by
  let e (q : α) := ‖V q (o q)-o q‖+‖V q (s q)-F (s q)‖+
    ‖V q (Z (o q))-Z (o q)‖+‖V q (Z (s q))-F (Z (s q))‖
  let ε (q : α) := (r q)⁻¹*e q
  have he : Tendsto ε l (𝓝 0) := by
    simpa only [ε,e,mul_add,add_zero] using ((h1.add h2).add h3).add h4
  have hmul : ∀ᶠ q in l,r q*ε q=e q := by
    filter_upwards [hr] with q hq
    simp only [ε,←mul_assoc,mul_inv_cancel₀ hq.ne',one_mul]
  apply actual_scaled_flip_tendsto U V Z F hZ hanti Ω o s w hx r ε
    (fun q => ‖(r q)⁻¹ • (U q).symm (Z (s q))-w q‖) t hr he ht
  · filter_upwards [hmul] with q hq
    rw [hq]
    dsimp only [e]
    linarith [norm_nonneg (V q (s q)-F (s q)),norm_nonneg (V q (Z (o q))-Z (o q)),
      norm_nonneg (V q (Z (s q))-F (Z (s q)))]
  · filter_upwards [hmul] with q hq
    rw [hq]
    dsimp only [e]
    linarith [norm_nonneg (V q (o q)-o q),norm_nonneg (V q (Z (o q))-Z (o q)),
      norm_nonneg (V q (Z (s q))-F (Z (s q)))]
  · filter_upwards [hmul] with q hq
    rw [hq]
    dsimp only [e]
    linarith [norm_nonneg (V q (o q)-o q),norm_nonneg (V q (s q)-F (s q)),
      norm_nonneg (V q (Z (s q))-F (Z (s q)))]
  · filter_upwards [hmul] with q hq
    rw [hq]
    dsimp only [e]
    linarith [norm_nonneg (V q (o q)-o q),norm_nonneg (V q (s q)-F (s q)),
      norm_nonneg (V q (Z (o q))-Z (o q))]
  · exact Eventually.of_forall (fun _ => le_rfl)

end ForwardControl

namespace PointedTree
open CoherentFock RootSpin
local instance echoRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance echoRealSMul : SMul ℝ ModeInfinity := echoRealModule.toDistribMulAction.toSMul

 
theorem modeFock_probe_insertion (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (K : ℕ) :
    modeFock (insertionInfinity (probePrefix r w a K))=
      (ordinaryLocal w).symm ((probeGain r w a K).symm
        (SpinOperators.act Z (probeGain r w a K (ordinaryLocal w (vacuum ModeInfinity))))) := by
  rw [modeFock_insertion]
  change _=(ordinaryLocal w).symm (ordinaryLocal w
    ((ordinaryLocal (probePrefix r w a K)).symm (SpinOperators.act Z
      (ordinaryLocal (probePrefix r w a K) ((ordinaryLocal w).symm (ordinaryLocal w (vacuum ModeInfinity)))))))
  simp only [LinearIsometryEquiv.symm_apply_apply]

 

theorem actual_flip_mode_tendsto {α : Type*} {l : Filter α}
    (r : α → ℝ) (w : α → List Gate) (a : ℕ → ShortPulse) (K : ℕ)
    (o s : α → SpinSpace ModeInfinity) (address : α → ModeInfinity)
    (F : SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity)
    (hanti : ∀x,SpinOperators.act Z (F x)= -F (SpinOperators.act Z x))
    (hx : ∀q,ordinaryLocal (w q) (vacuum ModeInfinity)=o q+s q)
    (t : ℝ) (hr : ∀ᶠ q in l,0<r q)
    (h1 : Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (o q)-o q‖) l (𝓝 0))
    (h2 : Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (s q)-F (s q)‖) l (𝓝 0))
    (h3 : Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (SpinOperators.act Z (o q))-
      SpinOperators.act Z (o q)‖) l (𝓝 0))
    (h4 : Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (w q) a K (SpinOperators.act Z (s q))-
      F (SpinOperators.act Z (s q))‖) l (𝓝 0))
    (ht : Tendsto (fun q => ‖(r q)⁻¹ • (ordinaryLocal (w q)).symm (SpinOperators.act Z (s q))-
      modeFock (address q)‖) l (𝓝 0)) :
    Tendsto (fun q => ‖(t/r q) • (insertionInfinity (probePrefix (r q) (w q) a K)-insertionInfinity (w q))-
      (-2*t) • address q‖) l (𝓝 0) := by
  have h := ForwardControl.scaled_flip_from_limits (fun q => ordinaryLocal (w q))
    (fun q => probeGain (r q) (w q) a K) (SpinOperators.act Z) F
    (fun x => (SpinOperators.norm_act Z_unitary x).le) hanti (vacuum ModeInfinity) o s
    (fun q => modeFock (address q)) hx r t hr h1 h2 h3 h4 ht
  apply h.congr'
  exact Eventually.of_forall (fun q => by
    dsimp only
    rw [←modeFock.norm_map ((t/r q) • (insertionInfinity (probePrefix (r q) (w q) a K)-insertionInfinity (w q))-(-2*t) • address q)]
    simp only [map_sub, RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul]
    rw [modeFock_probe_insertion,modeFock_insertion])

end PointedTree

 

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
namespace RootSpin

 

theorem exists_mixer_frame (a b : ℝ) (hab : a^2+b^2=1) :
    ∃ β : ℝ,Real.cos (2*β)=a ∧ Real.sin (2*β)=b ∧
      Real.cos (2*(β+Real.pi/4))= -b ∧ Real.sin (2*(β+Real.pi/4))=a := by
  let z : ℂ := ⟨a,b⟩
  have hn : ‖z‖=1 := by
    have h2 : ‖z‖^2=1 := by
      rw [Complex.sq_norm]
      simpa only [Complex.normSq_apply,z,pow_two] using hab
    nlinarith [norm_nonneg z]
  refine ⟨z.arg/2,?_,?_,?_,?_⟩
  · simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0),hn,one_mul] using Complex.norm_mul_cos_arg z
  · simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0),hn,one_mul] using Complex.norm_mul_sin_arg z
  · rw [show 2*(z.arg/2+Real.pi/4)=z.arg+Real.pi/2 by ring,Real.cos_add_pi_div_two]
    congr 1
    simpa only [hn,one_mul] using Complex.norm_mul_sin_arg z
  · rw [show 2*(z.arg/2+Real.pi/4)=z.arg+Real.pi/2 by ring,Real.sin_add_pi_div_two]
    simpa only [hn,one_mul] using Complex.norm_mul_cos_arg z

end RootSpin

namespace CoherentFock
open RootSpin
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
theorem phaseZ_eq_act_exp (θ : ℝ) :
    phaseZ (E:=E) θ=SpinOperators.act (NormedSpace.exp ((Complex.I*(θ:ℂ)) • Z)) := by
  have hz : (Complex.I*(θ:ℂ)) • Z=Matrix.diagonal
      (fun i : Fin 2 => (((if i=0 then θ else -θ : ℝ):ℂ)*Complex.I)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z] <;> ring
  rw [hz,Matrix.exp_diagonal,Pi.exp_def]
  simp only [←Complex.exp_eq_exp_ℂ,phaseZ]

end CoherentFock

namespace RootSpin

 

theorem exp_rotated_Z (β θ : ℝ) :
    NormedSpace.exp ((Complex.I*(θ:ℂ)) • ((R β).conjTranspose*Z*R β))=
      (R β).conjTranspose*NormedSpace.exp ((Complex.I*(θ:ℂ)) • Z)*R β := by
  let U : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
    ⟨(R β).conjTranspose,R β,(Unitary.mem_iff.mp (R_unitary β)).1,
      (Unitary.mem_iff.mp (R_unitary β)).2⟩
  have he := Matrix.exp_units_conj U ((Complex.I*(θ:ℂ)) • Z)
  change NormedSpace.exp ((R β).conjTranspose*((Complex.I*(θ:ℂ)) • Z)*R β)=
    (R β).conjTranspose*NormedSpace.exp ((Complex.I*(θ:ℂ)) • Z)*R β at he
  rwa [Matrix.mul_smul,Matrix.smul_mul] at he

end RootSpin

namespace SpinOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem act_conj_comp (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (act A : Double H →L[ℂ] Double H).comp ((act B).comp (act C))=act (A*B*C) := by
  rw [act_mul,act_mul,ContinuousLinearMap.comp_assoc]
end SpinOperators

namespace CoherentFock
open RootSpin
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
theorem probePhase_eq_act_exp (β θ : ℝ) :
    probePhase (E:=E) (R β) θ=SpinOperators.act
      (NormedSpace.exp ((Complex.I*(θ:ℂ)) • ((R β).conjTranspose*Z*R β))) := by
  calc
    _ = (SpinOperators.act (R β).conjTranspose).comp
        ((SpinOperators.act (NormedSpace.exp ((Complex.I*(θ:ℂ)) • Z))).comp (SpinOperators.act (R β))) :=
      congrArg (fun T : SpinSpace E →L[ℂ] SpinSpace E =>
        (SpinOperators.act (R β).conjTranspose).comp (T.comp (SpinOperators.act (R β))))
          (phaseZ_eq_act_exp θ)
    _ = SpinOperators.act ((R β).conjTranspose*NormedSpace.exp ((Complex.I*(θ:ℂ)) • Z)*R β) :=
      SpinOperators.act_conj_comp _ _ _
    _ = _ := congrArg SpinOperators.act (exp_rotated_Z β θ).symm

end CoherentFock

namespace QuaternionControl
open SeedControl RootSpin

@[simp] theorem skewX_eq : SeedControl.x=(-Complex.I) • X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SeedControl.x,X]
@[simp] theorem skewY_eq : SeedControl.y=(-Complex.I) • Y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SeedControl.y,Y]
@[simp] theorem skewZ_eq : SeedControl.z=(-Complex.I) • Z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SeedControl.z,Z]

def axisAngle (β : ℝ) (b : Bool) : ℝ := if b then β else β+Real.pi/4

def axisProjection (a b : ℝ) (v : ℝ×ℝ) (e : Bool) : ℝ :=
  if e then a*v.1+b*v.2 else -b*v.1+a*v.2

 

theorem spinGen_eq_rotated {ι : Type*} (a b β : ℝ)
    (hc : Real.cos (2*β)=a) (hs : Real.sin (2*β)=b)
    (hc' : Real.cos (2*(β+Real.pi/4))= -b) (hs' : Real.sin (2*(β+Real.pi/4))=a)
    (v : ι → ℝ×ℝ) (e : Bool) (i : ι) :
    spinGen a b (fun j => a*(v j).1+b*(v j).2)
      (fun j => -b*(v j).1+a*(v j).2) e i=
      axisProjection a b (v i) e • ((-Complex.I) •
        ((R (axisAngle β e)).conjTranspose*Z*R (axisAngle β e))) := by
  cases e <;> simp only [spinGen,Bool.false_eq_true,ite_false,ite_true,axisProjection,axisAngle,
    R_conjugate_Z,hc,hs,hc',hs',skewZ_eq,skewY_eq]
  all_goals
    ext j k
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_neg]
    ring

end QuaternionControl

 

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
namespace SpinOperators
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem act_prod (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (s : List ι) :
    (act ((s.map A).prod) : Double H →L[ℂ] Double H)=ProbeProduct.act (fun i => act (A i)) s := by
  induction s with
  | nil => exact act_one
  | cons i s ih =>
    simp only [List.map_cons,List.prod_cons,act_mul,ih,ProbeProduct.act]

end SpinOperators

namespace QuaternionControl
open RootSpin

theorem real_smul_skew (τ c : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    τ • (c • ((-Complex.I) • P))=(Complex.I*((-τ*c:ℝ):ℂ)) • P := by
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

theorem exp_skewX (θ : ℝ) : NormedSpace.exp (θ • SeedControl.x)=R θ := by
  rw [skewX_eq,R_eq_exp]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  ring

 

theorem phase_product_eq {ι : Type*} (v : ι → ℝ×ℝ) (a b β θ : ℝ)
    (hc : Real.cos (2*β)=a) (hs : Real.sin (2*β)=b)
    (hc' : Real.cos (2*(β+Real.pi/4))= -b) (hs' : Real.sin (2*(β+Real.pi/4))=a)
    (s : List (Bool×ℝ))
    (hprod : ∀i,(s.reverse.map (fun p => NormedSpace.exp (p.2 •
      spinGen a b (fun j => a*(v j).1+b*(v j).2)
        (fun j => -b*(v j).1+a*(v j).2) p.1 i))).prod=NormedSpace.exp (θ • SeedControl.x))
    (i : ι) :
    (s.reverse.map (fun p => NormedSpace.exp
      ((Complex.I*((-p.2*axisProjection a b (v i) p.1:ℝ):ℂ)) •
        ((R (axisAngle β p.1)).conjTranspose*Z*R (axisAngle β p.1))))).prod=R θ := by
  have h := hprod i
  simp only [spinGen_eq_rotated a b β hc hs hc' hs',real_smul_skew,exp_skewX] at h
  exact h

end QuaternionControl

namespace PointedTree
open CoherentFock RootSpin QuaternionControl

 

def projectionPhase (v : ℝ×ℝ) (p : ShortPulse) : ℝ :=
  -p.2*(Real.cos (2*p.1)*v.1+Real.sin (2*p.1)*v.2)

theorem rotated_coordinate (a b β : ℝ)
    (hc : Real.cos (2*β)=a) (hs : Real.sin (2*β)=b)
    (hc' : Real.cos (2*(β+Real.pi/4))= -b) (hs' : Real.sin (2*(β+Real.pi/4))=a)
    (v : ℝ×ℝ) (e : Bool) :
    Real.cos (2*axisAngle β e)*v.1+Real.sin (2*axisAngle β e)*v.2=axisProjection a b v e := by
  cases e <;> simp only [axisAngle,axisProjection,Bool.false_eq_true,ite_false,ite_true,hc,hs,hc',hs']

 

theorem selective_phase_control {ι : Type*} [Fintype ι]
    (v : ι → ℝ×ℝ) (hv : ∀i,v i≠0) (θ : ℝ) :
    ∃ (K : ℕ) (a : ℕ → ShortPulse) (T : ℝ),0≤T ∧
      (∀j<K,|(a j).2|≤T) ∧
      (∀ (w : List Gate) (x : PreSpin ModeInfinity),
        ((List.range K).reverse.map (fun j => Complex.I •
          probeField (R (a j).1) (startingVelocity w a j) x)).sum=0) ∧
      ∀i,ProbeProduct.act (fun j => probePhase (E:=ModeInfinity) (R (a j).1)
        (projectionPhase (v i) (a j))) (List.range K).reverse=SpinOperators.act (R θ) := by
  obtain ⟨c,d,hcd,hs⟩ := selective_rotations_zero_clocks v hv
  obtain ⟨β,hc,hd,hc',hd'⟩ := exists_mixer_frame c d hcd
  obtain ⟨s,hs0,hsp⟩ := hs θ
  let a := pulseSequence (axisAngle β) s
  let T := FiniteError.envelope s.length (fun j => (a j).2)
  refine ⟨s.length,a,T,FiniteError.envelope_nonneg ..,?_,?_,?_⟩
  · intro j hj; exact FiniteError.le_envelope s.length (fun j => (a j).2) j hj
  · intro w x; exact pulseSequence_clocks (axisAngle β) s hs0 w x
  · intro i
    let F (p : Bool×ℝ) : Matrix (Fin 2) (Fin 2) ℂ := NormedSpace.exp
      ((Complex.I*((-p.2*axisProjection c d (v i) p.1:ℝ):ℂ)) •
        ((R (axisAngle β p.1)).conjTranspose*Z*R (axisAngle β p.1)))
    have hprod : (s.reverse.map F).prod=R θ := phase_product_eq v c d β θ hc hd hc' hd' s hsp i
    have hmat : ((List.range s.length).reverse.map (fun j => F (s.getD j (false,0)))).prod=R θ := by
      rw [List.reverse_range_map_getD_eq]; exact hprod
    have hf : (fun j => probePhase (E:=ModeInfinity) (R (a j).1) (projectionPhase (v i) (a j)))=
        (fun j => SpinOperators.act (F (s.getD j (false,0)))) := by
      funext j
      dsimp only [a,pulseSequence,projectionPhase]
      rw [rotated_coordinate c d β hc hd hc' hd',probePhase_eq_act_exp]
    rw [hf,←SpinOperators.act_prod,hmat]

end PointedTree

 

open scoped InnerProductSpace Topology
open Filter
namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
theorem short_large_phase (r S τ : ℝ) (v d : E) :
    -2*(⟪-((r*τ:ℝ):ℂ) • v,S • d⟫_ℂ).im=2*r*S*τ*(⟪v,d⟫_ℂ).im := by
  rw [inner_smul_left]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) S d,inner_smul_real_right]
  simp only [map_neg,Complex.conj_ofReal,Complex.real_smul,Complex.mul_im,Complex.neg_re,
    Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  ring

 

theorem imaginary_projection_difference (v v' d : E) :
    |(⟪v,d⟫_ℂ).im-(⟪v',d⟫_ℂ).im|≤‖v-v'‖*‖d‖ := by
  calc
    _ = |(⟪v-v',d⟫_ℂ).im| := by rw [inner_sub_left,Complex.sub_im]
    _ ≤ ‖⟪v-v',d⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _

end CoherentFock

end

end OAI
