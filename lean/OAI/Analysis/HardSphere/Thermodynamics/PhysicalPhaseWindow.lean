import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PhysicalPhase
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalUniformModulus

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
open BathSlice
attribute [local instance] Classical.propDecidable

lemma geometry_scale_eventually {A b : ℝ} (hA : 0<A) (hb : 0<b) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0<α → α≤2*A →
      α/D≤1/4096 ∧ 6*(α/D)≤ spatialCloseScale D b ∧
      (1/(2744*A))*D≤1/(1372*(α/D)) := by
  have hr := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).eventually (eventually_ge_atTop (12*A/b))
  filter_upwards [eventually_ge_atTop (max 1 (8192*A)),hr] with D hD hr
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hD)
  have hbD : 12*A≤b*D^(2/3:ℝ) := by
    have hh := (div_le_iff₀ hb).mp hr
    nlinarith
  have h8192 : 8192*A≤D := (le_max_right _ _).trans hD
  intro α hα hαA
  refine ⟨(div_le_iff₀ hDp).mpr (by nlinarith),?_,?_⟩
  · rw [←mul_div_assoc]
    apply (div_le_iff₀ hDp).mpr
    have he : (spatialCloseScale D b)*D=b*D^(2/3:ℝ) := by
      unfold spatialCloseScale
      rw [mul_assoc]
      conv_lhs => arg 2; arg 2; rw [←Real.rpow_one D]
      rw [←Real.rpow_add hDp]
      norm_num
    rw [he]
    nlinarith
  · have hh : (1372*(α/D))>0 := by positivity
    apply (le_div_iff₀ hh).mpr
    have he : 1/(2744*A)*D*(1372*(α/D))=α/(2*A) := by field_simp; ring
    rw [he]
    exact (div_le_one (by positivity : 0<2*A)).mpr hαA

theorem physical_uniform_phase_error {A c : ℝ} (hA : 2≤A) (hc : 0<c) :
    ∃D₀ : ℝ,1≤D₀ ∧ ∃K₀ : ℕ,100≤K₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),K₀≤K →
    ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    Phase.modulusOccupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume-c/2≤
      Phase.occupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  have hAp : 0<A := by linarith
  obtain ⟨Q,hQ,htail⟩ := physical_geometry_error
  let θ := 1/(2744*A)
  have hθ : 0<θ := by dsimp only [θ]; positivity
  obtain ⟨b,H,hb,hb1,hH,hlim,hfin⟩ := htail θ hθ
  let p := fun D : ℝ ↦ ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))
  obtain ⟨Ds,hDs,hfin⟩ := hfin (2*A)
  have herror : Tendsto (fun D : ℝ ↦ 1029*(2*A)^2/D+128*(2^27:ℝ)*p D) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x:=1029*(2*A)^2)).div_atTop (tendsto_id (α:=ℝ))).add (hlim.const_mul (128*(2^27:ℝ)))
    simpa only [mul_zero,add_zero,p,id_eq] using hh
  have hlarge := (geometry_scale_eventually hAp hb).and
    ((herror.eventually (gt_mem_nhds (by positivity : (0:ℝ)<c^2/128))).and
      (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/(16*2^27)))))
  obtain ⟨De,hDe⟩ := eventually_atTop.mp hlarge
  have hKlim := tendsto_pow_const_mul_const_pow_of_lt_one 3 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨Ke,hKe⟩ := eventually_atTop.mp (hKlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<c^2/128)))
  refine ⟨max Ds De,hDs.trans (le_max_left _ _),max 100 Ke,le_max_left _ _,?_⟩
  intro N K instK L hL hK D α hDeq hD hαlo hαhi ψ hψ
  have hDsD := (le_max_left Ds De).trans hD
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hDs.trans hDsD)
  have hα : 1≤α := by linarith
  have hp : 0≤p D := Real.rpow_nonneg (by positivity) _
  obtain ⟨hscale,herr,hpD⟩ := hDe D ((le_max_right Ds De).trans hD)
  obtain ⟨hr,hsep,hθD⟩ := hscale α (by linarith) hαhi
  have h100 : 100≤L.val := by rw [hL]; exact_mod_cast (le_max_left 100 Ke).trans hK
  have hnum : 8*(2^27:ℝ)*p D≤1/2 := by linarith
  have hgeom := hfin hL h100 D α hDeq hDsD hα hαhi hr hsep hθD ψ hψ hnum
  let loss := (∫Y,(volume : Measure (Torus L)).real (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))/L.val^3
  have hfirst : 1029*α^2/D≤1029*(2*A)^2/D := by gcongr
  have hlast : (K:ℝ)^3*((2^27:ℝ)*p D)^K≤(K:ℝ)^3*(1/2:ℝ)^K := by
    gcongr
    linarith
  have hKerr := hKe K ((le_max_right 100 Ke).trans hK)
  have hloss : loss≤c^2/64 := by change loss≤_ at hgeom; linarith
  have hsqrt : Real.sqrt loss≤c/8 := by
    apply (Real.sqrt_le_left (by positivity : 0≤c/8)).mpr
    nlinarith
  have hphase := ground_physical_phase_transfer hψ ((microMesh_bounds (by positivity : 0<α/D) (by linarith : α/D≤1)).1)
  dsimp only [loss] at hsqrt
  linarith

end HardSphere
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
attribute [local instance] Classical.propDecidable

lemma occupation_eq_phase {n : ℕ} {L : Length} (f : ScalarL2 (n+1) L) :
    occupation (Nat.zero_lt_succ n) f=
      Phase.occupation (fun p : Configuration n L×Torus L ↦ f (Fin.cons p.2 p.1)) volume volume := by
  have hLp := L.property
  unfold occupation Phase.occupation
  rw [Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity)]
  simp only [div_eq_mul_inv,mul_comm]
  rfl

theorem physical_scaled_occupation :
    ∃A c D₀ : ℝ,2≤A ∧ 0<c ∧ 1≤D₀ ∧ ∃K₀ : ℕ,400≤K₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀hN : 2≤N,∀hL : L.val=(K:ℝ),K₀≤K →
    ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ →
      c≤occupation (lt_of_lt_of_le (by decide : 0<2) hN) ψ.1 := by
  obtain ⟨A,c,Dm,hA,hc,hDm,Km,hKm,hmod⟩ := Groups.physical_uniform_modulus
  obtain ⟨Dp,hDp,Kp,hKp,hphase⟩ := physical_uniform_phase_error hA hc
  refine ⟨A,c/2,max Dm Dp,hA,by positivity,hDm.trans (le_max_left _ _),
    max Km Kp,hKm.trans (le_max_left _ _),?_⟩
  intro N K instK L hN hL hK D α hDeq hD hlo hhi ψ hψ
  cases N with
  | zero => omega
  | succ n =>
    have hn : 0<n := by omega
    have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.mpr hN
    have hm := hmod hL ((le_max_left Km Kp).trans hK) D α
      (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq)
      ((le_max_left Dm Dp).trans hD) hlo hhi ψ hψ
    have hp := hphase hL ((le_max_right Km Kp).trans hK) D α
      (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq)
      ((le_max_right Dm Dp).trans hD) hlo hhi ψ hψ
    rw [occupation_eq_phase]
    linarith

end HardSphere
end
end

end OAI
