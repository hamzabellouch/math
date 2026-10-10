import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPathWeight
import OAI.Analysis.HardSphere.Bridges.TorusLocalBridge
import OAI.Analysis.HardSphere.Geometry.LocalAE

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere
open Wiener

lemma IsGroundVector.ae_killed_zero_propagation {N : ℕ} {L : Length} {a t : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (ht : 0≤t) :
    ∀ᵐ ω ∂killedPathLaw N L a t, u.1 (ω 0)=0 → u.1 (ω 1)=0 := by
  let Z : Set (Configuration N L) := {X | u.1 X=0}
  have hZ : MeasurableSet Z := (Lp.stronglyMeasurable u.1).measurable (measurableSet_singleton 0)
  let f : Configuration N L → ℂ := Z.indicator (fun _ ↦ 1)
  have hf : MemLp f 2 volume := (memLp_const (1:ℂ)).indicator hZ
  let F : ScalarL2 N L := hf.toLp f
  have hF : F =ᵐ[volume] f := MemLp.coeFn_toLp hf
  have hInner : inner ℂ F (modulusScalar u.1)=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hF,coe_modulusScalar u.1] with X hX hM
    simp only [RCLike.inner_apply,hX,hM]
    by_cases hz : u.1 X=0
    · simp [hz]
    · simp [f,Z,hz]
  have hi := integrable_killed_endpoints N L a t F (modulusScalar u.1) 0 1
  have he : (∫ω, conj (F (ω 0))*modulusScalar u.1 (ω 1) ∂killedPathLaw N L a t)=0 := by
    rw [←killedTransition_pairing,show modulusScalar u.1=(modulusJet u).1 from rfl,
      hu.modulus.killed_eigenvector ht,inner_smul_right]
    change _ * inner ℂ F (modulusScalar u.1)=0
    rw [hInner,mul_zero]
  let g : ConfigurationPath N L → ℝ := fun ω ↦ if u.1 (ω 0)=0 then ‖u.1 (ω 1)‖ else 0
  have hg : (fun ω ↦ conj (F (ω 0))*modulusScalar u.1 (ω 1)) =ᵐ[killedPathLaw N L a t]
      fun ω ↦ (g ω:ℂ) := by
    filter_upwards [ae_restrict_of_ae ((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp hF),
      ae_restrict_of_ae ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp (coe_modulusScalar u.1))] with ω h0 h1
    dsimp only [Function.comp_def] at h0 h1
    rw [h0,h1]
    by_cases hz : u.1 (ω 0)=0 <;> simp [f,Z,g,hz]
  have hig : Integrable g (killedPathLaw N L a t) :=
    (Complex.reCLM.integrable_comp (hi.congr hg)).congr (Eventually.of_forall fun _ ↦ rfl)
  have heg : ∫ω,g ω ∂killedPathLaw N L a t=0 := by
    have hh := congrArg Complex.re ((integral_congr_ae hg).symm.trans he)
    exact (Complex.reCLM.integral_comp_comm (hi.congr hg)).trans hh
  have hgn : ∀ᵐ ω ∂killedPathLaw N L a t, 0≤g ω := ae_of_all _ (fun ω ↦ by dsimp [g]; split_ifs <;> positivity)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hgn hig).mp heg
  filter_upwards [hz] with ω hω h0
  have hn : ‖u.1 (ω 1)‖=0 := by simpa [g,h0] using hω
  exact norm_eq_zero.mp hn

def complexPhase (z : ℂ) : ℂ := z/(‖z‖:ℂ)

lemma complexPhase_eq_of_inner {z w : ℂ} (hz : z≠0) (hw : w≠0)
    (h : conj z*w=(‖z‖*‖w‖:ℝ)) : complexPhase z=complexPhase w := by
  have hnz : (‖z‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hnw : (‖w‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  apply (div_eq_div_iff hnz hnw).mpr
  have hh := congrArg (fun u : ℂ ↦ z*u) h
  rw [←mul_assoc,Complex.mul_conj',Complex.ofReal_mul] at hh
  apply mul_left_cancel₀ hnz
  calc
    (‖z‖:ℂ)*(z*(‖w‖:ℂ))=z*((‖z‖:ℂ)*(‖w‖:ℂ)) := by ring
    _ = (‖z‖:ℂ)^2*w := hh.symm
    _ = (‖z‖:ℂ)*(w*(‖z‖:ℂ)) := by ring

lemma complexPhase_mul_norm (z : ℂ) : complexPhase z*(‖z‖:ℂ)=z := by
  by_cases hz : z=0
  · simp [complexPhase,hz]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

lemma norm_complexPhase {z : ℂ} (hz : z≠0) : ‖complexPhase z‖=1 := by
  rw [complexPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr hz)

lemma inner_eq_of_complexPhase_eq {z w : ℂ} (h : complexPhase z=complexPhase w) :
    conj z*w=(‖z‖*‖w‖:ℝ) := by
  by_cases hz : z=0
  · simp [hz]
  by_cases hw : w=0
  · simp [hw]
  have hez := complexPhase_mul_norm z
  have hew := complexPhase_mul_norm w
  conv_lhs => rw [←hez,←hew,←h,map_mul]
  simp only [Complex.conj_ofReal]
  calc
    conj (complexPhase z)*(‖z‖:ℂ)*(complexPhase z*(‖w‖:ℂ))=
        (complexPhase z*conj (complexPhase z))*((‖z‖:ℂ)*(‖w‖:ℂ)) := by ring
    _ = _ := by rw [Complex.mul_conj',norm_complexPhase hz]; simp

lemma measurable_complexPhase : Measurable complexPhase := by unfold complexPhase; fun_prop

lemma IsGroundVector.ae_killed_complexPhase {N : ℕ} {L : Length} {a t : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (ht : 0≤t) :
    ∀ᵐ ω ∂killedPathLaw N L a t, complexPhase (u.1 (ω 0))=complexPhase (u.1 (ω 1)) := by
  have hrev := (reverse_killedPath_preserving N L a t).quasiMeasurePreserving.ae
    (hu.ae_killed_zero_propagation ht)
  filter_upwards [hu.ae_killed_zero_propagation ht,hu.ae_killed_endpoints_phase ht,hrev] with ω h0 hphase h1
  have hr : u.1 (ω 1)=0 → u.1 (ω 0)=0 := by simpa [reverseConfigurationPath] using h1
  by_cases hz : u.1 (ω 0)=0
  · rw [hz,h0 hz]
  · exact complexPhase_eq_of_inner hz (mt hr hz) hphase

end HardSphere

namespace HardSphere

lemma IsGroundVector.phase_region {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {x : Configuration N L} (hx : x∈allowed N L a) :
    ∃z, x∈LocalAE.region volume (fun y ↦ complexPhase (u.1 y)=z) := by
  have hm := measurable_complexPhase.comp (Lp.stronglyMeasurable u.1).measurable
  have hpm : MeasurableSet {p : Configuration N L×Configuration N L |
      complexPhase (u.1 p.1)=complexPhase (u.1 p.2)} :=
    measurableSet_eq_fun (hm.comp measurable_fst) (hm.comp measurable_snd)
  obtain ⟨U,hU,hxU,hsub,hp⟩ := killed_ae_torus_local_pairs L a (P:=fun X Y ↦ complexPhase (u.1 X)=complexPhase (u.1 Y)) hpm
    (fun t ht ↦ hu.ae_killed_complexPhase ht.le) hx
  obtain ⟨z,hz⟩ := LocalAE.ae_local_const_of_ae_pairs volume (hU.measure_ne_zero volume ⟨x,hxU⟩) hp
  exact ⟨z,U,hU,hxU,hz⟩

def groundPhaseRepresentative {N : ℕ} {L : Length} (u : Jet N L) : Configuration N L → ℂ :=
  LocalAE.representative volume (fun y ↦ complexPhase (u.1 y))

lemma IsGroundVector.ae_phaseRepresentative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) :
    ∀ᵐ x ∂volume.restrict (allowed N L a), complexPhase (u.1 x)=groundPhaseRepresentative u x :=
  LocalAE.representative_ae volume (isOpen_allowed N L a) (fun _ hx ↦ hu.phase_region hx)

lemma IsGroundVector.phaseRepresentative_eq_on_connected {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {S : Set (Configuration N L)} (hS : IsPreconnected S)
    (hsub : S⊆allowed N L a) {x y : Configuration N L} (hx : x∈S) (hy : y∈S) :
    groundPhaseRepresentative u x=groundPhaseRepresentative u y :=
  LocalAE.representative_eq_on_connected volume hS (fun _ hz ↦ hu.phase_region (hsub hz)) hx hy

end HardSphere

end

end OAI
