import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalSupply
import OAI.Analysis.HardSphere.Allocation.CertificateWindow

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma source_boundary_eq {D t : ℝ} (hD : 0<D) (ht : 0<t) (hh : D⁻¹<2*t)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    prefixTime midpointTime w=splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hh) := by
  apply Subtype.ext
  change (1/2:ℝ)*(w:ℝ)=D⁻¹/(D⁻¹+(2*t-D⁻¹))
  rw [show D⁻¹+(2*t-D⁻¹)=2*t by ring]
  apply (eq_div_iff (by positivity : (2*t)≠0)).mpr
  nlinarith

theorem physical_ground_bad_supply :
    ∃A ell b H t₀ : ℝ,2≤A ∧ 0<ell ∧ 0<b ∧ 0<H ∧ 0<t₀ ∧
    ∀t : ℝ,0<t → t≤t₀ → ∀p : ℝ,0<p → p≤1 →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀{N K q G : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length},
    ∀hL : L.val=(K:ℝ),100≤L.val → ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀w : Time,t*(w:ℝ)=D⁻¹ → (G*(2*q):ℝ)≤ell*D/2 →
    ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ → ∀g : Fin G,∀T : Finset (Fin 3→Fin K),
      physicalDatumLaw g ψ (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ))
        (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (2*t) (prefixTime midpointTime w)
        {d : PhysicalDatum N K (2*q) G L | T⊆datumBad hL g (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊)
          t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (prefixTime midpointTime w) d}≤
        (6*ENNReal.ofReal p+ENNReal.ofReal ((2/5:ℝ)^q))^T.card := by
  obtain ⟨A,ell,hA2,hell,hcert⟩ := ground_certificate_supply_ge_two
  have hA : 0<A := by linarith
  obtain ⟨b,H,tc,hb,hb4,hH,htc,hcert⟩ := hcert (ell/12) (by positivity)
  obtain ⟨ts,hts,hsupply⟩ := canonical_supply_counts hell hb (by positivity : 0<A/2) (by positivity : 0<2*A) hH
  refine ⟨A,ell,b,H,min tc ts,hA2,hell,hb,hH,lt_min htc hts,?_⟩
  intro t ht htt p hp hp1
  obtain ⟨Dc,hDc,hcert⟩ := hcert p hp hp1 t ht (htt.trans (min_le_left _ _))
  obtain ⟨Ds,hDs,hsupply⟩ := hsupply t ht (htt.trans (min_le_right _ _))
  refine ⟨max Dc Ds,hDc.trans (le_max_left _ _),?_⟩
  intro N K q G instN instK L hL h100 D α hDeq hD hαlo hαhi w hw hG ψ hψ g T
  have hDDc := (le_max_left Dc Ds).trans hD
  have hDDs := (le_max_right Dc Ds).trans hD
  obtain ⟨hDp,hh,hcert⟩ := hcert N K L hL D α h100 hDeq hDDc hαlo hαhi
  have hwindow := source_boundary_eq hDp ht hh w hw
  let C := 64*(meanCost+1)
  have hC : meanCost+1≤C := by dsimp [C]; nlinarith [meanCost_nonneg]
  have hjoint : ∀T : Finset (Fin 3→Fin K),
      groundPathLaw N L (α/D) (2*t) ψ {ω | ∀v∈T,¬Certificate
        (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω}≤
      (6*ENNReal.ofReal p)^T.card := by
    intro T
    refine (measure_mono ?_).trans (hcert ψ hψ T)
    intro ω hω v hv hc
    apply hω v hv
    have hc' := certificate_mono_constants le_rfl hC hc
    rw [←hwindow] at hc'
    simpa only [sourceMesh,two_mul,spatialCloseScale] using hc'
  have hcounts (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
      (hc : Certificate (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω) :=
    hsupply D α hDDs hαlo hαhi N K ⌈t/(α/D)^2⌉₊ L (by linarith) rfl w hw (ell/12) (by linarith) v ω hc
  have hcfull (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
      (hc : Certificate (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω) :
      G*(2*q)≤(eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω).card ∧
      10*((eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω)∩
        fullFailure ⌈t/(α/D)^2⌉₊ t (α/D) (D^(1/12:ℝ)) C (b*D^(-(1/3):ℝ)/8) w v ω).card≤
        (eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω).card := by
    obtain ⟨hlo,hbad⟩ := hcounts v ω hc
    refine ⟨?_,hbad⟩
    exact_mod_cast hG.trans hlo
  let := hψ.groundPathLaw_probability (by linarith : 0≤2*t)
  exact physical_bad_joint_of_certified_counts hL g ⌈t/(α/D)^2⌉₊ t (α/D) (D^(1/12:ℝ)) C
    (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D w
    (groundPathLaw N L (α/D) (2*t) ψ) (6*ENNReal.ofReal p) hjoint hcfull T

end HardSphere.Groups
end
end

end OAI
