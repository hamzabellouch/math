import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.InverseDensityError
import OAI.Analysis.CoulombRadii.RadialBounds.PhysicalBarrierData
import OAI.Analysis.CoulombRadii.Propagation.RetainedGoodEvent
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralCountControl

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def profileRadius (ε : ℝ) (N j : ℕ) : ℝ := initialAtomicRadius ε ((N+1:ℕ):ℝ)*2^j

def profileDensity {N : ℕ} (ψ : Wavefunction (N+1)) [IsProbabilityMeasure (rawLaw ψ)]
    (ε s : ℝ) (j : ℕ) : ObservationSample (N+1) (j+1) → Position → ℝ :=
  let P := observationLaw (j+1) (rawLaw ψ)
  let rs := fun k : Fin (j+1) => profileRadius ε N k.val
  fun o => conditionalPacketDensity P Prod.fst (tailObservation rs j) Coulomb.unitWindow 1
    (initialAtomicRadius ε ((N+1:ℕ):ℝ)) s (tailObservation rs j o)

structure QuantumProfileDatum {N : ℕ} (ψ : Wavefunction (N+1)) [IsProbabilityMeasure (rawLaw ψ)]
    (ε B C L M s q Cq : ℝ) where
  j : ℕ
  low : s/(2*q) ≤ profileRadius ε N j
  high : profileRadius ε N j ≤ s/q
  datum : PropagationDatum (observationLaw (j+1) (rawLaw ψ)) B C (profileRadius ε N j)
    ((N+1:ℕ):ℝ) L (profileDensity ψ ε s j)
  G : Set (ObservationSample (N+1) (j+1))
  measurable : MeasurableSet G
  failure : (observationLaw (j+1) (rawLaw ψ)).real Gᶜ ≤ M*s^9+Cq*s^25
  valid : ∀ o∈G,PropagationInvariant B C (profileRadius ε N j) ((N+1:ℕ):ℝ) L
    (datum.offset o) (profileDensity ψ ε s j o) (datum.error o) ∧
    Integrable (datum.error o) ∧ (∫ x,datum.error o x) ≤ 1
  band : ∀ o∈G,∀ x,profileRadius ε N j ≤ ‖x‖ → ‖x‖ ≤ q*s →
    screenedField ((N+1:ℕ):ℝ) (profileDensity ψ ε s j o) x ≤ physicalSpatialCap/‖x‖^4 ∧
    |profileDensity ψ ε s j o x-tfDensityScalar (screenedField ((N+1:ℕ):ℝ)
      (profileDensity ψ ε s j o) x)| ≤ (q^8)⁻¹/‖x‖^6

lemma profile_band_coverage {s q r : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hl : s/(2*q) ≤ r) : q*s ≤ 4*q^2*r := by
  have hqpos : 0 < q := by linarith only [hq]
  have H := (div_le_iff₀ (by positivity : (0:ℝ)<2*q)).mp hl
  have H' := mul_le_mul_of_nonneg_left H hqpos.le
  have hr : 0 ≤ r := (div_pos hs (by positivity)).le.trans hl
  nlinarith only [H',sq_nonneg q,mul_nonneg (sq_nonneg q) hr]

theorem physical_profile_constants : ∃ ε B C L M : ℝ,0 < ε ∧ 0 < B ∧ 0 ≤ M ∧
    ∃ Zbar : ℝ → ℕ, ∀ q : ℝ,2 ≤ q → ∃ Cq : ℝ,0 < Cq ∧
      ∃ sq : ℝ,0 < sq ∧ ∀ {N : ℕ} (ψ : Wavefunction (N+1)),
        ∀ hψ : IsNormalizedGroundState (N+1) ψ, ∀ s : ℝ,0 < s → s < sq → Zbar s ≤ N+1 →
        initialAtomicRadius ε ((N+1:ℕ):ℝ)/s ≤ q⁻¹ →
         let := rawLaw_isProbability (hψ.choose_spec.1.2.2.1)
          (hψ.choose_spec.2.1)
        Nonempty (QuantumProfileDatum ψ ε B C L M s q Cq) := by
  obtain ⟨ε,B,C,L,M,hε,hB,hC,hM,HB⟩ := physical_barrier_data
  obtain ⟨D,hD,Zmin,Henergy⟩ := physical_neutral_energy_offset
  obtain ⟨sB,hsB,hsB1,HB⟩ := HB D hD
  choose ZB HZB using HB
  let Zbar := fun s => max Zmin (if H : 0 < s ∧ s < sB then ZB s H.1 H.2 else 0)
  refine ⟨ε,B,C,L,M,hε,hB,hM,Zbar,?_⟩
  intro q hq
  obtain ⟨Cq,hCq,Hinv⟩ := physical_tf_band hq
  obtain ⟨sI,hsI,hsI1,Hinv⟩ := Hinv D hD
  refine ⟨Cq,hCq,min sB sI,lt_min hsB hsI,?_⟩
  intro N ψ hψ s hs hss hZbar hsmall
  have hZm : Zmin ≤ N+1 := (le_max_left ..).trans hZbar
  have hsBs : s < sB := hss.trans_le (min_le_left ..)
  have hsIs : s < sI := hss.trans_le (min_le_right ..)
  have hZB : ZB s hs hsBs ≤ N+1 := by
    have H := (le_max_right Zmin _).trans hZbar
    simpa only [Zbar,dite_eq_left (show 0 < s ∧ s < sB from ⟨hs,hsBs⟩)] using H
  obtain ⟨g,hd,hn,hmin⟩ := hψ
  have := rawLaw_isProbability hd.2.2.1 hn
  have hZ : 1 ≤ N+1 := by omega
  have hZpos : 0 < ((N+1:ℕ):ℝ) := by positivity
  have hr₀ := initialAtomicRadius_pos hε hZpos
  obtain ⟨j,hjl,hju⟩ := dyadic_radius_choice hr₀ hs (by linarith only [hq]) hsmall
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hrjs : profileRadius ε N j ≤ s := hju.trans ((div_le_self hs.le hq1))
  have he := Henergy (N+1) hZm hZ hd hn hmin
  have hE := Coulomb.atom_unrestricted_bottom_real (N+1) hZ
    (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) (asH1_antisymmetric hd) ((asH1_mass ..).trans hn)
  obtain ⟨d,hdcost⟩ := HZB s hs hsBs (N+1) hZB hZ hd hn hmin hE.le he
    (show (N+1:ℝ) ≤ 3*((N+1:ℕ):ℝ) by push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) N]) (K:=j+1) ⟨j,by omega⟩ hrjs
  obtain ⟨V,hV,hVp,HV⟩ := d.valid_event hdcost
  obtain ⟨G,hG,hGp,HG⟩ := Hinv (N+1) hZ hd hn hmin hE.le he hr₀ hs hsIs
    (J:=j+1) ⟨j,by omega⟩ hrjs
  refine ⟨⟨j,hjl,hju,d,V∩G,hV.inter hG,?_,?_,?_⟩⟩
  · rw [compl_inter]
    exact (measureReal_union_le Vᶜ Gᶜ).trans ((add_le_add hVp hGp).trans
      (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (mul_pos hr₀ (by positivity)).le hrjs 9) hM) le_rfl))
  · intro o ho
    exact HV o ho.1
  · intro o ho x hx hxq
    exact HG o ho.2 x hx (hxq.trans (profile_band_coverage hq hs hjl))
end NeutralAtom
end

end

end OAI
