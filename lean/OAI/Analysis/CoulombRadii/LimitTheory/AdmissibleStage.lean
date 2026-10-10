import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.TailFinish

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem admissible_profile_stages {Zbar : ℝ → ℕ} {s : ℕ → ℝ} {N : ℕ → ℕ}
    (had : Admissible Zbar s N) (ε : ℝ) (Cq sq : ℕ → ℝ) (hsq : ∀ k,0 < sq k) :
    ∃ k : ℕ → ℕ,Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      0 < s n ∧ s n < sq (k n) ∧ Zbar (s n) ≤ N n+1 ∧
      Cq (k n)*s n^25 ≤ (((k n+2:ℕ):ℝ))⁻¹ ∧
      initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n ≤ (((k n+2:ℕ):ℝ))⁻¹ := by
  have hc : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0) := by
    simpa only [initialAtomicRadius,Nat.cast_add,Nat.cast_one] using nuclear_clamp_tendsto
      (Eventually.of_forall (fun n => (by positivity : (0:ℝ)<(N n+1:ℝ)))) had.1 had.2.2.2 ε
  apply slow_stages (P:=fun k n =>
    0 < s n ∧ s n < sq k ∧ Zbar (s n) ≤ N n+1 ∧
    Cq k*s n^25 ≤ (((k+2:ℕ):ℝ))⁻¹ ∧
    initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n ≤ (((k+2:ℕ):ℝ))⁻¹)
  intro k
  have HK : 0 < (((k+2:ℕ):ℝ))⁻¹ := by positivity
  have Hp : Tendsto (fun n => Cq k*s n^25) atTop (𝓝 0) := by simpa using (had.2.1.pow 25).const_mul (Cq k)
  filter_upwards [had.1,had.2.1.eventually_lt_const (hsq k),had.2.2.1,
    Hp.eventually_lt_const HK,hc.eventually_lt_const HK] with n hs hsq hZ hp hc
  exact ⟨hs,hsq,hZ,hp.le,hc.le⟩

lemma shifted_stage_tendsto {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (K : ℕ) :
    Tendsto (fun n => k (n+K)+2) atTop atTop := by
  exact (tendsto_add_atTop_nat 2).comp (hk.comp (tendsto_add_atTop_nat K))
end NeutralAtom
end

end
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem physical_expected_exterior_asymptotic : ∃ Zbar : ℝ → ℕ,ExpectedExteriorAsymptotic Zbar := by
  obtain ⟨ε,B,C,L,M,hε,hB,hM,Zbar,Hdata⟩ := physical_profile_constants
  have HG := fun k : ℕ => Hdata ((k+2:ℕ):ℝ) (by exact_mod_cast (show 2 ≤ k+2 by omega))
  choose Cq hCq sq hsq HD using HG
  refine ⟨Zbar,?_⟩
  intro s N had ψ hψ a ha
  let : ∀ n,IsProbabilityMeasure (rawLaw (ψ n)) := fun n =>
    rawLaw_isProbability (hψ n).choose_spec.1.2.2.1 (hψ n).choose_spec.2.1
  obtain ⟨k,hk,hgood⟩ := admissible_profile_stages had ε Cq sq hsq
  obtain ⟨K,hK⟩ := eventually_atTop.mp hgood
  have Hstage (n : ℕ) := hK (n+K) (Nat.le_add_left K n)
  let s' := fun n => s (n+K)
  let N' := fun n => N (n+K)
  let ψ' := fun n => ψ (n+K)
  let q := fun n => k (n+K)+2
  let Cq' := fun n => Cq (k (n+K))
  have hsp : ∀ n,0 < s' n := fun n => (Hstage n).1
  have hs : Tendsto s' atTop (𝓝 0) := had.2.1.comp (tendsto_add_atTop_nat K)
  have hz : Tendsto (fun n => N' n+1) atTop atTop := had.charge_tendsto.comp (tendsto_add_atTop_nat K)
  have hq : Tendsto q atTop atTop := shifted_stage_tendsto hk K
  have hpr : ∀ n,0 < initialAtomicRadius ε ((N' n+1:ℕ):ℝ) :=
    fun n => initialAtomicRadius_pos hε (by positivity)
  have hr : Tendsto (fun n => initialAtomicRadius ε ((N' n+1:ℕ):ℝ)/s' n) atTop (𝓝 0) := by
    have HR : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0) := by
      simpa only [initialAtomicRadius,Nat.cast_add,Nat.cast_one] using nuclear_clamp_tendsto
        (Eventually.of_forall (fun n => (by positivity : (0:ℝ)<(N n+1:ℝ)))) had.1 had.2.2.2 ε
    exact HR.comp (tendsto_add_atTop_nat K)
  have hdn (n : ℕ) : Nonempty (QuantumProfileDatum (ψ' n) ε B C L M (s' n) (q n:ℝ) (Cq' n)) :=
    HD (k (n+K)) (ψ (n+K)) (hψ (n+K)) (s (n+K)) (Hstage n).1 (Hstage n).2.1
      (Hstage n).2.2.1 (Hstage n).2.2.2.2
  let d := fun n => Classical.choice (hdn n)
  have hp : ∀ n,Cq' n*s' n^25 ≤ (q n:ℝ)⁻¹ := fun n => (Hstage n).2.2.2.1
  have hpacket (a b : ℝ) (ha : 0 < a) (hab : a < b) := quantum_profile_packet_limit
    N' ψ' (fun n => hψ (n+K)) hε hB hM s' hsp hs hz hr q hq Cq' d hp ha hab
  have hann (a b : ℝ) (ha : 0 < a) (hab : a < b) := expected_raw_annulus_of_packets
    (fun n => N' n+1) (fun n => rawLaw (ψ' n)) Coulomb.unitWindow Coulomb.unitWindow.continuous
    Coulomb.unitWindow_mass Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) ha hab
    (Eventually.of_forall hsp) (Eventually.of_forall hpr) hs hr hpacket
  have htail := expected_exterior_of_raw_annuli physical_uniform_count_control s' N' ψ'
    (fun n => hψ (n+K)) hsp hs hz hann ha
  apply (tendsto_add_atTop_iff_nat K).mp
  simpa only [s',N',ψ',bTF_cube] using htail
end NeutralAtom
end

end

end OAI
