import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationSmallScale
import OAI.Analysis.CoulombRadii.FormDomain.RawAnnularMoment
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorShellError

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma shell_error_numeric {C K D r m p : ℝ} (hC : 0≤C) (hK : 0≤K) (hD : 0≤D)
    (hr : 0<r) (hr1 : r≤1) (hDr : D*r^7≤1)
    (hm : m≤C*(Coulomb.screenMass D r)^2) (hp : p≤K*r^24) :
    Real.sqrt m*Real.sqrt p≤2*Real.sqrt C*Real.sqrt K*r^9 := by
  have hM : Real.sqrt m≤2*Real.sqrt C/r^3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hm.trans ?_⟩
    have H := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Coulomb.screenMass_pos D r).le (screenMass_small_offset hr hr1 hD hDr) 2) hC
    apply H.trans_eq
    field_simp
    nlinarith [Real.sq_sqrt hC]
  have hP : Real.sqrt p≤Real.sqrt K*r^12 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hp.trans_eq ?_⟩
    rw [mul_pow,Real.sq_sqrt hK,←pow_mul]
  calc
    _≤(2*Real.sqrt C/r^3)*(Real.sqrt K*r^12) :=
      mul_le_mul hM hP (Real.sqrt_nonneg p) (by positivity)
    _=_ := by field_simp

lemma physical_bad_shell_error : ∃ C : ℝ,0≤C ∧
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    ∀ {E D : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → 0≤D →
    ∀ {g₀ : Position → ℝ},Continuous g₀ → (∫ y,g₀ y^2)=1 → (∀ y,1<‖y‖ → g₀ y=0) →
    ∀ {c r₀ s r K : ℝ},0<c → 0<r₀ → 0<s → r₀≤r → r≤1 → D*r^7≤1 →
    c*s^packetExponent≤1/4 → 0≤K →
    ∀ (rads : Fin J → ℝ) (j : ℕ),
    ∀ {Bad : Set (ObservationSample n J)},MeasurableSet[observationSigma rads j] Bad →
    (observationLaw J (rawLaw ψ)).real Bad≤K*r^24 →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ o in Bad,∫ y in {y : Position | r≤‖y‖ ∧ ‖y‖<2*r},
      conditionalPacketDensity P Prod.fst (tailObservation rads j) g₀ c r₀ s (tailObservation rads j o) y ∂volume ∂P)≤
      C*Real.sqrt K*r^9 := by
  obtain ⟨C,hC,HC⟩ := atomic_raw_annular_second_moment (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<4)
  refine ⟨2*Real.sqrt C,by positivity,?_⟩
  intro n J Z hZ ψ g hd hn E D hE he hD g₀ hg hm hgs c r₀ s r K hc hr₀ hs hrr hr1 hDr hq hK rads j Bad hBad hp
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  have hr : 0<r := hr₀.trans_le hrr
  have hT : MeasurableSet {y : Position | r/2<‖y‖ ∧ ‖y‖<4*r} :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have H := conditional_packet_event_bound (observationLaw J (rawLaw ψ)) (rawLaw ψ)
    (observationLaw_rawProjection (J:=J) (rawLaw ψ)) (measurable_tailObservation rads j) hg hm hc hr₀ hs
    {y : Position | r≤‖y‖ ∧ ‖y‖<2*r} {y : Position | r/2<‖y‖ ∧ ‖y‖<4*r} hT
    (fun z y hy hk => packet_shell_center hgs hc hr₀ hs hrr hq hy hk) hBad
  apply H.trans
  apply shell_error_numeric hC hK hD hr hr1 hDr _ hp
  simpa only [one_div_mul_eq_div] using HC Z hZ hd hn hE he hD hr
end NeutralAtom

end

end

end OAI
