import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorDataMeasurable
import OAI.Analysis.CoulombRadii.Packets.MasterTruncatedCap

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def physicalFieldCapUnit : ℝ :=
  2*Coulomb.atomicBudgetRecursionC^2*Real.sqrt Coulomb.atomicCountConstant*100000^4
lemma physicalFieldCapUnit_pos : 0 < physicalFieldCapUnit := by
  have h : 0 < Coulomb.atomicBudgetRecursionC := lt_of_lt_of_le (by norm_num) Coulomb.atomicBudgetRecursionC_ge_four
  have hP : 0 < Coulomb.atomicCountConstant := lt_of_lt_of_le (by norm_num) Coulomb.atomicCountConstant_ge_two
  unfold physicalFieldCapUnit
  positivity

lemma scaled_screen_field {a δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (_ : 0 ≤ δ) :
    (100000*a)^4*(2*Coulomb.atomicBudgetRecursionC^2*
      Coulomb.screenFieldUnit δ Coulomb.atomicCountConstant a)=
    physicalFieldCapUnit*(1+Real.sqrt (δ*a^7)) := by
  have hpow : a^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hinv : 1 ≤ (a^3)⁻¹ := (one_le_inv₀ (pow_pos ha 3)).mpr hpow
  have hsqrt : Real.sqrt (δ*a^7)=a^3*Real.sqrt (δ*a) := by
    rw [show δ*a^7=(a^3)^2*(δ*a) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (pow_nonneg ha.le 3)]
  unfold Coulomb.screenFieldUnit Coulomb.screenMass Coulomb.screenBaseMass physicalFieldCapUnit
  rw [max_eq_left hinv,hsqrt]
  field_simp [ha.ne']

lemma scaled_screen_field_log {a D Q : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hDa : D*a^7 ≤ 1) :
    (100000*a)^4*(2*Coulomb.atomicBudgetRecursionC^2*
      Coulomb.screenFieldUnit (D+Q) Coulomb.atomicCountConstant a) ≤
    2*physicalFieldCapUnit+physicalFieldCapUnit*Real.sqrt (Q*a^7) := by
  rw [scaled_screen_field ha ha1 (add_nonneg hD hQ),add_mul]
  have hs : Real.sqrt (D*a^7+Q*a^7) ≤ 1+Real.sqrt (Q*a^7) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (mul_nonneg hQ (pow_nonneg ha.le 7)),Real.sqrt_nonneg (Q*a^7)]
  have hC := physicalFieldCapUnit_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hs hC]

lemma cap_square_of_mean {b C Q a : ℝ} (_ : 0 ≤ C) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hb : 2*C ≤ b) (hh : b ≤ 2*C+C*Real.sqrt (Q*a^7)) :
    (b-2*C)^2 ≤ C^2*Q*a^7 := by
  have ht : 0 ≤ b-2*C := by linarith
  have hle : b-2*C ≤ C*Real.sqrt (Q*a^7) := by linarith
  have H := pow_le_pow_left₀ ht hle 2
  rw [mul_pow,Real.sq_sqrt (mul_nonneg hQ (pow_nonneg ha 7))] at H
  nlinarith only [H]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_field_tail (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h)
    {E D : ℝ} (hE : (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g ≤ E+D) (hD : 0 ≤ D)
    (r : Fin J → ℝ) (hr : ∀ k,0 < r k) (j : ℕ)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hy : y≠0) (ha1 : Coulomb.atomicCellScale y ≤ 1)
    (hDa : D*(Coulomb.atomicCellScale y)^7 ≤ 1)
    (hwidth : 2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y) :
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let f := fun z : ObservationSample n J => ‖y‖^4*((Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z)) y)
    ∀ {b : ℝ}, 2*physicalFieldCapUnit ≤ b → 0 < P.real {z | b < f z} →
      (b-2*physicalFieldCapUnit)^2 ≤
        (physicalFieldCapUnit^2*observationEventEnergyConstant*
          observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*
          (Coulomb.atomicCellScale y)^7)*(1-Real.log (P.real {z | b < f z}))^5 := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  intro b hb hp
  let P := observationLaw J (rawLaw ψ)
  let obs : ObservationSample n J → Fin J → UnorderedArray n := tailObservation r j
  let F := fun datum => (Z:ℝ)*coulombKernel y-
    potentialOf (conditionalPacketDensity P Prod.fst obs g₀ c r₀ s datum) y
  let B := {datum | b < ‖y‖^4*F datum}
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hF : Measurable F := measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst obs g₀.continuous hgs hm hc hr₀ hs y)
  have hB : MeasurableSet B := measurableSet_lt measurable_const (hF.const_mul _)
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn r hr j hB
  change 0 < P.real (obs ⁻¹' B) at hp
  have hp1 : P.real (obs ⁻¹' B) ≤ 1 := measureReal_le_one
  let p := P.real (obs ⁻¹' B)
  let Q := observationEventEnergyConstant*
    observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*(1-Real.log p)^5
  have hlog : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (observationWidthSquareSum_nonneg _)) (pow_nonneg hlog 5)
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (hr k.val) _)
    (hB.preimage (measurable_retainedTailObservation j))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp)
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u ≤ E+(D+Q) := by
    simpa only [←hpEq] using hue
  have Hcap := atomic_master_field_cap (Coulomb.atom Z hZ) (by intro i; rfl)
    u hu hum hE hue' (add_nonneg hD hQ) g₀ hm hrad hg hc hr₀ hs hscale y hy hwidth
  have Htower := retainedEvent_field_mean hd.2.2.1 hn r hr j hB u hum hlaw hp
    g₀.continuous hgs hm hc hr₀ hs y ((Z:ℝ)*coulombKernel y)
  have hatt : Coulomb.attraction (Coulomb.atom Z hZ) y=(Z:ℝ)*coulombKernel y := by
    simp [Coulomb.attraction,Coulomb.atom,Coulomb.coulombKernel,coulombKernel]
  rw [hatt,Htower] at Hcap
  have hfi : Integrable (fun z => F (obs z)) P :=
    (integrable_const _).sub (conditionalPacketPotential_integrable P (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation r j) g₀.continuous hgs hm hc hr₀ hs y)
  have Hlow := le_normalized_event (hB.preimage (measurable_tailObservation r j))
    (hfi.const_mul (‖y‖^4)) hp (v:=b)
    (Eventually.of_forall (fun z hz => (show b < ‖y‖^4*F (obs z) from hz).le))
  rw [integral_const_mul] at Hlow
  have Hs := mul_le_mul_of_nonneg_left Hcap (pow_nonneg (norm_nonneg y) 4)
  have he : ‖y‖=100000*Coulomb.atomicCellScale y := by unfold Coulomb.atomicCellScale; ring
  have Hlog := scaled_screen_field_log (Coulomb.atomicCellScale_pos hy) ha1 hD hQ hDa
  rw [←he] at Hlog
  have hb' : b ≤ 2*physicalFieldCapUnit+physicalFieldCapUnit*Real.sqrt (Q*(Coulomb.atomicCellScale y)^7) := by
    exact (Hlow.trans (by simpa only [mul_left_comm] using Hs)).trans Hlog
  have H := cap_square_of_mean physicalFieldCapUnit_pos.le hQ
    (Coulomb.atomicCellScale_pos hy).le hb hb'
  convert H using 1
  dsimp [Q,p,P,obs,B,F]
  ring
end NeutralAtom
end

end

end OAI
