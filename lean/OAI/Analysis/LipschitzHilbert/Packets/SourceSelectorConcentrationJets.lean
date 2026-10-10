import OAI.Analysis.LipschitzHilbert.Trees.SourceMixedReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceThreshold

namespace OAI

/-! Unmasked reference moments for all three original covariant jets.
Only the synthesis waves change. The frozen original analyzing
coefficient and its proved local budget are retained exactly. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

/-- All raw jets have the same lattice and fixed envelope constant. -/
def rawJetFamily (i : Fin 3) : PlanarPacketFamily N κ ι :=
  { P.family with
    wave := P.raw i
    wave_measurable := fun j u k =>
      (modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
        (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale
        (P.length_pos j).ne' i).measurable
    wave_bound := fun j u k y x => by
      simpa only [family,zero_add,length] using P.raw_bound_three i j u k y x }

theorem rawJetFamily_derivative (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv ((P.rawJetFamily i).wave j u k y) x‖ ≤
      ((P.rawJetFamily i).constant/(P.rawJetFamily i).length j)*
        (lineEnvelope ((P.rawJetFamily i).centerX j u) ((P.rawJetFamily i).length j) 3 x*
          lineEnvelope ((P.rawJetFamily i).centerZ j u) P.width 2 y) := by
  apply (P.raw_derivative_bound i j u k y x).trans
  change _ ≤ (P.constant/P.length j)*_
  change _ ≤ (P.constant/P.length j)*
    (lineEnvelope (P.family.centerX j u) (P.length j) 3 x*
      lineEnvelope (P.family.centerZ j u) P.width 2 y)
  rw [P.family_centerX,P.family_centerZ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
  exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
    (lineEnvelope_antitone _ _ _ (Nat.le_trans (by decide : 2 ≤ 3) P.order_ge_three))
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

/-- The same exact horizontal normalization used for the zeroth jet. -/
theorem rawJetFamily_reference_derivative (i : Fin 3)
    (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    let Q := (P.rawJetFamily i).horizontalRescale P.topLength P.topLength_pos
    ‖deriv (Q.wave j u k y) x‖ ≤ (Q.constant/Q.length j)*
      (lineEnvelope (Q.centerX j u) (Q.length j) 3 x*
        lineEnvelope (Q.centerZ j u) P.width 2 y) := by
  dsimp only
  change ‖deriv (schwartzDilation ((P.rawJetFamily i).wave j u k y) P.topLength P.topLength_pos.ne') x‖ ≤ _
  rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.topLength_pos]
  rw [PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
    PlanarPacketFamily.horizontalRescale_centerZ,
    lineEnvelope_horizontalDilation _ _ P.topLength _ _ P.topLength_pos.ne']
  have h := mul_le_mul_of_nonneg_left (P.rawJetFamily_derivative i j u k y (P.topLength*x))
    P.topLength_pos.le
  convert h using 1
  change (P.constant/(P.length j/P.topLength))*_ = P.topLength*((P.constant/P.length j)*_)
  field_simp [(P.length_pos j).ne',P.topLength_pos.ne']

variable (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def mixedReferenceJetLine (i : Fin 3) (y : ℝ) : LinePacketFamily N κ ι :=
  let A := (P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y
  let R := ((P.withProfile alt hAlt).rawJetFamily i).horizontalRescale P.topLength P.topLength_pos
  let S := R.analyzedLine d
    (fun z => v (z.1,P.topLength*z.2))
    (hv.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun z => g (z.1,P.topLength*z.2))
    (hg.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun _ => hg1 _) y
    (fun j u k x => (P.withProfile alt hAlt).rawJetFamily_reference_derivative i j u k y x)
  { S with coeff := A.coeff, coeff_norm := A.coeff_norm }

@[simp] theorem mixedReferenceJetLine_coeff (i : Fin 3) (y : ℝ) (j : Fin N) (u : ι j) :
    (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  (P.frozenProfile c hc).referenceAnalyzedLine_coeff d v hv g hg hg1 y j u

@[simp] theorem mixedReferenceJetLine_wave (i : Fin 3) (y : ℝ)
    (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).wave j u k x =
      (P.withProfile alt hAlt).raw i j u k y (P.topLength*x) := rfl

theorem mixedReferenceJetLine_budget_iff (i : Fin 3) (y B : ℝ) :
    (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).HasLocalBudget B ↔
      ((P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y).HasLocalBudget B :=
  Iff.rfl

/-- Actual unmasked synthesis with the original frozen analyzing
 coefficient and the requested covariant jet. -/
def mixedReferenceJetBand (i : Fin 3) (j : Fin N) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k*
      (P.withProfile alt hAlt).raw i j u k y x)

theorem mixedReferenceJetLine_partial (i : Fin 3) (y x : ℝ) (n : ℕ) :
    hilbertPartialBandSum (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).packets n x =
      (P.constant*Real.pi^2)⁻¹ • packetPartialSum
        (fun j => P.mixedReferenceJetBand c hc alt hAlt d v g i j y (P.topLength*x)) n := by
  ext k
  simp only [hilbertPartialBandSum,partialBandSum,packetPartialSum,
    LinePacketFamily.packets,packetSynthesis_apply,mixedReferenceJetBand,
    WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [P.mixedReferenceJetLine_coeff,P.mixedReferenceJetLine_wave,PiLp.smul_apply]
    simp only [Complex.real_smul]
    ring
  · simp only [ite_eq_right hj,WithLp.ofLp_zero,Pi.zero_apply,smul_zero]

theorem mixedReferenceJetBand_variation (i : Fin 3) (y x : ℝ) :
    cubicVariation (packetPartialSum
      (fun j => P.mixedReferenceJetBand c hc alt hAlt d v g i j y (P.topLength*x))) N =
      (P.constant*Real.pi^2)*
        (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).variation x := by
  have hD : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have heq : packetPartialSum (fun j =>
      P.mixedReferenceJetBand c hc alt hAlt d v g i j y (P.topLength*x)) =
      fun n => (P.constant*Real.pi^2) • hilbertPartialBandSum
        (P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y).packets n x := by
    funext n
    rw [P.mixedReferenceJetLine_partial c hc alt hAlt d v hv g hg hg1 i y x n,
      smul_smul,mul_inv_cancel₀ hD.ne',one_smul]
  rw [heq,LinePacketFamily.cubicVariation_smul_nonneg _ N _ hD.le]
  rfl

/-- The jet index changes neither the original analyzing budget nor
 the moment constant. Annuli are required for the actual jet waves. -/
theorem mixed_reference_jet_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
    ∀ (i : Fin 3),
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw i j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw i j u k y) xi = 0) →
    ∀ (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let Q := P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M P.constant (A/Real.pi^4) grid p*grid.lineMeasure univ := by
  obtain ⟨A,hA,hbudget⟩ := referenceAnalyzedLine_uniform_budget hL hlo hhi
  obtain ⟨M,hM,hvariation⟩ := LinePacketFamily.uniform_line_moment_of_supported hL hlo hhi
  refine ⟨A,M,hA,hM,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh i hSlow hShigh y grid hb hwidth p hp
  let Q := P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y
  have hB : 0 ≤ A/Real.pi^4 := div_nonneg hA.le (pow_nonneg Real.pi_pos.le _)
  have hQ : Q.HasLocalBudget (A/Real.pi^4) :=
    hbudget N κ ι (P.frozenProfile c hc) d v hv g hg hg1 hd hAlow hAhigh y
  have hlen (j : Fin N) : Q.length j = P.length j/P.topLength := by
    change (P.topLength/P.topLength)/(2:ℝ)^j.val = (P.topLength/(2:ℝ)^j.val)/P.topLength
    ring
  have hwidth' (j : Fin N) (u : ι j) : Q.length j ≤ grid.width := by
    rw [hlen]
    exact (div_le_iff₀ P.topLength_pos).mpr (by simpa only [mul_comm] using hwidth j u)
  have hl (j : Fin N) (u : ι j) (k : κ) (xi : ℝ) (hxi : |xi| < lo*(2:ℝ)^j.val) :
      𝓕 (Q.wave j u k) xi = 0 := by
    change 𝓕 (schwartzDilation ((P.withProfile alt hAlt).raw i j u k y)
      P.topLength P.topLength_pos.ne') xi = 0
    apply schwartzDilation_low _ P.topLength (lo*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hSlow j u k y eta
    convert heta using 1
    ring
  have hh (j : Fin N) (u : ι j) (k : κ) (xi : ℝ) (hxi : hi*(2:ℝ)^j.val < |xi|) :
      𝓕 (Q.wave j u k) xi = 0 := by
    change 𝓕 (schwartzDilation ((P.withProfile alt hAlt).raw i j u k y)
      P.topLength P.topLength_pos.ne') xi = 0
    apply schwartzDilation_high _ P.topLength (hi*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hShigh j u k y eta
    convert heta using 1
    ring
  exact hvariation N κ ι Q (A/Real.pi^4) hB hQ hl hh grid hb hwidth' p hp

/-- The same fixed lower bound on L works for every jet, packet family,
 reference height and binary grid. -/
theorem mixed_reference_jet_polynomial_tail (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (a J : ℝ) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^a →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
    ∀ (i : Fin 3),
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw i j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw i j u k y) xi = 0) →
    ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) →
      let Q := P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y
      grid.lineMeasure {x | L^(a+4) ≤ |Q.variation x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  obtain ⟨A,M,hA,hM,hm⟩ := mixed_reference_jet_uniform_moments hL hlo hhi
  have hB : 0 ≤ A/Real.pi^4 := by positivity
  filter_upwards [eventually_reference_thresholds M (A/Real.pi^4) a J hM.le hB ha hJ]
    with L hthreshold
  obtain ⟨n,hn,hdecay,_hT,hthreshold⟩ := hthreshold
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh i hSlow hShigh y grid hb hwidth
  let Q := P.mixedReferenceJetLine c hc alt hAlt d v hv g hg hg1 i y
  have hb' : 1 < grid.branching := by omega
  have hmoment := hm N κ ι P c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh i hSlow hShigh y grid hb' hwidth n (by positivity)
  have hbound := (hthreshold grid P.constant hb P.constant_pos.le hP).2
  have ht := (measure_mono (show {x | L^(a+4) ≤ |Q.variation x|} ⊆
      {x | 4*(lineMomentBase P.constant (M*P.constant^2*(A/Real.pi^4)+1)
        grid.branching*(n:ℝ)) ≤ |Q.variation x|} from
      fun _ hx => hbound.trans hx)).trans
    (reference_variation_tail grid.lineMeasure Q.variation Q.continuous_variation.measurable
      M P.constant (A/Real.pi^4) grid P.constant_pos.le n hn hmoment)
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact ht.trans (mul_le_mul' hdecay' le_rfl)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
