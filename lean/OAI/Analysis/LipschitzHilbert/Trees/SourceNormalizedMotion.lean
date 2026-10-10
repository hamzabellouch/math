import OAI.Analysis.LipschitzHilbert.Trees.SourceNormalizedDecay
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalPowerGain

namespace OAI

/-! Mass normalization of the proved physical amplitude power gain.
The local input is the raw physical motion, before multiplying by any
mass power or hierarchy transition. No normalized motion is assumed. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

/-- Both exact normalization coefficients have the smaller fixed power
gain, uniformly over the source phase and block parameters. -/
theorem eventually_source_normalization_coefficients (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw p μ : ℝ) (steps : ℕ) (Z : ℝ),
      1 ≤ Kw → 1 ≤ p → 0 ≤ μ → μ ≤ 1 →
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 →
      let G := SourceParameters.step L
      let δ := (5*D/Kw)/Real.sqrt G
      let es := (|-(1/p)|+|μ-1+1/p|)*δ
      let qs := Real.exp es*es
      let en := |μ-1| * δ
      let qn := Real.exp en*en
      let el := (steps:ℝ)*Z*(2*δ)
      let ql := Real.exp el*el
      let qt := qn+ql+qn*ql
      ((1+qs)*G^(-(1/4:ℝ))+qs*L^Q ≤ G^(-(1/8:ℝ))) ∧
      ((1+qt)*G^(-(1/4:ℝ))+qt*L^Q ≤ G^(-(1/8:ℝ))) := by
  have hs := eventually_source_mass_rescaling_error D hD
  have ht := eventually_source_transition_error D hD
  have hp := eventually_source_relative_product (20*D*Real.exp 1) 4 (by positivity)
  have hds := eventually_source_rescaled_motion (10*D*Real.exp 1) 0 Q (by positivity) hQ
  have hdt := eventually_source_rescaled_motion (3*(20*D*Real.exp 1)) 4 Q (by positivity) hQ
  filter_upwards [hs,ht,hp,hds,hdt,eventually_ge_atTop (1:ℝ)] with L hs ht hp hds hdt hL
  intro Kw p μ steps Z hKw hp1 hμ0 hμ1 hsteps hZ0 hZ
  dsimp only
  let G := SourceParameters.step L
  let δ := (5*D/Kw)/Real.sqrt G
  let en := |μ-1| * δ
  let qn := Real.exp en*en
  let el := (steps:ℝ)*Z*(2*δ)
  let ql := Real.exp el*el
  have hG : 0 < G := SourceParameters.step_pos L
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hqn0 : 0 ≤ qn := by dsimp [qn,en]; positivity
  have hql0 : 0 ≤ ql := by dsimp [ql,el]; positivity
  have hmu : |μ-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : en ≤ (|-(1/(1:ℝ))|+|μ-1+1/(1:ℝ)|)*δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    refine hmu.trans ?_
    have hb : (1:ℝ) ≤ 1+|μ-1+1/(1:ℝ)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    simpa only [div_one,abs_neg,abs_one] using hb
  have hqn : qn ≤ (10*D*Real.exp 1)/Real.sqrt G := by
    exact (mul_le_mul (Real.exp_le_exp.mpr he) he
      (by dsimp [en]; positivity) (Real.exp_pos _).le).trans
      (hs 1 μ Kw (by norm_num) hμ0 hμ1 hKw)
  have hL4 : (1:ℝ) ≤ L^4 := one_le_pow₀ hL
  have hqnPoly : qn ≤ (20*D*Real.exp 1)*L^4/Real.sqrt G := by
    apply hqn.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg G)
    have hx := mul_le_mul_of_nonneg_left hL4 (show 0 ≤ 20*D*Real.exp 1 by positivity)
    nlinarith [show 0 ≤ D*Real.exp 1 by positivity]
  have hqlPoly : ql ≤ (20*D*Real.exp 1)*L^4/Real.sqrt G :=
    ht steps Z Kw hsteps hZ0 hZ hKw
  have hprod := hp qn ql hqn0 hql0
    (by simpa only [Real.rpow_ofNat] using hqnPoly)
    (by simpa only [Real.rpow_ofNat] using hqlPoly)
  constructor
  · apply hds _ _ (L^Q) (by positivity) le_rfl (by positivity)
      (by simpa only [Real.rpow_zero,mul_one] using hs p μ Kw hp1 hμ0 hμ1 hKw)
      (by positivity) le_rfl
  · exact hdt _ _ (L^Q) (by positivity) le_rfl (by positivity) hprod
      (by positivity) le_rfl

/-- The source raw amplitude power gain, physical mass log motion and
actual transition quotient estimate imply both normalized motion bounds.
The raw bound is the conclusion of `source_physical_amplitude_power_gain`. -/
theorem eventually_source_normalized_motion
    (D Q : ℝ) (hD : 0 ≤ D) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (κ : Type) [Fintype κ],
    ∀ (Kw p μ n n' c c' : ℝ) (steps : ℕ) (Z : ℝ),
      1 ≤ Kw → 1 ≤ p → 0 ≤ μ → μ ≤ 1 →
      0 < n → 0 < n' → 0 < c → 0 < c' →
      (steps:ℝ) ≤ L^2 → 0 ≤ Z → Z ≤ 2*L^2 →
    ∀ (frequency : κ → ℝ) (b : ℝ) (A A' : EuclideanSpace ℂ κ) (lam lam' : ℂ),
      lam ≠ 0 → ‖lam‖ ≤ 1 →
      let G := SourceParameters.step L
      let δ := (5*D/Kw)/Real.sqrt G
      let el := (steps:ℝ)*Z*(2*δ)
      |Real.log n'-Real.log n| ≤ δ →
      |Real.log c'-Real.log c| ≤ δ →
      ‖A‖ ≤ L^Q*c →
      ‖A'-diagonalModulation frequency A b‖ ≤ G^(-(1/4:ℝ))*c →
      ‖lam'/lam-1‖ ≤ Real.exp el*el →
      (‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        diagonalModulation frequency (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ ≤
        G^(-(1/8:ℝ))*(c/n)^(1/p)*c^μ) ∧
      (‖((n'^(μ-1):ℝ):ℂ) • (lam' • A')-
        ((n^(μ-1):ℝ):ℂ) • (lam • diagonalModulation frequency A b)‖ ≤
        G^(-(1/8:ℝ))*n^μ*(c/n)) := by
  filter_upwards [eventually_source_normalization_coefficients D Q hD hQ,
    eventually_ge_atTop (1:ℝ)] with L hcoeff hL
  intro κ _ Kw p μ n n' c c' steps Z hKw hp hμ0 hμ1 hn hn' hc hc' hsteps hZ0 hZ
    frequency b A A' lam lam' hlam0 hlam
  dsimp only
  intro hN hchild hA hraw hlamMove
  let G := SourceParameters.step L
  let δ := (5*D/Kw)/Real.sqrt G
  let el := (steps:ℝ)*Z*(2*δ)
  let ql := Real.exp el*el
  have hG : 0 < G := SourceParameters.step_pos L
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hcoeff' := hcoeff Kw p μ steps Z hKw hp hμ0 hμ1 hsteps hZ0 hZ
  have hbase : ‖diagonalModulation frequency A b‖ ≤ L^Q*c := by
    simpa only [norm_diagonalModulation] using hA
  have hscaled := massPowerScale_amplitude_motion hn hn' hc hc' hδ
    (show 0 ≤ G^(-(1/4:ℝ)) by positivity) (show 0 ≤ L^Q by positivity)
    hN hchild (-(1/p)) (μ-1+1/p) A' (diagonalModulation frequency A b) hbase hraw
  have hlamAbs : ‖lam'-lam‖ ≤ ql := by
    have hm := complex_relative_motion_to_sub hlam0 hlamMove
    exact hm.trans ((mul_le_mul_of_nonneg_left hlam (show 0 ≤ ql by dsimp [ql,el]; positivity)).trans_eq
      (mul_one ql))
  have hnum := prediction_numerator_motion hn hn' hc.le hδ
    (show 0 ≤ ql by dsimp [ql,el]; positivity)
    (show 0 ≤ G^(-(1/4:ℝ)) by positivity) (show 0 ≤ L^Q by positivity)
    hN μ lam lam' hlam hlamAbs A' (diagonalModulation frequency A b) hbase hraw
  constructor
  · have hcomm : diagonalModulation frequency
        (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b =
        massPowerScale n c (-(1/p)) (μ-1+1/p) • diagonalModulation frequency A b :=
      (diagonalModulationRealIsometry frequency b).map_smul _ _
    rw [hcomm]
    apply hscaled.trans
    have hb := mul_le_mul_of_nonneg_right hcoeff'.1
      (show 0 ≤ (c/n)^(1/p)*c^μ by positivity)
    rw [mul_assoc,prediction_mass_scale_identity hn hc]
    simpa only [mul_assoc] using hb
  · exact hnum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff'.2 (Real.rpow_nonneg hn.le μ))
      (div_pos hc hn).le)

end LipschitzHilbert

end

end OAI
