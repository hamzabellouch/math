import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralHolder
import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralPowerGain
import OAI.Analysis.LipschitzHilbert.Trees.SourceCountParameters

namespace OAI

/-! The mass and measure bounds in §11 give the precise power of N in
the central estimate. The previously proved exponent gain then absorbs
all of the fixed polynomial factors. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

 theorem central_root_budget {L N F S q p gamma : ℝ}
    (hL : 1 ≤ L) (hN : 0 < N) (hF : 0 < F) (hS : 0 ≤ S)
    (hq : 0 ≤ q) (hp : 1 ≤ p) (hgamma2 : gamma ≤ 2)
    (hSupper : S ≤ L^q*N^2*F) :
    (L^q*S^(1/p))*F^(1-1/p)*(L^q*N)^gamma ≤
      L^(4*q)*F*N^(gamma+2/p) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpinv : 1/p ≤ 1 := (div_le_one hp0).mpr hp
  have hSpow := Real.rpow_le_rpow hS hSupper (one_div_nonneg.mpr hp0.le)
  have hSprod : (L^q*N^2*F)^(1/p) = L^(q/p)*N^(2/p)*F^(1/p) := by
    rw [Real.mul_rpow (by positivity) hF.le,
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hL0.le,← Real.rpow_natCast,← Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    simp only [div_eq_mul_inv,one_mul]
  have hFprod : F^(1/p)*F^(1-1/p) = F := by
    rw [← Real.rpow_add hF]
    rw [show 1/p+(1-1/p) = (1:ℝ) by ring,Real.rpow_one]
  have hLprod : L^q*L^(q/p)*(L^q)^gamma = L^(q+q/p+q*gamma) := by
    rw [← Real.rpow_mul hL0.le,← Real.rpow_add hL0,← Real.rpow_add hL0]
  have hNprod : N^(2/p)*N^gamma = N^(gamma+2/p) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (L^q*(L^q*N^2*F)^(1/p))*F^(1-1/p)*(L^q*N)^gamma := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSpow (by positivity))
          (by positivity)) (by positivity)
    _ = L^(q+q/p+q*gamma)*F*N^(gamma+2/p) := by
      rw [hSprod,Real.mul_rpow (by positivity) hN.le]
      calc
        _ = (L^q*L^(q/p)*(L^q)^gamma)*(F^(1/p)*F^(1-1/p))*(N^(2/p)*N^gamma) := by ring
        _ = _ := by rw [hLprod,hFprod,hNprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hF.le
      apply Real.rpow_le_rpow_of_exponent_le hL
      have hqp : q/p ≤ q := by
        have h := mul_le_mul_of_nonneg_left hpinv hq
        simpa only [mul_one,mul_one_div] using h
      have hqgamma := mul_le_mul_of_nonneg_left hgamma2 hq
      nlinarith

 theorem source_central_estimate {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) [IsFiniteMeasure μ] (n : X → ℝ) (amp : X → EuclideanSpace ℂ κ)
    (L N F S q p alpha beta : ℝ)
    (hL : 1 ≤ L) (hN : 0 < N) (hF : 0 < F) (hS : 0 ≤ S) (hq : 0 ≤ q)
    (hp : 1 < p) (hgamma : 0 ≤ 1-alpha/p+beta) (hgamma2 : 1-alpha/p+beta ≤ 2)
    (hn : ∀ x, 0 < n x) (hnM : ∀ x, n x ≤ L^q*N)
    (hnmeas : Measurable n) (hamp : Measurable amp)
    (hmeasure : μ.real Set.univ ≤ F) (hSupper : S ≤ L^q*N^2*F)
    (henergy : Integrable (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) μ)
    (hmoment : (∫ x, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p)) :
    Integrable (fun x => n x^beta*‖amp x‖) μ ∧
      (∫ x, n x^beta*‖amp x‖ ∂μ) ≤
        L^(4*q)*F*N^(1+(2-alpha)/p+beta) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := by linarith
  have hFpower : (μ.real Set.univ)^(1-1/p) ≤ F^(1-1/p) :=
    Real.rpow_le_rpow (by positivity) hmeasure
      (by have := (div_le_one hp0).mpr hp.le; linarith)
  obtain ⟨hi,hb⟩ := central_weight_integral μ n amp alpha p beta (L^q*N) (L^q*S^(1/p))
    hn hnM hnmeas hamp hp (by positivity) hgamma henergy hmoment
  refine ⟨hi,?_⟩
  calc
    _ ≤ (L^q*S^(1/p))*(μ.real Set.univ)^(1-1/p)*(L^q*N)^(1-alpha/p+beta) := hb
    _ ≤ (L^q*S^(1/p))*F^(1-1/p)*(L^q*N)^(1-alpha/p+beta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFpower (by positivity)) (by positivity)
    _ ≤ L^(4*q)*F*N^((1-alpha/p+beta)+2/p) :=
      central_root_budget hL hN hF hS hq hp.le hgamma2 hSupper
    _ = _ := by
      congr 2
      ring

/-- The actual source phase and shift count give the central negative-power
estimate once the normalized vertex moment has been established. -/
theorem eventually_source_central_integral_gain (d q Q : ℝ)
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (X κ : Type*) [MeasurableSpace X] [Fintype κ]
      (μ : Measure X) [IsFiniteMeasure μ] (n : X → ℝ) (amp : X → EuclideanSpace ℂ κ)
      (N F S : ℝ), 0 < N → 0 < F → 0 ≤ S → L/2 ≤ Real.log N →
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let beta := ((1+PhaseCombinatorics.phaseParameter D)/p)/(SourceParameters.blockCount L:ℝ)
    (∀ x, 0 < n x) → (∀ x, n x ≤ L^q*N) → Measurable n → Measurable amp →
    μ.real Set.univ ≤ F → S ≤ L^q*N^2*F →
    Integrable (fun x => ‖(n x^(alpha/p-1)) • amp x‖^p) μ →
    (∫ x, ‖(n x^(alpha/p-1)) • amp x‖^p ∂μ)^(1/p) ≤ L^q*S^(1/p) →
    Integrable (fun x => n x^beta*‖amp x‖) μ ∧
      (∫ x, n x^beta*‖amp x‖ ∂μ) ≤ L^(-Q)*N*F := by
  filter_upwards [eventually_ge_atTop (16:ℝ),
    eventually_source_central_power_gain_actual d (4*q) Q hd (by positivity) hQ]
    with L hL hgain
  intro D hD hDb X κ _ _ μ _ n amp N F S hN hF hS hlog p alpha beta
    hn hnM hnmeas hamp hmeasure hSupper henergy hmoment
  have hp4 : 4 ≤ p := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith [hL])
  have hp0 : 0 < p := by linarith
  have htheta := PhaseCombinatorics.phaseParameter_range hD
  change 0 < PhaseCombinatorics.phaseParameter D ∧
    PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
  obtain ⟨htheta0,htheta1⟩ := htheta
  have hK : (1:ℝ) ≤ SourceParameters.blockCount L := by
    exact_mod_cast SourceParameters.blockCount_pos (show 1 < L by linarith)
  have halpha : 0 ≤ alpha/p := div_nonneg (by dsimp [alpha]; linarith) hp0.le
  have halpha1 : alpha/p ≤ 1 := (div_le_one hp0).mpr (by dsimp [alpha]; linarith)
  have hbeta0 : 0 ≤ beta := by
    exact div_nonneg (div_nonneg (by linarith) hp0.le) (zero_le_one.trans hK)
  have hbeta1 : beta ≤ 1 := by
    apply (div_le_self (div_nonneg (by linarith) hp0.le) hK).trans
    exact (div_le_one hp0).mpr (by linarith)
  obtain ⟨hi,hb⟩ := source_central_estimate μ n amp L N F S q p alpha beta
    (by linarith) hN hF hS hq (by linarith) (by linarith) (by linarith)
    hn hnM hnmeas hamp hmeasure hSupper henergy hmoment
  refine ⟨hi,?_⟩
  have hexp : 1+(2-alpha)/p+beta = 1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
      ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ) := by
    dsimp only [alpha,beta,p]
    ring
  rw [hexp] at hb
  calc
    _ ≤ L^(4*q)*F*N^(1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
        ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)) := hb
    _ = (L^(4*q)*N^(1-PhaseCombinatorics.phaseParameter D/Real.sqrt L+
        ((1+PhaseCombinatorics.phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)))*F := by ring
    _ ≤ (L^(-Q)*N)*F := mul_le_mul_of_nonneg_right (hgain D N hD hDb hN hlog) hF.le
    _ = _ := rfl

end LipschitzHilbert

end

end OAI
