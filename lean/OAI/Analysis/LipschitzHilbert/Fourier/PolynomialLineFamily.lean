import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement
import OAI.Analysis.LipschitzHilbert.Packets.PolynomialPacket

namespace OAI

/-! Apply a common horizontal top weight to actual line packets. The
coefficient budget is unchanged, and the packet order is fixed by the
weight degree, independently of the moment order. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert.LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def localizationConstant (P : LinePacketFamily N κ ι) (q : ℕ) : ℝ :=
  16^q*(1+2*(q:ℝ))*P.constant

theorem localizationConstant_pos (P : LinePacketFamily N κ ι) (q : ℕ) :
    0 < P.localizationConstant q := by
  unfold localizationConstant
  exact mul_pos (mul_pos (by positivity) (by positivity)) P.constant_pos

theorem localizationConstant_ge (P : LinePacketFamily N κ ι) (q : ℕ) :
    16^q*P.constant ≤ P.localizationConstant q := by
  unfold localizationConstant
  calc
    _ = 16^q*1*P.constant := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
      P.constant_pos.le

theorem localized_wave_bound (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr : 0 < r) (hscale : P.topLength ≤ r)
    (hcenter : ∀ j i, |P.centerX j i-a| ≤ r)
    (hwave : ∀ j i k x, ‖P.wave j i k x‖ ≤ P.constant *
      (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) :
    ∀ j i k x, ‖polynomialLocalization a r q (P.wave j i k) x‖ ≤
      P.localizationConstant q * (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 P.lineY) := by
  intro j i k x
  have h := polynomialLocalization_packet_bound (P.wave j i k) a r
    (P.centerX j i) (P.length j)
    (P.constant*lineEnvelope (P.centerZ j i) P.width 2 P.lineY) q 3
    (P.length_pos j) hr ((P.length_le_topLength j).trans hscale) (hcenter j i)
    (mul_nonneg P.constant_pos.le (lineEnvelope_nonneg _ _ _ _))
    (fun t => by simpa only [mul_assoc, mul_left_comm, mul_comm] using hwave j i k t) x
  calc
    _ ≤ (16^q*P.constant) * (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 P.lineY) := by convert h using 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (P.localizationConstant_ge q)
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))

theorem localized_derivative_bound (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr : 0 < r) (hscale : P.topLength ≤ r)
    (hcenter : ∀ j i, |P.centerX j i-a| ≤ r)
    (hwave : ∀ j i k x, ‖P.wave j i k x‖ ≤ P.constant *
      (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY))
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k) x‖ ≤ (P.constant/P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) :
    ∀ j i k x, ‖deriv (polynomialLocalization a r q (P.wave j i k)) x‖ ≤
      (P.localizationConstant q/P.length j) *
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
         lineEnvelope (P.centerZ j i) P.width 2 P.lineY) := by
  intro j i k x
  have h := polynomialLocalization_derivative_bound (P.wave j i k) a r
    (P.centerX j i) (P.length j)
    (P.constant*lineEnvelope (P.centerZ j i) P.width 2 P.lineY) q 3
    (P.length_pos j) hr ((P.length_le_topLength j).trans hscale) (hcenter j i)
    (mul_nonneg P.constant_pos.le (lineEnvelope_nonneg _ _ _ _))
    (fun t => by simpa only [mul_assoc, mul_left_comm, mul_comm] using hwave j i k t)
    (fun t => by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hderiv j i k t) x
  convert h using 1
  unfold localizationConstant
  ring

def localized (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr : 0 < r) (hscale : P.topLength ≤ r) (hcenter : ∀ j i, |P.centerX j i-a| ≤ r)
    (hwave : ∀ j i k x, ‖P.wave j i k x‖ ≤ P.constant *
      (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY))
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k) x‖ ≤ (P.constant/P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) : LinePacketFamily N κ ι :=
  P.replaceWaves (P.localizationConstant q) (P.localizationConstant_pos q)
    (fun j i k => polynomialLocalization a r q (P.wave j i k))
    (P.localized_wave_bound a r q hr hscale hcenter hwave)
    (P.localized_derivative_bound a r q hr hscale hcenter hwave hderiv)

theorem localized_budget (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr hscale hcenter hwave hderiv) (B : ℝ) (hB : P.HasLocalBudget B) :
    (P.localized a r q hr hscale hcenter hwave hderiv).HasLocalBudget B := hB

theorem localized_packets (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr hscale hcenter hwave hderiv) (j : Fin N) (k : κ) :
    (P.localized a r q hr hscale hcenter hwave hderiv).packets j k =
      polynomialLocalization a r q (P.packets j k) := by
  ext x
  change packetSynthesis (fun i => P.coeff j i k)
    (fun i => polynomialLocalization a r q (P.wave j i k)) x = _
  rw [packetSynthesis_apply, polynomialLocalization_apply, packets, packetSynthesis_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [polynomialLocalization_apply]
  ring

theorem cubicVariation_smul_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E) (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    cubicVariation (fun n => c • F n) N = c * cubicVariation F N := by
  rw [cubicVariation, finiteCubicVariation_smul, abs_of_nonneg hc,
    Real.mul_rpow (pow_nonneg hc 3) (finiteCubicVariation_nonneg F N)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
  norm_num

theorem localized_variation (P : LinePacketFamily N κ ι) (a r : ℝ) (q : ℕ)
    (hr hscale hcenter hwave hderiv) (x : ℝ) :
    (P.localized a r q hr hscale hcenter hwave hderiv).variation x =
      polynomialWeight a r q x * P.variation x := by
  have heq : (P.localized a r q hr hscale hcenter hwave hderiv).packets =
      fun j k => polynomialLocalization a r q (P.packets j k) := by
    funext j k
    exact P.localized_packets a r q hr hscale hcenter hwave hderiv j k
  unfold variation
  rw [heq]
  simp_rw [hilbertPartialBandSum_polynomialLocalization]
  exact cubicVariation_smul_nonneg _ N _
    (zero_le_one.trans (polynomialWeight_one_le a r q x))

end LipschitzHilbert.LinePacketFamily

end

end OAI
