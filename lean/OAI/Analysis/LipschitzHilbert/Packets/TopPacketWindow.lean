import OAI.Analysis.LipschitzHilbert.Packets.TopWeightedPacket
import OAI.Analysis.LipschitzHilbert.Fourier.PolynomialLineFamily

namespace OAI

/-! Actual top-weighted line packets. The window records only geometry
and the fixed packet decay order, and introduces no concentration input. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

structure TopPacketWindow (P : LinePacketFamily N κ ι) (q : ℕ) where
  baseX : ℝ
  baseZ : ℝ
  radiusX : ℝ
  radiusZ : ℝ
  radiusX_pos : 0 < radiusX
  radiusZ_pos : 0 < radiusZ
  length_le : P.topLength ≤ radiusX
  width_le : P.width ≤ radiusZ
  centerX_mem : ∀ j i, |P.centerX j i-baseX| ≤ radiusX
  centerZ_mem : ∀ j i, |P.centerZ j i-baseZ| ≤ radiusZ
  wave_bound : ∀ j i k x, ‖P.wave j i k x‖ ≤ P.constant *
    (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
     lineEnvelope (P.centerZ j i) P.width (2+2*q) P.lineY)
  deriv_bound : ∀ j i k x, ‖deriv (P.wave j i k) x‖ ≤ (P.constant/P.length j) *
    (lineEnvelope (P.centerX j i) (P.length j) (3+2*q) x *
     lineEnvelope (P.centerZ j i) P.width (2+2*q) P.lineY)

namespace TopPacketWindow
variable {P : LinePacketFamily N κ ι} {q : ℕ}

def constant (_T : TopPacketWindow P q) : ℝ := 16^q*(1+2*(q:ℝ))*(16^q*P.constant)

theorem constant_pos (T : TopPacketWindow P q) : 0 < T.constant := by
  exact mul_pos (mul_pos (by positivity) (by positivity))
    (mul_pos (by positivity) P.constant_pos)

theorem constant_ge (T : TopPacketWindow P q) : 16^q*(16^q*P.constant) ≤ T.constant := by
  unfold constant
  calc
    _ = 16^q*1*(16^q*P.constant) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
      (mul_nonneg (by positivity) P.constant_pos.le)

def family (T : TopPacketWindow P q) : LinePacketFamily N κ ι :=
  P.replaceWaves T.constant T.constant_pos
    (fun j i k => topWeightedWave (P.wave j i k) T.baseX T.radiusX T.baseZ T.radiusZ P.lineY q)
    (by
      intro j i k x
      have h := topWeightedWave_bound (P.wave j i k) T.baseX T.radiusX T.baseZ T.radiusZ
        P.lineY (P.centerX j i) (P.length j) (P.centerZ j i) P.width P.constant q 3 2
        (P.length_pos j) T.radiusX_pos P.width_pos T.radiusZ_pos
        ((P.length_le_topLength j).trans T.length_le) T.width_le (T.centerX_mem j i)
        (T.centerZ_mem j i) P.constant_pos.le (T.wave_bound j i k) x
      exact h.trans (mul_le_mul_of_nonneg_right T.constant_ge
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))))
    (by
      intro j i k x
      exact topWeightedWave_derivative_bound (P.wave j i k) T.baseX T.radiusX T.baseZ T.radiusZ
        P.lineY (P.centerX j i) (P.length j) (P.centerZ j i) P.width P.constant q 3 2
        (P.length_pos j) T.radiusX_pos P.width_pos T.radiusZ_pos
        ((P.length_le_topLength j).trans T.length_le) T.width_le (T.centerX_mem j i)
        (T.centerZ_mem j i) P.constant_pos.le (T.wave_bound j i k) (T.deriv_bound j i k) x)

theorem family_budget (T : TopPacketWindow P q) (B : ℝ) (hB : P.HasLocalBudget B) :
    T.family.HasLocalBudget B := hB

theorem family_packets (T : TopPacketWindow P q) (j : Fin N) (k : κ) :
    T.family.packets j k =
      topWeightedWave (P.packets j k) T.baseX T.radiusX T.baseZ T.radiusZ P.lineY q :=
  packetSynthesis_topWeighted _ _ _ _ _ _ _ _

theorem family_variation (T : TopPacketWindow P q) (x : ℝ) :
    T.family.variation x =
      (polynomialWeight T.baseX T.radiusX q x * polynomialWeight T.baseZ T.radiusZ q P.lineY) *
        P.variation x := by
  have heq : T.family.packets = fun j k =>
      topWeightedWave (P.packets j k) T.baseX T.radiusX T.baseZ T.radiusZ P.lineY q := by
    funext j k
    exact T.family_packets j k
  unfold LinePacketFamily.variation
  rw [heq]
  simp_rw [hilbertPartialBandSum_topWeighted]
  apply LinePacketFamily.cubicVariation_smul_nonneg
  exact mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
    (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))

end TopPacketWindow
end LipschitzHilbert

end

end OAI
