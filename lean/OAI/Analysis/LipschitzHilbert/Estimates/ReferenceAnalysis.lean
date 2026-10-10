import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients

namespace OAI

/-! Actual selected analyzing integrals on the reference chart. Integrability
is obtained from the two-coordinate packet envelope and a bounded test. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def selectedWave (P : ReferencePacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d s.1 then P.wave s.1 s.2 k z.1 z.2 else 0

def mainCoefficient (P : ReferencePacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (i : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
    (P.selectedWave d v) g ⟨j,i⟩

theorem wave_integrable (P : ReferencePacketFamily N κ ι)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (j : Fin N) (i : ι j) (k : κ) :
    Integrable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2) := by
  have hz := integrable_lineEnvelope (P.baseZ + P.width * (P.site j i).2)
    P.width P.width_pos (by decide : 1 ≤ 3)
  have hx := integrable_lineEnvelope (P.baseX + P.length j * (P.site j i).1)
    (P.length j) (P.length_pos j) (by decide : 1 ≤ 3)
  apply ((hz.mul_prod hx).const_mul P.constant).mono' (hw j i k).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [mul_comm] using P.wave_bound j i k z.1 z.2

theorem selectedWave_measurable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (s : Σ j, ι j) (k : κ) : Measurable (P.selectedWave d v s k) :=
  Measurable.ite (measurableSet_le hv measurable_const) (hw s.1 s.2 k) measurable_const

theorem selectedWave_integrable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (s : Σ j, ι j) (k : κ) : Integrable (P.selectedWave d v s k) := by
  exact (P.wave_integrable hw s.1 s.2 k).indicator (measurableSet_le hv measurable_const)

theorem analyzing_integrable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (s : Σ j, ι j) (k : κ) :
    Integrable (fun z => g z k * conj (P.selectedWave d v s k z)) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.selectedWave_integrable d v hv hw s k).norm.mono'
    (hgm.mul (continuous_star.measurable.comp (P.selectedWave_measurable d v hv hw s k))).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, norm_star]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hgk (norm_nonneg _)

theorem diagonalSynthesis_selectedWave (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ × ℝ) :
    diagonalSynthesis (P.selectedWave d v) (fun s : Σ j, ι j => c s.1 s.2) z =
      P.thresholdSynthesis c d v z := by
  classical
  ext k
  simp only [diagonalSynthesis, thresholdSynthesis, WithLp.ofLp_sum, Finset.sum_apply,
    Fintype.sum_sigma, selectedWave]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : v z ≤ d j
  · simp only [ite_eq_left hj, scaleSynthesis, packets, packetSynthesis_apply]
  · simp only [ite_eq_right hj, mul_zero, Finset.sum_const_zero]
    rfl

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
