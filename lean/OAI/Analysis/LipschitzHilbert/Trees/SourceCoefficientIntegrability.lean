import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalCoefficient
import OAI.Analysis.LipschitzHilbert.Estimates.CoefficientPolarization

namespace OAI

/-! Bounded measurable tests make the original physical analyzing
integrals integrable, so coefficient polarization uses genuine linearity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem physicalSelectedWave_measurable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Measurable (P.physicalSelectedWave t d v q k) :=
  Measurable.ite (measurableSet_le hv measurable_const)
    (P.physicalPacket t q.1 q.2 k).continuous.measurable measurable_const

theorem physicalSelectedWave_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Integrable (P.physicalSelectedWave t d v q k) (volume.prod volume) :=
  (P.physicalPacket t q.1 q.2 k).integrable.indicator (measurableSet_le hv measurable_const)

theorem physical_analyzing_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (q : Σ j, ι j) (k : κ) :
    Integrable (fun z => g z k*conj (P.physicalSelectedWave t d v q k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalSelectedWave_integrable t d v hv q k).norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (P.physicalSelectedWave_measurable t d v hv q k))).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_mul,norm_star]
  have hk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (norm_nonneg _)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
