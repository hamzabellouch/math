import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

def realL2ZeroExtension {n : ℕ} (K : Set (Fin n → ℝ)) (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume.restrict K)) : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  ((memLp_indicator_iff_restrict hK).mpr (Lp.memLp f)).toLp (K.indicator f)

theorem realL2ZeroExtension_ae {n : ℕ} (K : Set (Fin n → ℝ)) (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume.restrict K)) :
    (realL2ZeroExtension K hK f : (Fin n → ℝ) → ℝ) =ᵐ[volume] K.indicator f :=
  MemLp.coeFn_toLp _

theorem realL2ZeroExtension_ae_on {n : ℕ} (K : Set (Fin n → ℝ)) (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume.restrict K)) :
    (realL2ZeroExtension K hK f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict K] f := by
  filter_upwards [ae_restrict_of_ae (realL2ZeroExtension_ae K hK f),ae_restrict_mem hK] with x hx hmem
  rw [hx,indicator_of_mem hmem]

theorem realL2ZeroExtension_norm {n : ℕ} (K : Set (Fin n → ℝ)) (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume.restrict K)) : ‖realL2ZeroExtension K hK f‖=‖f‖ := by
  rw [realL2ZeroExtension,Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hK]
  rfl

theorem realL2_restrict_memLp {n : ℕ} {K L : Set (Fin n → ℝ)} (hLK : L ⊆ K)
    (f : Lp ℝ 2 (volume.restrict K)) : MemLp f 2 (volume.restrict L) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono hLK le_rfl)

def realL2Restriction {n : ℕ} {K L : Set (Fin n → ℝ)} (hLK : L ⊆ K)
    (f : Lp ℝ 2 (volume.restrict K)) : Lp ℝ 2 (volume.restrict L) :=
  (realL2_restrict_memLp hLK f).toLp f

theorem realL2Restriction_ae {n : ℕ} {K L : Set (Fin n → ℝ)} (hLK : L ⊆ K)
    (f : Lp ℝ 2 (volume.restrict K)) :
    (realL2Restriction hLK f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict L] f :=
  MemLp.coeFn_toLp _

theorem realL2Restriction_norm_le {n : ℕ} {K L : Set (Fin n → ℝ)} (hLK : L ⊆ K)
    (f : Lp ℝ 2 (volume.restrict K)) : ‖realL2Restriction hLK f‖ ≤ ‖f‖ := by
  rw [realL2Restriction,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne
    (eLpNorm_mono_measure f (Measure.restrict_mono hLK le_rfl))

end
end Yau

end OAI
