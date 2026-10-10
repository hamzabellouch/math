import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCell
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellIntegralFreezing

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.MixedCellIntegralFreezing
open MeasureTheory PrimeCellFreezing
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def mixedLogRectangle (loI hiI : ℝ) (lo hi : ι → ℝ) : Set (ℝ × (ι → ℝ)) :=
  Set.Icc loI hiI ×ˢ logRectangle lo hi

def mixedLogDensity (M : ℕ) (G : ℝ) (φ : ℝ → ℝ) (w : ι → ℝ)
    (t : ℝ × (ι → ℝ)) : ℝ :=
  (Real.exp (t.1-G) * φ (t.1-G) / (M : ℝ)) * logCellDensity w t.2

def mixedLogMass (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (w lo hi : ι → ℝ) : ℝ :=
  ∫ t in mixedLogRectangle loI hiI lo hi, mixedLogDensity M G φ w t

theorem mixedLogMass_eq (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (w lo hi : ι → ℝ)
    (hI : loI ≤ hiI) :
    mixedLogMass M loI hiI G φ w lo hi =
      IntegerCell.integerDensityMass M loI hiI G φ * logCellMass w lo hi := by
  unfold mixedLogMass mixedLogDensity mixedLogRectangle
  change (∫ t in Set.Icc loI hiI ×ˢ logRectangle lo hi,
    (Real.exp (t.1-G) * φ (t.1-G) / (M : ℝ)) * logCellDensity w t.2
      ∂(volume.prod volume)) = _
  rw [setIntegral_prod_mul (fun t : ℝ => Real.exp (t-G) * φ (t-G) / (M : ℝ))
    (logCellDensity w) (Set.Icc loI hiI) (logRectangle lo hi)]
  congr 1
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hI]
  rfl

theorem residue_mixedLogMass_eq (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (Z lo hi : ι → ℝ)
    (hI : loI ≤ hiI) (horder : ∀ i, lo i ≤ hi i) :
    mixedLogMass M loI hiI G φ (fun i => ((Nat.totient M : ℝ) * Z i)⁻¹) lo hi =
      IntegerCell.integerDensityMass M loI hiI G φ *
        ∏ i, PrimeProgression.harmonicIntegral M (lo i) (hi i) / Z i := by
  rw [mixedLogMass_eq M loI hiI G φ _ lo hi hI,
    residue_logCellMass_eq_prod M Z lo hi horder]

omit [Fintype ι] in
theorem isCompact_mixedLogRectangle (loI hiI : ℝ) (lo hi : ι → ℝ) :
    IsCompact (mixedLogRectangle loI hiI lo hi) :=
  isCompact_Icc.prod (isCompact_logRectangle lo hi)

theorem continuousOn_mixedLogDensity (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) :
    ContinuousOn (mixedLogDensity M G φ w) (mixedLogRectangle loI hiI lo hi) := by
  have hI : Continuous (fun t : ℝ × (ι → ℝ) =>
      Real.exp (t.1-G) * φ (t.1-G) / (M : ℝ)) := by fun_prop
  exact hI.continuousOn.mul ((continuousOn_logCellDensity w lo hi hlo).comp
    continuous_snd.continuousOn (fun _ ht => ht.2))

theorem integrableOn_mixedLogDensity (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) :
    IntegrableOn (mixedLogDensity M G φ w) (mixedLogRectangle loI hiI lo hi) :=
  (continuousOn_mixedLogDensity M loI hiI G φ w lo hi hφ hlo).integrableOn_compact
    (isCompact_mixedLogRectangle loI hiI lo hi)

theorem mixedLogDensity_nonneg (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i)
    {t : ℝ × (ι → ℝ)} (ht : t ∈ mixedLogRectangle loI hiI lo hi) :
    0 ≤ mixedLogDensity M G φ w t :=
  mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (hφ t.1 ht.1)) (Nat.cast_nonneg M))
    (logCellDensity_nonneg w lo hi hw hlo ht.2)

theorem mixedLogMass_nonneg (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi : ι → ℝ) (hφ : ∀ t ∈ Set.Icc loI hiI, 0 ≤ φ (t-G))
    (hw : ∀ i, 0 ≤ w i) (hlo : ∀ i, 0 < lo i) :
    0 ≤ mixedLogMass M loI hiI G φ w lo hi := by
  apply setIntegral_nonneg (isCompact_mixedLogRectangle loI hiI lo hi).measurableSet
  intro t ht
  exact mixedLogDensity_nonneg M loI hiI G φ w lo hi hφ hw hlo ht

end Ostmann.Arithmetic.MixedCellIntegralFreezing

end

end OAI
