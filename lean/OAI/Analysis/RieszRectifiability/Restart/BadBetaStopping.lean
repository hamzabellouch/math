import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SupportDescendantCountable
import OAI.Analysis.RieszRectifiability.Packing.OriginalADBetaPacking
import OAI.Analysis.RieszRectifiability.Nets.CountableCellMultiplicity

namespace OAI

/-!
# Stopping estimates from bad-beta multiplicity

Bad-beta descendants form a countable family of measurable cells. Their total-mass
packing bound controls the tail of the cell multiplicity and gives almost-everywhere
finite incidence. At the threshold twice the packing constant, at least half the
root-cell mass remains in the low-multiplicity region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def badBetaMultiplicity {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Ambient d → ℝ≥0∞ :=
  cellMultiplicity (fun i : BadBetaDescendant n μ R hR k z H ε => i.val.cell)

theorem badBetaDescendant_countable {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Countable (BadBetaDescendant n μ R hR k z H ε) := by
  let := supportCellDescendant_countable μ R hR k z
  unfold BadBetaDescendant
  infer_instance

theorem badBetaMultiplicity_measurable {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Measurable (badBetaMultiplicity n μ R hR k z H ε) := by
  let := badBetaDescendant_countable n μ R hR k z H ε
  exact cellMultiplicity_measurable (fun i : BadBetaDescendant n μ R hR k z H ε => i.val.cell)
    (fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩)

theorem original_AD_Riesz_bad_beta_stopping {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      (∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
        μ {x | t ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
          (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / t) ∧
      (∀ᵐ x ∂μ, {i : BadBetaDescendant (p + 1) μ R hR k z H ε | x ∈ i.val.cell}.Finite) := by
  obtain ⟨K, hK, hpack⟩ := original_AD_Riesz_bad_beta_total_mass hnd μ hAD hRiesz H ε hH hε
  refine ⟨K, hK, ?_⟩
  intro R hR k z hcore
  let := badBetaDescendant_countable (p + 1) μ R hR k z H ε
  let A (i : BadBetaDescendant (p + 1) μ R hR k z H ε) := i.val.cell
  have hA : ∀ i, MeasurableSet (A i) := fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hp := hpack R hR k z hcore
  constructor
  · intro t ht htt
    exact cellMultiplicity_tail_bound μ A hA _ t hp ht htt
  · have htop : μ (cleanSupportCell μ R hR k z) < ∞ :=
      (measure_mono (show cleanSupportCell μ R hR k z ⊆ supportLatticeCell μ R hR k z
        from fun _ hx => hx.1)).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top
    apply ae_finite_cell_incidence μ A hA
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) hp

theorem original_AD_Riesz_low_beta_count_half_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      μ (cleanSupportCell μ R hR k z) / 2 ≤
        μ {x ∈ cleanSupportCell μ R hR k z |
          badBetaMultiplicity (p + 1) μ R hR k z H ε x < ENNReal.ofReal K * 2} := by
  obtain ⟨K, hK, hpack⟩ := original_AD_Riesz_bad_beta_total_mass hnd μ hAD hRiesz H ε hH hε
  refine ⟨K, hK, ?_⟩
  intro R hR k z hcore
  let := badBetaDescendant_countable (p + 1) μ R hR k z H ε
  let A (i : BadBetaDescendant (p + 1) μ R hR k z H ε) := i.val.cell
  have hA : ∀ i, MeasurableSet (A i) := fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have htop : μ (cleanSupportCell μ R hR k z) < ∞ :=
    (measure_mono (show cleanSupportCell μ R hR k z ⊆ supportLatticeCell μ R hR k z
      from fun _ hx => hx.1)).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top
  exact cellMultiplicity_half_mass μ A hA (cleanSupportCell μ R hR k z) (ENNReal.ofReal K)
    (ENNReal.ofReal_pos.mpr hK).ne' ENNReal.ofReal_ne_top htop.ne (hpack R hR k z hcore)

end

end RieszRectifiability

end OAI
