import OAI.Analysis.CircleDomains.Sobolev.PriorityL2Approximation

namespace OAI

/-! Retain the small energy of the altered support, as required by the
third term in the actual saved-barrier estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_priority_L2_approximation_with_support
    {B U : Set ℂ} (hB : IsClosed B) (hU : IsOpen U) (hUB : U ⊆ Bᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, b n ∈ B)
    (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (b n))
    (c : ℕ → ℝ) (X : ℂ → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ)
    {K : ℝ} (hK : 0 ≤ K) (hc : ∀ n, ‖c n‖ ≤ K) (hXb : ∀ z ∈ U, ‖X z‖ ≤ K)
    (hDX : MemLp (fderiv ℝ X) 2 (volume.restrict U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (b n) (r n) ⊆ O n) ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (b n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (b n), χ n z = 1)) ∧
      let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
      MemLp (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U) ∧
        (eLpNorm (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U)).toReal < ε ∧
        (eLpNorm ((⋃ n, support (χ n)).indicator (fun z => ‖fderiv ℝ X z‖))
          2 (volume.restrict U)).toReal < ε := by
  let τ := ε/(2*(2*K+1))
  have hτ : 0 < τ := div_pos hε (by positivity)
  let a : ℕ → ℝ := fun n => τ/2/2^n
  have ha : ∀ n, 0 < a n := fun n => by dsimp [a]; positivity
  have has : HasSum a τ := hasSum_geometric_two' τ
  obtain ⟨r, χ, hr, hrt, hrO, hmass, hχ, hA, hAnorm⟩ :=
    exists_priority_cutoffs hDX.norm b O hO
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hτ)) a ha has.summable
  have hs (n : ℕ) : support (χ n) ⊆ ball (b n) (r n) :=
    (subset_tsupport (χ n)).trans (hχ n).2.2.1
  have hχs (n : ℕ) : ContDiff ℝ ∞ (χ n) := (hχ n).1
  have hχu (n : ℕ) (z : ℂ) : χ n z ∈ Icc (0 : ℝ) 1 := (hχ n).2.2.2.1 z
  obtain ⟨hP, hPn⟩ := priority_source_L2_error hB hU hUB b hb r hrt χ hχs hχu hs
    c X hX hK hc hXb hDX hA
  have hAn : (eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal ≤ τ := by
    apply (ENNReal.toReal_mono hA.ne_top
      (eLpNorm_mono_measure _ Measure.restrict_le_self)).trans
    simpa only [has.tsum_eq] using hAnorm
  let S := ⋃ n, support (χ n)
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun n =>
    ((hχs n).continuous.isOpen_preimage _ isOpen_ne).measurableSet)
  have hSE : S ⊆ ⋃ n, ball (b n) (r n) := iUnion_mono hs
  have hI : (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal < τ := by
    apply indicator_L2_norm_lt_of_energy_lt hDX.norm hS hτ
    exact (lintegral_mono_set hSE).trans_lt hmass
  refine ⟨r, χ, hr, hrt, hrO, hχ, hP, ?_, ?_⟩
  swap
  · exact hI.trans_le (div_le_self hε.le (by nlinarith))
  have hnum : (2*K+1)*τ = ε/2 := by
    dsimp [τ]
    have hden : 2*K+1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hden]
  calc
    _ ≤ 2*K*(eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal +
        (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal := hPn
    _ < 2*K*τ+τ := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hAn (by positivity)) hI
    _ = (2*K+1)*τ := by ring
    _ = ε/2 := hnum
    _ < ε := by linarith

end CircleDomainRigidity

end

end OAI
