import OAI.Analysis.KadisonKastler.RegularIntervalAverages

namespace OAI

/-! # Reconstruction from localized Haar averages

Finite packet averages belong to the explicit commutant algebra. The
normalized interval limit recovers every operator commuting with the
regular core, and hence proves the published commutant formula.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem complex_normalization_identity {r : ℝ} (hr : r ≠ 0) (x y : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) * x - y = r⁻¹ • (x - r • y) := by
  have hc : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
    norm_cast
    exact inv_mul_cancel₀ hr
  simp only [RCLike.real_smul_eq_coe_mul (K := ℂ)]
  change ((r⁻¹ : ℝ) : ℂ) * x - y = ((r⁻¹ : ℝ) : ℂ) * (x - (r : ℂ) * y)
  rw [mul_sub, ← mul_assoc, hc, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem regularNormalizedIntervalAverage_tendsto_supported
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    {A : ℝ} (hA : 0 ≤ A) (f g : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f)
    (hg : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc g = g) :
    Tendsto (fun n => inner ℂ f (regularNormalizedIntervalAverage n T g)) atTop
      (𝓝 (inner ℂ f (T g))) := by
  let b : ℝ := 8 * A * (‖T‖ * (‖f‖ * ‖g‖))
  have hscale : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_mono (fun n => by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1))⁻¹ * b) atTop (𝓝 0) := by
    simpa only [zero_mul] using hscale.mul_const b
  have hlarge : ∀ᶠ n : ℕ in atTop, A ≤ (n : ℝ) + 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop A)] with n hn
    linarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hlarge.mono fun n hn => ?_) hb
  have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have he : inner ℂ f (regularNormalizedIntervalAverage n T g) - inner ℂ f (T g) =
      (2 * ((n : ℝ) + 1))⁻¹ •
        (inner ℂ f (regularLocalizationAverage
          (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
          (by simp [Real.volume_Icc]) T g) -
          (2 * ((n : ℝ) + 1) : ℝ) • inner ℂ f (T g)) := by
    change inner ℂ f (((((2 * ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) •
      (regularLocalizationAverage
        (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
        (by simp [Real.volume_Icc]) T g))) - _ = _
    rw [inner_smul_right]
    exact complex_normalization_identity hp.ne' _ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact mul_le_mul_of_nonneg_left (regularIntervalAverage_error_le T hT hA hn f g hf hg)
    (inv_nonneg.mpr hp.le)

private theorem regularIndicatorProjection_larger
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (f : RegularCoreHilbert H) :
    regularIndicatorProjection t ht (regularIndicatorProjection s hs f) =
      regularIndicatorProjection s hs f := by
  have h := congrArg star (regularIndicatorProjection_mul_of_subset (H := H) s t hs ht hst)
  simp only [star_mul,
    (regularIndicatorProjection_isStarProjection (H := H) s hs).isSelfAdjoint.star_eq,
    (regularIndicatorProjection_isStarProjection (H := H) t ht).isSelfAdjoint.star_eq] at h
  exact congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B f) h

/-- Normalized interval localization converges weakly on all regular vectors. -/
theorem regularNormalizedIntervalAverage_tendsto_weak
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun n => inner ℂ f (regularNormalizedIntervalAverage n T g)) atTop
      (𝓝 (inner ℂ f (T g))) := by
  apply weak_tendsto_of_strong_cutoff_tests (fun n => regularNormalizedIntervalAverage n T) T
    (fun k => regularIndicatorProjection (Set.Icc (-(k : ℝ)) (k : ℝ)) measurableSet_Icc)
    regularIntervalProjection_tendsto ‖T‖ (norm_nonneg T)
    (fun n => norm_regularNormalizedIntervalAverage_le n T) ?_ g f
  intro k l x y
  let A : ℝ := max (k : ℝ) (l : ℝ)
  have hk : Set.Icc (-(k : ℝ)) (k : ℝ) ⊆ Set.Icc (-A) A := by
    intro r hr
    have hh : (k : ℝ) ≤ A := le_max_left _ _
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hl : Set.Icc (-(l : ℝ)) (l : ℝ) ⊆ Set.Icc (-A) A := by
    intro r hr
    have hh : (l : ℝ) ≤ A := le_max_right _ _
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  exact regularNormalizedIntervalAverage_tendsto_supported T hT
    (le_trans (Nat.cast_nonneg k) (le_max_left _ _)) _ _
    (regularIndicatorProjection_larger _ _ measurableSet_Icc measurableSet_Icc hl y)
    (regularIndicatorProjection_larger _ _ measurableSet_Icc measurableSet_Icc hk x)

/-- The explicit convolution algebra contains every core-commuting operator. -/
theorem regularLocalizationReconstruction_mem
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hπ : ∀ a ∈ P, Commute T (regularCoreEmbedding U hU a))
    (hρ : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    T ∈ regularCommutantAlgebra U P := by
  have hm (n : ℕ) : regularNormalizedIntervalAverage n T ∈ regularCommutantAlgebra U P := by
    rw [regularNormalizedIntervalAverage]
    exact (regularCommutantAlgebra U P).smul_mem
      (regularLocalizationAverage_mem U hU P T hπ _ measurableSet_Icc
        (by simp [Real.volume_Icc])) (((2 * ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ)
  let a (n : ℕ) : Algebra (regularCommutantAlgebra U P) :=
    ⟨regularNormalizedIntervalAverage n T, hm n⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) _ a T
  intro f g
  exact regularNormalizedIntervalAverage_tendsto_weak T hρ g f

universe u

/-- The regular commutant identity follows from packet localization. -/
theorem publishedRegularCommutant : PublishedRegularCommutant.{u} := by
  intro H _ _ _ _ U hU P hP
  apply le_antisymm
  · intro T hT
    apply regularLocalizationReconstruction_mem U hU P T
    · intro a ha
      exact (VonNeumannAlgebra.mem_commutant_iff.mp hT _
        (regularCoreEmbedding_mem_core U hU P ha)).symm
    · intro r
      exact (VonNeumannAlgebra.mem_commutant_iff.mp hT _
        (regularTranslation_mem_core U hU P (Multiplicative.ofAdd r))).symm
  · intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    exact VonNeumannAlgebra.mem_commutant_iff.mp
      (regularCommutantAlgebra_le_fixed_commutant U P hT) S
      (regularCoreAlgebra_le_fixed U hU P hP hS)

end

end KadisonKastler

end OAI
