import OAI.MeasureTheory.Falconer.Estimates.Availability

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

def FrostmanBallBound {d : ℕ} (μ : Measure (Space d)) (s C : ℝ) : Prop :=
  ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C * r^s)

/-- Application-level specialization of Mattila (1995), Theorem 8.8.
The upper bound on the exponent only fixes a convenient unit-size gap. -/
def PublishedFrostmanAboveHalf : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ E : Set (Space d), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E →
    ∃ s : ℝ, (d : ℝ) / 2 < s ∧ s < (d : ℝ) / 2 + 1 ∧
      ∃ μ : ProbabilityMeasure (Space d), (μ : Measure (Space d)) Eᶜ = 0 ∧
        ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (μ : Measure (Space d)) s C

theorem noAtoms_of_frostman {d : ℕ} (μ : Measure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hb : FrostmanBallBound (μ : Measure (Space d)) s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

theorem normalized_frostman_restriction {d : ℕ} (μ : ProbabilityMeasure (Space d))
    {s C : ℝ} (hb : FrostmanBallBound (μ : Measure (Space d)) s C) (hC : 0 < C)
    (A : Set (Space d)) (hA : MeasurableSet A) (hpos : 0 < (μ : Measure (Space d)) A) :
    ∃ ν : ProbabilityMeasure (Space d), (ν : Measure (Space d)) Aᶜ = 0 ∧
      ∃ D : ℝ, 0 < D ∧ FrostmanBallBound (ν : Measure (Space d)) s D := by
  let m := ((μ : Measure (Space d)) A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  let ν₀ : Measure (Space d) := ENNReal.ofReal m⁻¹ • (μ : Measure (Space d)).restrict A
  have hprob : IsProbabilityMeasure ν₀ := by
    constructor
    dsimp [ν₀]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      ← ENNReal.ofReal_toReal (measure_ne_top (μ : Measure (Space d)) A),
      ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one]
  let ν : ProbabilityMeasure (Space d) := ⟨ν₀, hprob⟩
  refine ⟨ν, ?_, m⁻¹ * C, mul_pos (inv_pos.mpr hm) hC, ?_⟩
  · simp [ν, ν₀, Measure.smul_apply, Measure.restrict_apply hA.compl]
  · intro x r hr
    change ν₀ (ball x r) ≤ _
    dsimp [ν₀]
    rw [Measure.restrict_apply measurableSet_ball]
    calc
      _ ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal (C * r^s) :=
        mul_le_mul_right ((measure_mono inter_subset_left).trans (hb x r hr)) _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

theorem distinct_support_points {d : ℕ} (μ : ProbabilityMeasure (Space d))
    [NullSingletonClass (μ : Measure (Space d))] :
    ∃ x ∈ (μ : Measure (Space d)).support,
      ∃ y ∈ (μ : Measure (Space d)).support, x ≠ y := by
  obtain ⟨x, hx⟩ := (μ : Measure (Space d)).nonempty_support (by
    intro h
    have hh := congrArg (fun ν : Measure (Space d) => ν univ) h
    simp at hh)
  have hcomp : (μ : Measure (Space d)) {x}ᶜ = 1 := by
    rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _)]
    simp
  obtain ⟨y, hy, hyS⟩ := (μ : Measure (Space d)).nonempty_inter_support_of_pos
    (by rw [hcomp]; exact zero_lt_one)
  exact ⟨x, hx, y, hyS, fun he => hy (by simp [he])⟩

theorem separated_compact_pieces {d : ℕ} (E : Set (Space d)) (hE : IsCompact E)
    (μ : ProbabilityMeasure (Space d)) (hμ : (μ : Measure (Space d)) Eᶜ = 0)
    [NullSingletonClass (μ : Measure (Space d))] :
    ∃ A B : Set (Space d), IsCompact A ∧ IsCompact B ∧ A ⊆ E ∧ B ⊆ E ∧
      0 < (μ : Measure (Space d)) A ∧ 0 < (μ : Measure (Space d)) B ∧
      ∃ r : ℝ, 0 < r ∧ ∀ a ∈ A, ∀ b ∈ B, r/2 ≤ dist a b ∧ dist a b ≤ 2*r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := distinct_support_points μ
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  let A := E ∩ closedBall x (r/1000)
  let B := E ∩ closedBall y (r/1000)
  have hpositive (z : Space d) (hz : z ∈ (μ : Measure (Space d)).support) :
      0 < (μ : Measure (Space d)) (E ∩ closedBall z (r/1000)) := by
    have hball := ((μ : Measure (Space d)).mem_support_iff_forall z).mp hz
      (ball z (r/1000)) (ball_mem_nhds z (by positivity))
    have hsub : ball z (r/1000) ⊆ (E ∩ closedBall z (r/1000)) ∪ Eᶜ := by
      intro w hw
      by_cases he : w ∈ E
      · exact Or.inl ⟨he, ball_subset_closedBall hw⟩
      · exact Or.inr he
    have hle := (measure_mono hsub).trans (measure_union_le _ _ (μ := (μ : Measure (Space d))))
    rw [hμ, add_zero] at hle
    exact hball.trans_le hle
  refine ⟨A, B, hE.inter_right isClosed_closedBall, hE.inter_right isClosed_closedBall,
    inter_subset_left, inter_subset_left, hpositive x hx, hpositive y hy, r, hr, ?_⟩
  intro a ha b hb
  have hax : dist a x ≤ r/1000 := ha.2
  have hby : dist b y ≤ r/1000 := hb.2
  have hupper := dist_triangle4 a x y b
  have hlower := dist_triangle4 x a b y
  rw [dist_comm y b] at hupper
  rw [dist_comm x a] at hlower
  change r/2 ≤ dist a b ∧ dist a b ≤ 2*r
  constructor <;> linarith

/-- Compact separated starting laws with a fixed positive Frostman gap,
constructed conditionally only on the cited classical Frostman lemma. -/
theorem starting_measures_of_published_frostman (hF : PublishedFrostmanAboveHalf)
    {d : ℕ} (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
    (hDim : (d : ℝ≥0∞) / 2 < dimH E) :
    ∃ χ : ℝ, 0 < χ ∧ χ < 1 ∧ ∃ μ ν : ProbabilityMeasure (Space d),
      IsCompact (μ : Measure (Space d)).support ∧ IsCompact (ν : Measure (Space d)).support ∧
      (μ : Measure (Space d)).support ⊆ E ∧ (ν : Measure (Space d)).support ⊆ E ∧
      ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ FrostmanBallBound (μ : Measure (Space d)) ((d : ℝ)/2 + χ) C ∧
        FrostmanBallBound (ν : Measure (Space d)) ((d : ℝ)/2 + χ) C ∧
        ∀ x ∈ (μ : Measure (Space d)).support, ∀ y ∈ (ν : Measure (Space d)).support,
          r/2 ≤ dist x y ∧ dist x y ≤ 2*r := by
  obtain ⟨s, hs, hs1, ζ, hζ, C, hC, hball⟩ := hF d hd E hE hDim
  have hs0 : 0 < s := (by positivity : (0 : ℝ) ≤ d/2).trans_lt hs
  let := noAtoms_of_frostman (ζ : Measure (Space d)) hs0 hball
  obtain ⟨A, B, hA, hB, hAE, hBE, hAp, hBp, r, hr, hsep⟩ :=
    separated_compact_pieces E hE ζ hζ
  obtain ⟨μ, hμ, Cμ, hCμ, hballμ⟩ := normalized_frostman_restriction ζ hball hC A hA.measurableSet hAp
  obtain ⟨ν, hν, Cν, _, hballν⟩ := normalized_frostman_restriction ζ hball hC B hB.measurableSet hBp
  have hsμ := (μ : Measure (Space d)).support_subset_of_isClosed hA.isClosed hμ
  have hsν := (ν : Measure (Space d)).support_subset_of_isClosed hB.isClosed hν
  refine ⟨s-d/2, by linarith, by linarith, μ, ν,
    hA.of_isClosed_subset Measure.isClosed_support hsμ,
    hB.of_isClosed_subset Measure.isClosed_support hsν, hsμ.trans hAE, hsν.trans hBE,
    max Cμ Cν, r, hCμ.trans_le (le_max_left _ _), hr, ?_, ?_, ?_⟩
  · convert (show FrostmanBallBound (μ : Measure (Space d)) s (max Cμ Cν) from ?_) using 1
    · ring
    · intro x t ht
      exact (hballμ x t ht).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · convert (show FrostmanBallBound (ν : Measure (Space d)) s (max Cμ Cν) from ?_) using 1
    · ring
    · intro x t ht
      exact (hballν x t ht).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  · exact fun x hx y hy => hsep x (hsμ hx) y (hsν hy)

end Falconer

end OAI
