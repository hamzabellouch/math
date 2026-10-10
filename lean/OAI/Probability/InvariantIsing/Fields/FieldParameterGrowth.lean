import OAI.Probability.InvariantIsing.Fields.FieldScalarLogCoshSecond

namespace OAI

/-! Local uniform growth follows from the actual bounded spatial
derivative and continuity of the parameter at spatial coordinate zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_spatial_linearGrowth {F D : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hD : ∀ y, |D y| ≤ K)
    (hd : ∀ y, HasDerivAt F (D y) y) : HasLinearGrowth F := by
  refine ⟨|F 0|, K, abs_nonneg _, hK, fun y => ?_⟩
  have hdiff : |F y - F 0| ≤ K * |y| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (univ : Set ℝ)) => (hd z).hasDerivWithinAt)
        (fun z _ => by simpa only [Real.norm_eq_abs] using hD z)
        convex_univ (mem_univ 0) (mem_univ y)
  rw [Real.norm_eq_abs]
  calc
    |F y| = |F y - F 0 + F 0| := by congr 1; ring
    _ ≤ |F y - F 0| + |F 0| := abs_add_le _ _
    _ ≤ K * |y| + |F 0| := add_le_add_left hdiff _
    _ = _ := by ring

lemma field_parameter_growth_eventually {U X : ℝ × ℝ → ℝ} {K t : ℝ}
    (_hK : 0 ≤ K) (hX : ∀ p, |X p| ≤ K)
    (hd : ∀ s y, HasDerivAt (fun z => U (s, z)) (X (s, y)) y)
    (hc : ContinuousAt (fun s => U (s, 0)) t) :
    ∀ᶠ s in 𝓝 t, ∀ y,
      |U (s, y)| ≤ |U (t, 0)| + 1 + K * |y| := by
  have he : ∀ᶠ s in 𝓝 t, |U (s, 0)| < |U (t, 0)| + 1 :=
    (tendsto_order.1 hc.abs).2 _ (lt_add_one _)
  filter_upwards [he] with s hs y
  have hdiff : |U (s, y) - U (s, 0)| ≤ K * |y| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (univ : Set ℝ)) => (hd s z).hasDerivWithinAt)
        (fun z _ => by simpa only [Real.norm_eq_abs] using hX (s, z))
        convex_univ (mem_univ 0) (mem_univ y)
  calc
    |U (s, y)| = |U (s, y) - U (s, 0) + U (s, 0)| := by congr 1; ring
    _ ≤ |U (s, y) - U (s, 0)| + |U (s, 0)| := abs_add_le _ _
    _ ≤ K * |y| + (|U (t, 0)| + 1) := add_le_add hdiff hs.le
    _ = _ := by ring

end InvariantIsing

end

end OAI
