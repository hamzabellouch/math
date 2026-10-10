import OAI.Analysis.Pureness.Stabilization.Cuntz

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace

def cutMultiplier (δ : ℝ≥0) (t : ℝ) : ℝ := Real.sqrt (max (t - δ) 0 / max t δ)

lemma cutMultiplier_continuous {δ : ℝ≥0} (hδ : 0 < δ) : Continuous (cutMultiplier δ) := by
  apply Real.continuous_sqrt.comp
  exact ((continuous_id.sub continuous_const).max continuous_const).div
    (continuous_id.max continuous_const) fun t => ne_of_gt (lt_of_lt_of_le hδ (le_max_right t δ))

lemma cutMultiplier_zero (δ : ℝ≥0) : cutMultiplier δ 0 = 0 := by
  simp [cutMultiplier]

lemma cutMultiplier_sq {δ : ℝ≥0} (_hδ : 0 < δ) (t : ℝ) :
    cutMultiplier δ t ^ 2 = max (t - δ) 0 / max t δ :=
  Real.sq_sqrt (div_nonneg (le_max_right _ _) (le_trans δ.2 (le_max_right _ _)))

lemma cutMultiplier_identity {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    cutMultiplier δ t * t * cutMultiplier δ t = max (t - δ) 0 := by
  calc
    cutMultiplier δ t * t * cutMultiplier δ t = t * cutMultiplier δ t ^ 2 := by ring
    _ = t * (max (t - δ) 0 / max t δ) := by rw [cutMultiplier_sq hδ]
    _ = max (t - δ) 0 := by
      by_cases ht : t ≤ δ
      · simp [max_eq_right (sub_nonpos.mpr ht)]
      · have ht0 : 0 < t := lt_trans hδ (lt_of_not_ge ht)
        rw [max_eq_left (le_of_not_ge ht)]
        field_simp

lemma cutMultiplier_bound {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    cutMultiplier δ t * cutMultiplier δ t ≤ (δ : ℝ)⁻¹ * max (t - δ) 0 := by
  rw [← sq, cutMultiplier_sq hδ]
  simpa only [div_eq_mul_inv, mul_comm] using
    (div_le_div_of_nonneg_left (le_max_right (t - δ) 0) (show (0 : ℝ) < δ from hδ) (le_max_right t (δ : ℝ)))

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma fixedCut_factorization (b : Positive A) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ g : A, star g = g ∧ g * b.1 * g = (Positive.cut δ b).1 ∧
      g * g ≤ (δ : ℝ)⁻¹ • (Positive.cut δ b).1 := by
  let f := cutMultiplier δ
  have hf : Continuous f := cutMultiplier_continuous hδ
  have hf0 : f 0 = 0 := cutMultiplier_zero δ
  have hb : IsSelfAdjoint b.1 := IsSelfAdjoint.of_nonneg b.2
  refine ⟨cfcₙ f b.1, (cfcₙ_predicate f b.1).star_eq, ?_, ?_⟩
  · change cfcₙ f b.1 * b.1 * cfcₙ f b.1 = cfcₙ (fun t : ℝ => max (t - δ) 0) b.1
    calc
      cfcₙ f b.1 * b.1 * cfcₙ f b.1 = cfcₙ (fun t : ℝ => f t * t * f t) b.1 := by
        rw [cfcₙ_mul (fun t : ℝ => f t * t) f b.1,
          cfcₙ_mul f (fun t : ℝ => t) b.1, cfcₙ_id' ℝ b.1]
      _ = _ := cfcₙ_congr fun t _ => cutMultiplier_identity hδ t
  · change cfcₙ f b.1 * cfcₙ f b.1 ≤
      (δ : ℝ)⁻¹ • cfcₙ (fun t : ℝ => max (t - δ) 0) b.1
    rw [← cfcₙ_mul f f b.1, ← cfcₙ_const_mul (δ : ℝ)⁻¹ (fun t : ℝ => max (t - δ) 0) b.1]
    apply (cfcₙ_le_iff _ _ b.1).mpr
    intro t _
    exact cutMultiplier_bound hδ t

theorem bounded_witness (a b : Positive A) (δ : ℝ≥0) (hδ : 0 < δ)
    (h : CuntzBelow a (Positive.cut δ b)) (η : ℝ) (hη : 0 < η) :
    ∃ w : A, ‖star w * b.1 * w - a.1‖ < η ∧
      ‖w‖ ^ 2 ≤ (‖a.1‖ + η) / (δ : ℝ) := by
  obtain ⟨v, hv⟩ := h η hη
  obtain ⟨g, hgstar, hgb, hgBound⟩ := fixedCut_factorization b hδ
  let w := g * v
  have hcompare : star w * b.1 * w = star v * (Positive.cut δ b).1 * v := by
    change star (g * v) * b.1 * (g * v) = _
    rw [star_mul, hgstar]
    calc
      star v * g * b.1 * (g * v) = star v * (g * b.1 * g) * v := by noncomm_ring
      _ = _ := by rw [hgb]
  have hmod : star w * w = star v * (g * g) * v := by
    change star (g * v) * (g * v) = _
    rw [star_mul, hgstar]
    noncomm_ring
  have horder : star w * w ≤ (δ : ℝ)⁻¹ • (star v * (Positive.cut δ b).1 * v) := by
    rw [hmod]
    simpa only [mul_smul_comm, smul_mul_assoc] using
      (star_left_conjugate_le_conjugate hgBound v)
  have hnorm : ‖w‖ ^ 2 ≤ (δ : ℝ)⁻¹ * ‖star v * (Positive.cut δ b).1 * v‖ := by
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg w)
    simpa only [CStarRing.norm_star_mul_self, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (show (0 : ℝ) < δ from hδ)), pow_two] using hn
  have hvnorm : ‖star v * (Positive.cut δ b).1 * v‖ ≤ ‖a.1‖ + η := by
    have hn := norm_le_norm_sub_add (star v * (Positive.cut δ b).1 * v) a.1
    linarith
  refine ⟨w, by simpa only [hcompare] using hv, ?_⟩
  calc
    ‖w‖ ^ 2 ≤ (δ : ℝ)⁻¹ * ‖star v * (Positive.cut δ b).1 * v‖ := hnorm
    _ ≤ (δ : ℝ)⁻¹ * (‖a.1‖ + η) := mul_le_mul_of_nonneg_left hvnorm (le_of_lt (inv_pos.mpr (show (0 : ℝ) < δ from hδ)))
    _ = (‖a.1‖ + η) / (δ : ℝ) := by rw [div_eq_mul_inv, mul_comm]

theorem bounded_coordinate_witnesses (a b : ℕ → Positive A) (δ : ℝ≥0) (hδ : 0 < δ)
    (M : ℝ) (ha : ∀ n, ‖(a n).1‖ ≤ M)
    (h : ∀ n, CuntzBelow (a n) (Positive.cut δ (b n))) :
    ∃ w : ℕ → A, (∀ n, ‖w n‖ ^ 2 ≤ (M + 1) / (δ : ℝ)) ∧
      Filter.Tendsto (fun n => ‖star (w n) * (b n).1 * w n - (a n).1‖)
        Filter.atTop (𝓝 0) := by
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  choose w hw using fun n => bounded_witness (a n) (b n) δ hδ (h n) (η n) (hη n)
  refine ⟨w, fun n => ?_, ?_⟩
  · have hηle : η n ≤ 1 := by
      dsimp [η]
      apply (div_le_one (by positivity)).mpr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact (hw n).2.trans ((div_le_div_iff_of_pos_right (show (0 : ℝ) < δ from hδ)).mpr
      (add_le_add (ha n) hηle))
  · exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hw n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat

theorem cut_cuntzBelow (a : Positive A) (δ : ℝ≥0) (hδ : 0 < δ) :
    CuntzBelow (Positive.cut δ a) a := by
  obtain ⟨g, hgstar, hga, _⟩ := fixedCut_factorization a hδ
  intro η hη
  exact ⟨g, by simpa [hgstar, hga] using hη⟩

theorem cuntzBelow_iff_cuts (a b : Positive A) :
    CuntzBelow a b ↔ ∀ δ : ℝ≥0, 0 < δ → CuntzBelow (Positive.cut δ a) b := by
  constructor
  · intro h δ hδ
    exact (cut_cuntzBelow a δ hδ).trans h
  · exact CuntzBelow.of_cuts

end CuntzTrace

end

end OAI
