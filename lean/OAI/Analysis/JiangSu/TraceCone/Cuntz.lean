import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights

namespace OAI


noncomputable section
open scoped Topology NNReal
open Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem conjugate_norm_le [PartialOrder A] [StarOrderedRing A] (v x : A) :
    ‖star v * x * v‖ ≤ ‖v‖ ^ 2 * ‖x‖ := by
  calc
    ‖star v * x * v‖ ≤ ‖star v * x‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ (‖star v‖ * ‖x‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖v‖ ^ 2 * ‖x‖ := by rw [norm_star]; ring

variable [PartialOrder A]

namespace CuntzBelow

theorem zero [StarOrderedRing A] (b : Positive A) : CuntzBelow Positive.zero b := by
  intro ε hε
  exact ⟨0, by simpa [Positive.zero] using hε⟩

theorem refl [StarOrderedRing A] (a : Positive A) : CuntzBelow a a := by
  intro ε hε
  let U := CStarAlgebra.approximateUnit A
  have hU := CStarAlgebra.increasingApproximateUnit A
  have hl : ∀ᶠ u in U, ‖a.1 * u - a.1‖ < ε / 2 := by
    have ht := ((hU.tendsto_mul_left a.1).sub (tendsto_const_nhds (x := a.1))).norm
    have hzero : Tendsto (fun u => ‖a.1 * u - a.1‖) U (𝓝 0) := by simpa using ht
    exact (tendsto_order.mp hzero).2 (ε / 2) (by linarith)
  have hr : ∀ᶠ u in U, ‖u * a.1 - a.1‖ < ε / 2 := by
    have ht := ((hU.tendsto_mul_right a.1).sub (tendsto_const_nhds (x := a.1))).norm
    have hzero : Tendsto (fun u => ‖u * a.1 - a.1‖) U (𝓝 0) := by simpa using ht
    exact (tendsto_order.mp hzero).2 (ε / 2) (by linarith)
  obtain ⟨u, hu, hstar, hul, hur⟩ :=
    (hU.eventually_norm.and (hU.eventually_star_eq.and (hl.and hr))).exists
  refine ⟨u, ?_⟩
  rw [hstar]
  have heq : u * a.1 * u - a.1 = u * (a.1 * u - a.1) + (u * a.1 - a.1) := by
    noncomm_ring
  rw [heq]
  have hnorm : ‖u * (a.1 * u - a.1)‖ ≤ ‖a.1 * u - a.1‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem eq_zero [StarOrderedRing A] {a : Positive A}
    (h : CuntzBelow a Positive.zero) : a.1 = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ := h ‖a.1‖ (norm_pos_iff.mpr ha)
  simp [Positive.zero] at hv

theorem trans [StarOrderedRing A] {a b c : Positive A}
    (hab : CuntzBelow a b) (hbc : CuntzBelow b c) :
    CuntzBelow a c := by
  intro ε hε
  obtain ⟨v, hv⟩ := hab (ε / 2) (by linarith)
  let C := ‖v‖ ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  let δ := ε / (2 * (C + 1))
  have hd : 0 < 2 * (C + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hd
  obtain ⟨w, hw⟩ := hbc δ hδ
  have hδeq : δ * (2 * (C + 1)) = ε := div_mul_cancel₀ ε hd.ne'
  have hCδ : C * δ ≤ ε / 2 := by nlinarith
  have hbound : C * ‖star w * c.1 * w - b.1‖ ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hw.le hC).trans hCδ
  refine ⟨w * v, ?_⟩
  have heq : star (w * v) * c.1 * (w * v) - a.1 =
      star v * (star w * c.1 * w - b.1) * v + (star v * b.1 * v - a.1) := by
    rw [star_mul]
    noncomm_ring
  rw [heq]
  calc
    ‖star v * (star w * c.1 * w - b.1) * v + (star v * b.1 * v - a.1)‖ ≤
        ‖star v * (star w * c.1 * w - b.1) * v‖ + ‖star v * b.1 * v - a.1‖ :=
      norm_add_le _ _
    _ ≤ C * ‖star w * c.1 * w - b.1‖ + ‖star v * b.1 * v - a.1‖ :=
      add_le_add (conjugate_norm_le _ _) le_rfl
    _ < ε := by linarith

theorem of_tendsto [StarOrderedRing A] {a : Positive A} (aₙ : ℕ → Positive A) (b : Positive A)
    (ha : Tendsto aₙ atTop (𝓝 a)) (h : ∀ n, CuntzBelow (aₙ n) b) : CuntzBelow a b := by
  intro ε hε
  have ht := tendsto_subtype_rng.mp ha
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (ε / 2) (by linarith)
  obtain ⟨v, hv⟩ := h N (ε / 2) (by linarith)
  refine ⟨v, ?_⟩
  have hd : ‖(aₙ N).1 - a.1‖ < ε / 2 := by simpa [dist_eq_norm] using hN N le_rfl
  have heq : star v * b.1 * v - a.1 =
      (star v * b.1 * v - (aₙ N).1) + ((aₙ N).1 - a.1) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt ((add_lt_add hv hd).trans_eq (add_halves ε))

theorem of_cuts [StarOrderedRing A] {a b : Positive A}
    (h : ∀ ε : ℝ≥0, 0 < ε → CuntzBelow (Positive.cut ε a) b) : CuntzBelow a b := by
  let ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  apply of_tendsto (fun n => Positive.cut (ε n) a) b
  · apply Positive.tendsto_cut
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  · intro n
    apply h
    dsimp [ε]
    positivity

end CuntzBelow
end TraceCone

end


noncomputable section
open scoped NNReal Topology

namespace TraceCone

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
    (div_le_div_of_nonneg_left (le_max_right (t - δ) 0)
      (show (0 : ℝ) < δ from hδ) (le_max_right t (δ : ℝ)))

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
    _ ≤ (δ : ℝ)⁻¹ * (‖a.1‖ + η) :=
      mul_le_mul_of_nonneg_left hvnorm
        (le_of_lt (inv_pos.mpr (show (0 : ℝ) < δ from hδ)))
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

end TraceCone

end

end OAI
