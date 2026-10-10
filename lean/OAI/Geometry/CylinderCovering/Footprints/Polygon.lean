import OAI.Geometry.CylinderCovering.Footprints.PolygonDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Shapes

namespace OAI

open Set MeasureTheory

namespace CylinderCovering.Footprints

@[simp] lemma radialReflection_apply (p : ℝ × ℝ) :
    radialReflection p = (-p.1, p.2) := rfl

@[simp] lemma radialReflection_involutive (p : ℝ × ℝ) :
    radialReflection (radialReflection p) = p := by
  ext <;> simp

lemma radialReflection_injective : Function.Injective radialReflection :=
  Function.LeftInverse.injective radialReflection_involutive

theorem absoluteFootprint_split {m M d A B : ℝ}
    (hM : 0 ≤ M) (hAd : 0 ≤ A * d) :
    absoluteFootprint m M d A B =
      affineFootprint m (M + A * d) d 0 B ∪
      radialReflection '' affineFootprint (-m) (A * d) d 0 B := by
  ext p
  constructor
  · intro hp
    change -A * d ≤ p.1 ∧ p.1 ≤ M + A * d ∧
      |p.2 - m * p.1| ≤ d / 2 * |p.1| + B * d ^ 2 at hp
    by_cases hu : 0 ≤ p.1
    · left
      simp only [affineFootprint, mem_ofPred_eq, neg_zero, zero_mul, add_zero]
      exact ⟨hu, hp.2.1, by simpa only [abs_of_nonneg hu] using hp.2.2⟩
    · right
      refine ⟨(-p.1, p.2), ?_, by ext <;> simp⟩
      simp only [affineFootprint, mem_ofPred_eq, neg_zero, zero_mul, add_zero]
      refine ⟨by linarith, by linarith [hp.1], ?_⟩
      simpa only [neg_mul_neg, abs_of_neg (lt_of_not_ge hu)] using hp.2.2
  · rintro (hp | ⟨q, hq, rfl⟩)
    · simp only [affineFootprint, mem_ofPred_eq, neg_zero, zero_mul, add_zero] at hp
      change -A * d ≤ p.1 ∧ p.1 ≤ M + A * d ∧
        |p.2 - m * p.1| ≤ d / 2 * |p.1| + B * d ^ 2
      exact ⟨by nlinarith [hp.1], hp.2.1,
        by simpa only [abs_of_nonneg hp.1] using hp.2.2⟩
    · simp only [affineFootprint, mem_ofPred_eq, neg_zero, zero_mul, add_zero] at hq
      change -A * d ≤ -q.1 ∧ -q.1 ≤ M + A * d ∧
        |q.2 - m * -q.1| ≤ d / 2 * |-q.1| + B * d ^ 2
      refine ⟨by linarith [hq.2.1], by linarith [hq.1], ?_⟩
      simpa only [neg_mul, mul_neg, sub_neg_eq_add, abs_neg,
        abs_of_nonneg hq.1] using hq.2.2

theorem absoluteFootprint_eq_union_hulls {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    absoluteFootprint m M d A B =
      convexHull ℝ (range (positiveAbsoluteVertices m M d A B)) ∪
      convexHull ℝ (range (negativeAbsoluteVertices m d A B)) := by
  have hAd : 0 < A * d := mul_pos hA hd
  rw [absoluteFootprint_split hM hAd.le]
  rw [affineFootprint_eq_convexHull_trapezoid hd (by simpa using hB)
    (by simpa using add_pos_of_nonneg_of_pos hM hAd)]
  rw [affineFootprint_eq_convexHull_trapezoid hd (by simpa using hB)
    (by simpa using hAd)]
  change _ ∪ radialReflection.toAffineMap '' convexHull ℝ _ = _
  rw [radialReflection.toAffineMap.image_convexHull, ← range_comp]
  rfl

theorem positiveAbsoluteVertices_injective {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    Function.Injective (positiveAbsoluteVertices m M d A B) := by
  apply trapezoidVertices_injective hd (by simpa using hB)
  simpa using add_pos_of_nonneg_of_pos hM (mul_pos hA hd)

theorem negativeAbsoluteVertices_injective {m d A B : ℝ}
    (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    Function.Injective (negativeAbsoluteVertices m d A B) := by
  apply radialReflection_injective.comp
  apply trapezoidVertices_injective hd (by simpa using hB)
  simpa using mul_pos hA hd

theorem absoluteFootprint_piece_interiors_nonempty {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    (interior (affineFootprint m (M + A * d) d 0 B)).Nonempty ∧
      (interior (radialReflection '' affineFootprint (-m) (A * d) d 0 B)).Nonempty := by
  have hAd : 0 < A * d := mul_pos hA hd
  constructor
  · exact affineFootprint_interior_nonempty (add_nonneg hM hAd.le) hd le_rfl
      (by simpa using hB) (by simpa using add_pos_of_nonneg_of_pos hM hAd)
  · have hneg := affineFootprint_interior_nonempty (m := -m) hAd.le hd le_rfl
      (by simpa using hB) (by simpa using hAd)
    have hsurj : Function.Surjective radialReflection :=
      fun p => ⟨radialReflection p, radialReflection_involutive p⟩
    have hopen : IsOpenMap radialReflection :=
      radialReflection.toAffineMap.isOpenMap
        (by change Continuous (fun p : ℝ × ℝ => (-p.1, p.2)); fun_prop) hsurj
    exact (hneg.image radialReflection).mono (hopen.image_interior_subset _)

theorem absolute_polygon_statement : AbsolutePolygonStatement := by
  intro m M d A B hM hd hA hB
  exact ⟨absoluteFootprint_eq_union_hulls hM hd hA hB,
    positiveAbsoluteVertices_injective hM hd hA hB,
    negativeAbsoluteVertices_injective hd hA hB⟩

theorem absoluteFootprint_piece_intersection {m M d A B : ℝ}
    (hM : 0 ≤ M) (hAd : 0 ≤ A * d) :
    affineFootprint m (M + A * d) d 0 B ∩
        radialReflection '' affineFootprint (-m) (A * d) d 0 B =
      {p : ℝ × ℝ | p.1 = 0 ∧ |p.2| ≤ B * d ^ 2} := by
  ext p
  constructor
  · rintro ⟨hp, q, hq, heq⟩
    have hp0 : 0 ≤ p.1 := by simpa [affineFootprint] using hp.1
    have hq0 : 0 ≤ q.1 := by simpa [affineFootprint] using hq.1
    have heq0 : -q.1 = p.1 := congrArg Prod.fst heq
    have hpz : p.1 = 0 := by linarith
    refine ⟨hpz, ?_⟩
    simpa only [hpz, mul_zero, sub_zero, zero_add] using hp.2.2
  · rintro ⟨hpz, hpwidth⟩
    constructor
    · change -0 * d ≤ p.1 ∧ p.1 ≤ M + A * d + 0 * d ∧
        |p.2 - m * p.1| ≤ d / 2 * p.1 + B * d ^ 2
      simpa only [hpz, neg_zero, zero_mul, mul_zero, add_zero,
        sub_zero, zero_add] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ M + A * d ∧ |p.2| ≤ B * d ^ 2 from
          ⟨le_rfl, add_nonneg hM hAd, hpwidth⟩)
    · refine ⟨p, ?_, ?_⟩
      · change -0 * d ≤ p.1 ∧ p.1 ≤ A * d + 0 * d ∧
          |p.2 - (-m) * p.1| ≤ d / 2 * p.1 + B * d ^ 2
        simpa only [hpz, neg_zero, zero_mul, mul_zero, add_zero,
          sub_zero, zero_add] using
          (show (0 : ℝ) ≤ 0 ∧ 0 ≤ A * d ∧ |p.2| ≤ B * d ^ 2 from
            ⟨le_rfl, hAd, hpwidth⟩)
      · ext <;> simp [hpz]

theorem absoluteFootprint_piece_intersection_volume {m M d A B : ℝ}
    (hM : 0 ≤ M) (hAd : 0 ≤ A * d) :
    volume (affineFootprint m (M + A * d) d 0 B ∩
      radialReflection '' affineFootprint (-m) (A * d) d 0 B) = 0 := by
  rw [absoluteFootprint_piece_intersection hM hAd]
  have heq : {p : ℝ × ℝ | p.1 = 0 ∧ |p.2| ≤ B * d ^ 2} =
      ({0} : Set ℝ) ×ˢ Icc (- (B * d ^ 2)) (B * d ^ 2) := by
    ext p
    simp [abs_le]
  rw [heq]
  change (volume.prod volume) (({0} : Set ℝ) ×ˢ Icc (- (B * d ^ 2)) (B * d ^ 2)) = 0
  rw [Measure.prod_prod]
  simp

theorem absoluteArea_eq_piece_areas (M d A B : ℝ) :
    absoluteArea M d A B =
      affineArea (M + A * d) d 0 B + affineArea (A * d) d 0 B := by
  unfold absoluteArea affineArea
  ring

section AffineImage

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem absoluteFootprint_image_eq_union_hulls (f : (ℝ × ℝ) →ᵃ[ℝ] E)
    {m M d A B : ℝ} (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    f '' absoluteFootprint m M d A B =
      convexHull ℝ (range (f ∘ positiveAbsoluteVertices m M d A B)) ∪
      convexHull ℝ (range (f ∘ negativeAbsoluteVertices m d A B)) := by
  rw [absoluteFootprint_eq_union_hulls hM hd hA hB, image_union,
    f.image_convexHull, f.image_convexHull, ← range_comp, ← range_comp]

end AffineImage

end CylinderCovering.Footprints

end OAI
