import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairPacking

namespace OAI

/-! # Image paths centered at their actual common starting point -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def basedImage (F : G → G) (a g : G) : G := (F a)⁻¹ * F g

omit [IsTopologicalGroup G] in
theorem basedImage_dist (F : G → G) (a g h : G) :
    dist (basedImage F a g) (basedImage F a h) = dist (F g) (F h) :=
  dist_mul_left _ _ _

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [MetricSpace G] [NormedSpace ℝ W] in
theorem basedImage_height (π : G →* Multiplicative W) (F : G → G) (a g : G) :
    (π (basedImage F a g)).toAdd = (π (F g)).toAdd - (π (F a)).toAdd := by
  simp only [basedImage, map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

/-- Centering the image gives a path based at the identity, preserves all
relative heights, and multiplies both coarse metric constants by the same
Lipschitz constant. -/
theorem basedImage_map_path (F : G → G) {K : ℝ≥0} (hF : LipschitzWith K F)
    {a g : G} (γ : Path a g) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    ∃ η : Path (1 : G) (basedImage F a g),
      (∀ t, η t = basedImage F a (γ t)) ∧ PathMetricBound η (K * L) (K * κ) := by
  have hc : Continuous (basedImage F a) := continuous_const.mul hF.continuous
  let η : Path (1 : G) (basedImage F a g) := (γ.map hc).cast (by simp [basedImage]) rfl
  refine ⟨η, (fun _ => rfl), ?_⟩
  intro s t
  change dist (basedImage F a (γ s)) (basedImage F a (γ t)) ≤ _
  rw [basedImage_dist]
  calc
    _ ≤ (K : ℝ) * dist (γ s) (γ t) := hF.dist_le_mul _ _
    _ ≤ (K : ℝ) * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) K.coe_nonneg
    _ = _ := by ring

omit [IsTopologicalGroup G] in
/-- A based image of a separated source set has the same cardinality and
unit-separated points, by the actual lower quasi-isometry inequality. -/
theorem basedImage_separated_card [DecidableEq G] {Λ : ℝ≥0} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (a : G) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    (s.image (basedImage p.val.1 a)).card = s.card ∧
      ∀ x ∈ s.image (basedImage p.val.1 a),
        ∀ y ∈ s.image (basedImage p.val.1 a), x ≠ y → 1 ≤ dist x y := by
  classical
  have hd (x y : G) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
      1 < dist (basedImage p.val.1 a x) (basedImage p.val.1 a y) := by
    rw [basedImage_dist]
    exact normalizedPair_image_dist_gt_one p hΛ (hsep x hx y hy hne)
  constructor
  · apply Finset.card_image_iff.mpr
    intro x hx y hy he
    by_contra hne
    have hh := hd x y hx hy hne
    rw [he, dist_self] at hh
    linarith
  · intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (hd u v hu hv (fun he => hne (congrArg _ he))).le

end PolycyclicRecognition

end

end OAI
