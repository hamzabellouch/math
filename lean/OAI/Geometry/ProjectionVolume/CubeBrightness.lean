import OAI.Geometry.ProjectionVolume.PolytopeCauchy
import OAI.Geometry.ProjectionVolume.EuclideanVolume
import OAI.Geometry.ProjectionVolume.FacetAreas

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092

def euclideanCube (d : ℕ) : Set (Euclidean d) :=
  WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1

theorem mem_euclideanCube {d : ℕ} (x : Euclidean d) :
    x ∈ euclideanCube d ↔ (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨WithLp.ofLp x, hx, WithLp.toLp_ofLp 2 x⟩

theorem euclideanCube_isCompact (d : ℕ) : IsCompact (euclideanCube d) :=
  isCompact_Icc.image (PiLp.continuous_toLp 2 _)

theorem euclideanCube_volume (d : ℕ) : volume (euclideanCube d) = 1 := by
  rw [euclideanCube, volume_euclidean_image]
  simp [Real.volume_Icc_pi]

def cubeNormal {d : ℕ} : Fin d ⊕ Fin d → Euclidean d
  | .inl i => -EuclideanSpace.single i 1
  | .inr i => EuclideanSpace.single i 1

def cubeOffset {d : ℕ} : Fin d ⊕ Fin d → ℝ
  | .inl _ => 0
  | .inr _ => 1

theorem cube_constraints (d : ℕ) :
    {x : Euclidean d | ∀ i, ⟪cubeNormal i, x⟫ ≤ cubeOffset i} = euclideanCube d := by
  ext x
  simp [mem_euclideanCube, Sum.forall, cubeNormal, cubeOffset,
    EuclideanSpace.inner_single_left]

def cubePolytope (d : ℕ) : HPolytope d (Fin d ⊕ Fin d) where
  normal := cubeNormal
  offset := cubeOffset
  normal_unit i := by cases i <;> simp [cubeNormal]
  compact := by rw [cube_constraints]; exact euclideanCube_isCompact d
  strict_feasible := by
    refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), ?_⟩
    intro i
    cases i <;> norm_num [cubeNormal, cubeOffset, EuclideanSpace.inner_single_left]
  distinct := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · congr 1
      by_contra h
      have hc := congrArg (fun p : Euclidean d × ℝ => p.1 i) hij
      simp [cubeNormal, h] at hc
    · have hc := congrArg Prod.snd hij
      norm_num [cubeOffset] at hc
    · have hc := congrArg Prod.snd hij
      norm_num [cubeOffset] at hc
    · congr 1
      by_contra h
      have hc := congrArg (fun p : Euclidean d × ℝ => p.1 i) hij
      simp [cubeNormal, h] at hc

theorem cubePolytope_body (d : ℕ) : (cubePolytope d).body = euclideanCube d :=
  cube_constraints d

theorem cubePolytope_face_lower {d : ℕ} (i : Fin d) :
    (cubePolytope d).face (.inl i) = {x | x ∈ euclideanCube d ∧ x i = 0} := by
  ext x
  change (x ∈ (cubePolytope d).body ∧ ⟪-EuclideanSpace.single i 1, x⟫ = 0) ↔ _
  rw [cubePolytope_body]
  simp [EuclideanSpace.inner_single_left]

theorem cubePolytope_face_upper {d : ℕ} (i : Fin d) :
    (cubePolytope d).face (.inr i) = {x | x ∈ euclideanCube d ∧ x i = 1} := by
  ext x
  change (x ∈ (cubePolytope d).body ∧ ⟪EuclideanSpace.single i 1, x⟫ = 1) ↔ _
  rw [cubePolytope_body]
  simp [EuclideanSpace.inner_single_left]

theorem cube_lower_face_chart (n : ℕ) (i : Fin (n + 1)) :
    facetEmbedding n i 0 '' euclideanCube n = (cubePolytope (n + 1)).face (.inl i) := by
  rw [cubePolytope_face_lower]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change facetEmbedding n i 0 x ∈ euclideanCube (n + 1) ∧ facetEmbedding n i 0 x i = 0
    rw [mem_euclideanCube] at hx ⊢
    simp [facetEmbedding, Fin.forall_iff_succAbove i, hx]
  · rintro ⟨hy, hi⟩
    refine ⟨WithLp.toLp 2 (i.removeNth y), ?_, ?_⟩
    · rw [mem_euclideanCube] at hy ⊢
      exact ⟨fun j => hy.1 (i.succAbove j), fun j => hy.2 (i.succAbove j)⟩
    · ext j
      induction j using i.succAboveCases <;> simp [facetEmbedding, hi]

theorem cube_lower_face_area (n : ℕ) (i : Fin (n + 1)) :
    μHE[n] ((cubePolytope (n + 1)).face (.inl i)) = 1 := by
  rw [← cube_lower_face_chart]
  have h := (facetEmbedding n i 0).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (euclideanCube n)
  simpa only [finrank_euclideanSpace_fin, facetEmbedding_normDet_zero,
    ENNReal.ofReal_one, euclideanCube_volume, mul_one] using h

theorem cube_upper_face_eq_vadd {d : ℕ} (i : Fin d) :
    (cubePolytope d).face (.inr i) =
      EuclideanSpace.single i (1 : ℝ) +ᵥ (cubePolytope d).face (.inl i) := by
  rw [cubePolytope_face_upper, cubePolytope_face_lower]
  ext y
  constructor
  · rintro ⟨hy, hi⟩
    refine ⟨y - EuclideanSpace.single i 1, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_euclideanCube] at hy ⊢
      constructor <;> intro j
      · by_cases hj : j = i
        · subst j; simp [PiLp.sub_apply, hi]
        · simpa [PiLp.sub_apply, PiLp.single_apply, hj] using hy.1 j
      · by_cases hj : j = i
        · subst j; simp [PiLp.sub_apply, hi]
        · simpa [PiLp.sub_apply, PiLp.single_apply, hj] using hy.2 j
    · simp [PiLp.sub_apply, hi]
    · change EuclideanSpace.single i 1 + (y - EuclideanSpace.single i 1) = y
      abel
  · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanCube] at hx ⊢
      constructor <;> intro j
      · by_cases hj : j = i
        · subst j; simp [vadd_eq_add, PiLp.add_apply, hi]
        · simpa [vadd_eq_add, PiLp.add_apply, PiLp.single_apply, hj] using hx.1 j
      · by_cases hj : j = i
        · subst j; simp [vadd_eq_add, PiLp.add_apply, hi]
        · simpa [vadd_eq_add, PiLp.add_apply, PiLp.single_apply, hj] using hx.2 j
    · simp [vadd_eq_add, PiLp.add_apply, hi]

theorem cube_upper_face_area (n : ℕ) (i : Fin (n + 1)) :
    μHE[n] ((cubePolytope (n + 1)).face (.inr i)) = 1 := by
  rw [cube_upper_face_eq_vadd, measure_vadd, cube_lower_face_area]

theorem cube_faceArea {d : ℕ} (hd : 0 < d) (i : Fin d ⊕ Fin d) :
    (cubePolytope d).faceArea i = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  cases i with
  | inl i =>
    change (μHE[n] ((cubePolytope (n + 1)).face (.inl i))).toReal = 1
    rw [cube_lower_face_area, ENNReal.toReal_one]
  | inr i =>
    change (μHE[n] ((cubePolytope (n + 1)).face (.inr i))).toReal = 1
    rw [cube_upper_face_area, ENNReal.toReal_one]

theorem euclideanCube_brightness {d : ℕ} (hd : 0 < d) (u : Euclidean d) :
    brightness (euclideanCube d) u = ∑ i, |u i| := by
  rw [← cubePolytope_body, (cubePolytope d).brightness_eq_sum]
  simp only [cube_faceArea hd, one_mul, Fintype.sum_sum_type]
  simp only [cubePolytope, cubeNormal, inner_neg_right, abs_neg,
    EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial]
  ring

theorem euclideanCube_diagonal_brightness {d : ℕ} (hd : 0 < d) :
    brightness (euclideanCube d) (WithLp.toLp 2 (1 : Fin d → ℝ)) = d := by
  rw [euclideanCube_brightness hd]
  simp

theorem euclideanCube_diagonal_extrusion {d : ℕ} (hd : 0 < d) :
    (volume (euclideanCube d +
      segment ℝ (0 : Euclidean d) (WithLp.toLp 2 (1 : Fin d → ℝ)))).toReal =
        (volume (euclideanCube d)).toReal +
          brightness (euclideanCube d) (WithLp.toLp 2 (1 : Fin d → ℝ)) := by
  rw [euclideanCube_volume, ENNReal.toReal_one, euclideanCube_diagonal_brightness hd]
  rw [euclideanCube, volume_euclidean_cube_add_diagonal d hd]
  rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one]
  ring

theorem euclideanCube_diagonal_projectionBody_support {d : ℕ} (hd : 0 < d) :
    SupportGeometry.support (projectionBody (euclideanCube d))
      (innerSL ℝ (WithLp.toLp 2 (1 : Fin d → ℝ))) = d := by
  rw [← cubePolytope_body, (cubePolytope d).projectionBody_support, cubePolytope_body,
    euclideanCube_diagonal_brightness hd]

end Paper092

end

end OAI
