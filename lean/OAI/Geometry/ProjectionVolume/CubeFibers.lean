import OAI.Geometry.ProjectionVolume.CubeBrightness
import Mathlib.Algebra.Order.Group.Pointwise.Interval

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092

def lineFiber {d : ℕ} (K : Set (Euclidean d)) (x u : Euclidean d) : Set ℝ :=
  {t | x + t • u ∈ K}

theorem lineFiber_add_segment {d : ℕ} (K : Set (Euclidean d)) (x u : Euclidean d) :
    lineFiber (K + segment ℝ 0 u) x u = lineFiber K x u + Icc (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨y, hy, z, hz, hsum⟩
    rw [segment_eq_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    simp only [smul_zero, zero_add] at hsum
    refine ⟨t - s, ?_, s, hs, sub_add_cancel t s⟩
    change x + (t - s) • u ∈ K
    have heq : x + (t - s) • u = y := by
      rw [sub_smul, ← add_sub_assoc, ← hsum, add_sub_cancel_right]
    rwa [heq]
  · rintro ⟨r, hr, s, hs, rfl⟩
    refine ⟨x + r • u, hr, s • u, ?_, ?_⟩
    · rw [segment_eq_image]
      exact ⟨s, hs, by simp⟩
    · rw [add_smul]
      abel_nf

theorem projection_add_parallel_segment {d : ℕ} (K : Set (Euclidean d)) (u : Euclidean d) :
    (normalHyperplane u).orthogonalProjectionOnto '' (K + segment ℝ 0 u) =
      (normalHyperplane u).orthogonalProjectionOnto '' K := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, v, hv, rfl⟩, rfl⟩
    rw [segment_eq_image] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    simp only [smul_zero, zero_add]
    refine ⟨x, hx, ?_⟩
    exact ((projection_eq_iff_parallel u (x + t • u) x).mpr ⟨t, rfl⟩).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, 0, left_mem_segment ℝ _ _, add_zero x⟩, rfl⟩

theorem cube_lineFiber_eq_interval {d : ℕ} (hd : 0 < d) (x : Euclidean d) :
    ∃ a b : ℝ, lineFiber (euclideanCube d) x (WithLp.toLp 2 (1 : Fin d → ℝ)) = Icc a b := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let a := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => -x i)
  let b := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin d => 1 - x i)
  refine ⟨a, b, ?_⟩
  ext t
  simp only [lineFiber, mem_ofPred_eq, mem_euclideanCube, PiLp.add_apply, PiLp.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one, mem_Icc,
    a, b, Finset.sup'_le_iff, Finset.le_inf'_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    exact ⟨fun i => by linarith [h.1 i], fun i => by linarith [h.2 i]⟩
  · intro h
    exact ⟨fun i => by linarith [h.1 i], fun i => by linarith [h.2 i]⟩

theorem cube_lineFiber_extrusion_intervals {d : ℕ} (hd : 0 < d) (x : Euclidean d)
    (hne : (lineFiber (euclideanCube d) x (WithLp.toLp 2 (1 : Fin d → ℝ))).Nonempty) :
    ∃ a b : ℝ, a ≤ b ∧
      lineFiber (euclideanCube d) x (WithLp.toLp 2 (1 : Fin d → ℝ)) = Icc a b ∧
      lineFiber (euclideanCube d + segment ℝ 0 (WithLp.toLp 2 (1 : Fin d → ℝ))) x
        (WithLp.toLp 2 (1 : Fin d → ℝ)) = Icc a (b + 1) := by
  obtain ⟨a, b, hab⟩ := cube_lineFiber_eq_interval hd x
  have hle : a ≤ b := nonempty_Icc.mp (hab ▸ hne)
  refine ⟨a, b, hle, hab, ?_⟩
  rw [lineFiber_add_segment, hab, Set.Icc_add_Icc hle (by norm_num : (0 : ℝ) ≤ 1), add_zero]

theorem interval_line_image {d : ℕ} (x u : Euclidean d) {a b : ℝ} (hab : a ≤ b) :
    (fun t : ℝ => x + t • u) '' Icc a b = segment ℝ (x + a • u) (x + b • u) := by
  let f : ℝ →ᵃ[ℝ] Euclidean d :=
    AffineMap.const ℝ ℝ x + (LinearMap.toSpanSingleton ℝ (Euclidean d) u).toAffineMap
  have hf (t : ℝ) : f t = x + t • u := rfl
  simpa only [hf, segment_eq_Icc hab] using image_segment ℝ f a b

theorem interval_line_length_increase {d : ℕ} (x u : Euclidean d) {a b : ℝ} (hab : a ≤ b) :
    dist (x + a • u) (x + (b + 1) • u) = dist (x + a • u) (x + b • u) + ‖u‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub (s : ℝ) : x + a • u - (x + s • u) = (a - s) • u := by
    rw [sub_smul]
    abel_nf
  rw [hsub, hsub, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : a - (b + 1) ≤ 0),
    abs_of_nonpos (by linarith : a - b ≤ 0)]
  ring

def lineFiberLength {d : ℕ} (K : Set (Euclidean d)) (x u : Euclidean d) : ℝ :=
  (μH[1] ((fun t : ℝ => x + t • u) '' lineFiber K x u)).toReal

theorem lineFiberLength_of_eq_Icc {d : ℕ} (K : Set (Euclidean d)) (x u : Euclidean d)
    {a b : ℝ} (hab : a ≤ b) (h : lineFiber K x u = Icc a b) :
    lineFiberLength K x u = dist (x + a • u) (x + b • u) := by
  rw [lineFiberLength, h, interval_line_image x u hab, hausdorffMeasure_segment]
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]

theorem cube_lineFiberLength_extrusion {d : ℕ} (hd : 0 < d) (x : Euclidean d)
    (hne : (lineFiber (euclideanCube d) x (WithLp.toLp 2 (1 : Fin d → ℝ))).Nonempty) :
    lineFiberLength (euclideanCube d + segment ℝ 0 (WithLp.toLp 2 (1 : Fin d → ℝ))) x
        (WithLp.toLp 2 (1 : Fin d → ℝ)) =
      lineFiberLength (euclideanCube d) x (WithLp.toLp 2 (1 : Fin d → ℝ)) +
        ‖WithLp.toLp 2 (1 : Fin d → ℝ)‖ := by
  obtain ⟨a, b, hab, hcube, hextrusion⟩ := cube_lineFiber_extrusion_intervals hd x hne
  rw [lineFiberLength_of_eq_Icc _ _ _ (by linarith : a ≤ b + 1) hextrusion,
    lineFiberLength_of_eq_Icc _ _ _ hab hcube]
  exact interval_line_length_increase _ _ hab

end Paper092

end

end OAI
