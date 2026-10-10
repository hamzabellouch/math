import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SpanCoefficientControl
import OAI.Analysis.RieszRectifiability.Flatness.AffineTubeMass

namespace OAI

/-!
A linear map that contracts a unit direction sends vectors close to a lower-dimensional subspace.
Orthogonal projection extends this estimate to the image of a tube around a subspace.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem contracted_direction_image_near_lower_subspace
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ[ℝ] F) (u : E) (hu : ‖u‖ = 1)
    (κ : ℝ) (hκ : 0 ≤ κ) (hTu : ‖T u‖ ≤ κ) :
    ∃ Q : Submodule ℝ F, Module.finrank ℝ Q < Module.finrank ℝ E ∧
      ∀ x : E, ∃ y ∈ Q, dist (T x) y ≤ κ * ‖x‖ := by
  let W : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let Q := W.map T
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W < Module.finrank ℝ E := by
    have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu0] at h
    change 1 + Module.finrank ℝ W = Module.finrank ℝ E at h
    omega
  refine ⟨Q, (Submodule.finrank_map_le T W).trans_lt hdim, ?_⟩
  intro x
  let v := x - inner ℝ u x • u
  have hv : v ∈ W := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    dsimp [v]
    simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      hu, one_pow, mul_one, sub_self]
  have hinner : |inner ℝ u x| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs, hu, one_mul] using! norm_inner_le_norm (𝕜 := ℝ) u x
  refine ⟨T v, ⟨v, hv, rfl⟩, ?_⟩
  calc
    dist (T x) (T v) = ‖inner ℝ u x • T u‖ := by
      rw [dist_eq_norm, ← map_sub]
      have hsub : x - v = inner ℝ u x • u := by dsimp [v]; abel
      rw [hsub, map_smul]
    _ = |inner ℝ u x| * ‖T u‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |inner ℝ u x| * κ := mul_le_mul_of_nonneg_left hTu (abs_nonneg _)
    _ ≤ ‖x‖ * κ := mul_le_mul_of_nonneg_right hinner hκ
    _ = κ * ‖x‖ := mul_comm _ _

theorem contracted_plane_tube_image_subset {n d : ℕ}
    (S : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ S = n)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ) (R δ : ℝ) :
    ∃ Q : Submodule ℝ (Ambient n), Module.finrank ℝ Q < n ∧
      T '' affineTube S.toAffineSubspace R δ ⊆
        affineTube Q.toAffineSubspace R (δ + κ * R) := by
  obtain ⟨Q, hQ, hnear⟩ := contracted_direction_image_near_lower_subspace
    (T.comp S.subtype) u hu κ hκ hTu
  refine ⟨Q, hdim ▸ hQ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
  let p : S := S.orthogonalProjectionOnto x
  have hpx : dist x (p : Ambient d) < δ := by
    change ‖x - S.starProjection x‖ < δ
    have heq : x - S.starProjection x = Sᗮ.starProjection x := by
      have h := S.starProjection_add_starProjection_orthogonal x
      exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
    rw [heq, ← submodule_infDist_eq_normal_projection S x]
    exact hx.2
  have hpR : ‖p‖ ≤ R := (S.norm_starProjection_apply_le x).trans hxR
  obtain ⟨y, hy, hpy⟩ := hnear p
  have hTxp : dist (T x) (T (p : Ambient d)) ≤ dist x (p : Ambient d) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hT _
  have hTxy : dist (T x) y < δ + κ * R := by
    have ht := dist_triangle (T x) (T (p : Ambient d)) y
    have hb : dist (T (p : Ambient d)) y ≤ κ * R :=
      hpy.trans (mul_le_mul_of_nonneg_left hpR hκ)
    linarith
  refine ⟨?_, (infDist_le_dist_of_mem hy).trans_lt hTxy⟩
  change dist (T x) 0 ≤ R
  simpa only [dist_zero_right] using! (hT x).trans hxR

theorem contracted_plane_tube_image_real_measure_bound {n d : ℕ}
    (S : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ S = n)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (μ : Measure (Ambient n)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    μ.real (T '' affineTube S.toAffineSubspace R δ) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * ((δ + κ * R) / R) * R ^ n := by
  obtain ⟨Q, hQ, hsub⟩ := contracted_plane_tube_image_subset S hdim T hT u hu κ hκ hTu R δ
  let τ := (δ + κ * R) / R
  have hτ : 0 < τ := div_pos (by positivity) hR
  have hτ1 : τ ≤ 1 := (div_le_one hR).mpr hwidth
  have hw : τ * R = δ + κ * R := div_mul_cancel₀ _ hR.ne'
  have hplane : IsAffineNPlane (Module.finrank ℝ Q) Q.toAffineSubspace := by
    refine ⟨⟨0, Q.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction]
  have hbound := lower_dimensional_affineTube_bound μ C hg Q.toAffineSubspace
    hplane hQ R τ hR hτ hτ1
  have hfinite : μ (affineTube Q.toAffineSubspace R (δ + κ * R)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact affineTube_measure_bound μ C hg Q.toAffineSubspace hplane R (δ + κ * R)
      hR.le (by positivity)
  calc
    _ ≤ μ.real (affineTube Q.toAffineSubspace R (δ + κ * R)) :=
      ENNReal.toReal_mono hfinite (measure_mono hsub)
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ (Module.finrank ℝ Q)) * τ * R ^ n := by
      simpa only [hw] using! hbound
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * τ * R ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR.le n)
      apply mul_le_mul_of_nonneg_right _ hτ.le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hQ.le)
        (mul_nonneg hg.1 (by positivity))

end

end RieszRectifiability

end OAI
