import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteCodimension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

namespace OAI

/-! # Finite-rank decomposition of a contracting time step

Orthogonal projection onto finitely many vectors turns the proved weak-null
bound into an operator-norm contraction with a finite-rank remainder.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem homogeneousOperator_isCompact_of_finiteRange (a k : ℝ)
    (K : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hK : FiniteDimensional ℝ (LinearMap.range K.toLinearMap)) :
    IsCompactOperator K := by
  let V := LinearMap.range K.toLinearMap
  let : FiniteDimensional ℝ V := hK
  let A : HomogeneousY a k →L[ℝ] V :=
    K.codRestrict V (fun x => ⟨x, rfl⟩)
  have hA : IsCompactOperator A := isCompactOperator_of_locallyCompactSpace_dom A
  exact hA.clm_comp V.subtypeL

theorem homogeneousOperator_finiteRank_bound (a k r R : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hr : 0 ≤ r) (hR : 0 < R) (hrR : r < R ^ 2)
    (T : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hweak : ∀ u : ℕ → HomogeneousY a k, (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖T (u j)‖ ^ 2 < r + ε) :
    ∃ B K : HomogeneousY a k →L[ℝ] HomogeneousY a k,
      T = B + K ∧ ‖B‖ < R ∧ FiniteDimensional ℝ (LinearMap.range K.toLinearMap) := by
  let δ := (R ^ 2 - r) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  obtain ⟨d, N, hsmall⟩ := homogeneousOperator_finite_annihilator a k r δ ha1 hk hδ T hweak
  let V : Submodule ℂ (HomogeneousY a k) :=
    Submodule.span ℂ (Set.range (fun i : Fin (N + 1) => d i.val))
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let P : HomogeneousY a k →L[ℝ] HomogeneousY a k := V.starProjection.restrictScalars ℝ
  let Q : HomogeneousY a k →L[ℝ] HomogeneousY a k := Vᗮ.starProjection.restrictScalars ℝ
  let B := T.comp Q
  let K := T.comp P
  have hmember (i : ℕ) (hi : i ≤ N) : d i ∈ V :=
    Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
  have hQ (u : HomogeneousY a k) : ‖T (Q u)‖ ^ 2 ≤ (r + δ) * ‖u‖ ^ 2 := by
    have h := hsmall (Q u) (fun i hi =>
      Submodule.inner_right_of_mem_orthogonal (K := V) (hmember i hi) (Vᗮ.starProjection_apply_mem u))
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (Vᗮ.norm_starProjection_apply_le u) 2)
      (by dsimp only [δ]; linarith))
  have hB : ‖B‖ ≤ Real.sqrt (r + δ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro u
    have h := hQ u
    have hs : (Real.sqrt (r + δ)) ^ 2 = r + δ := Real.sq_sqrt (by dsimp only [δ]; linarith)
    have hp : 0 ≤ Real.sqrt (r + δ) * ‖u‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    change ‖T (Q u)‖ ≤ _
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    calc
      _ ≤ (r + δ) * ‖u‖ ^ 2 := h
      _ = (Real.sqrt (r + δ) * ‖u‖) ^ 2 := by rw [mul_pow, hs]
  have hs1 : Real.sqrt (r + δ) < R := by
    apply (Real.sqrt_lt' hR).mpr
    dsimp only [δ]
    nlinarith
  refine ⟨B, K, ?_, hB.trans_lt hs1, ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    change T u = T (Q u) + T (P u)
    rw [← map_add]
    congr 1
    exact ((add_comm _ _).trans (Submodule.starProjection_add_starProjection_orthogonal (K := V) u)).symm
  · let A : V →L[ℝ] HomogeneousY a k := T.comp (V.subtypeL.restrictScalars ℝ)
    let F : HomogeneousY a k →L[ℝ] V := V.orthogonalProjectionOnto.restrictScalars ℝ
    have he : K.toLinearMap = A.toLinearMap.comp F.toLinearMap := rfl
    have hle : LinearMap.range K.toLinearMap ≤ LinearMap.range A.toLinearMap := by
      rw [he]
      exact LinearMap.range_comp_le_range _ _
    exact FiniteDimensional.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)

theorem homogeneousOperator_finiteRank_contraction (a k r : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hr : 0 ≤ r) (hr1 : r < 1)
    (T : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hweak : ∀ u : ℕ → HomogeneousY a k, (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖T (u j)‖ ^ 2 < r + ε) :
    ∃ B K : HomogeneousY a k →L[ℝ] HomogeneousY a k,
      T = B + K ∧ ‖B‖ < 1 ∧ FiniteDimensional ℝ (LinearMap.range K.toLinearMap) :=
  homogeneousOperator_finiteRank_bound a k r 1 ha1 hk hr zero_lt_one
    (by simpa only [one_pow] using hr1) T hweak

end DefocusingNLS

end OAI
