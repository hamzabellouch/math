import OAI.Geometry.SurfaceImmersion.Whitney.LoopDensityArcTriangle
import OAI.Geometry.SurfaceImmersion.Geometry.InteriorDensityLocal

namespace OAI

/-! Positive averaging densities when a symmetric circular arc surrounds the target. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem positive_density_near_of_arc_coverage
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2)) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} {m A : ℝ} (hc₀ : c b₀ = ![m, 0]) (hm : -1 < m) (hm1 : m < 1)
    (hA : Real.arccos m < A)
    (hcover : ∀ β ∈ Ioo (-A) A,
      ∃ t ∈ Ioo (0 : ℝ) 1, p b₀ t = ![Real.cos β, Real.sin β]) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b) := by
  let β := (Real.arccos m + min A Real.pi) / 2
  have hmin : Real.arccos m < min A Real.pi :=
    lt_min hA (Real.arccos_lt_pi.mpr hm)
  have hβlo : Real.arccos m < β := by dsimp [β]; linarith
  have hβhi : β < min A Real.pi := by dsimp [β]; linarith
  have hβpos : 0 < β := lt_of_le_of_lt (Real.arccos_nonneg m) hβlo
  have hβA : β < A := lt_of_lt_of_le hβhi (min_le_left _ _)
  have hβπ : β < Real.pi := lt_of_lt_of_le hβhi (min_le_right _ _)
  have hcos : Real.cos β < m := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg m) hβπ.le hβlo
    rwa [Real.cos_arccos hm.le hm1.le] at hh
  have hAp : 0 < A := lt_trans hβpos hβA
  obtain ⟨t₀, ht₀, hp₀⟩ := hcover 0 (by constructor <;> linarith)
  obtain ⟨t₁, ht₁, hp₁⟩ := hcover β ⟨by linarith, hβA⟩
  obtain ⟨t₂, ht₂, hp₂⟩ := hcover (-β) ⟨by linarith, by linarith⟩
  let t : Fin 3 → ℝ := ![t₀, t₁, t₂]
  have ht (i : Fin 3) : t i ∈ Ioo (0 : ℝ) 1 := by
    fin_cases i
    · exact ht₀
    · exact ht₁
    · exact ht₂
  have hpt (i : Fin 3) : p b₀ (t i) = arcTriangle (Real.cos β) (Real.sin β) i := by
    fin_cases i
    · simpa [t, arcTriangle] using hp₀
    · exact hp₁
    · simpa [t, arcTriangle, Real.cos_neg, Real.sin_neg] using hp₂
  have hcols : (fun i => augment (p b₀ (t i))) =
      fun i => augment (arcTriangle (Real.cos β) (Real.sin β) i) := by
    funext i
    rw [hpt]
  have hq : Real.cos β ≠ 1 := ne_of_lt (lt_trans hcos hm1)
  have hM : (columnOperator (fun i => augment (p b₀ (t i)))).IsInvertible := by
    rw [hcols]
    exact arcTriangle_invertible hq (Real.sin_pos_of_pos_of_lt_pi hβpos hβπ).ne'
  have hbary : columnOperator (fun i => augment (p b₀ (t i)))
      (arcWeights (Real.cos β) m) = augment (c b₀) := by
    rw [hcols, arcTriangle_barycenter hq, hc₀]
  have hpcont : Continuous (p b₀) := hp.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ψ, hψ, hper, hn, _hmass, ε, hε, hMψ, hw⟩ :=
    select_positive_moment_bumps hpcont ht hM (arcWeights_pos hcos hm1) hbary
  exact exists_positive_density_near hp hc hψ hn hper hε hMψ hw

end ClosedSurfaceR4.LoopDensity

end

end OAI
