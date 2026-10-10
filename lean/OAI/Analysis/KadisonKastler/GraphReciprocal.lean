import OAI.Analysis.KadisonKastler.GraphScaleDirection

namespace OAI

/-! # Reciprocal rescaling of closed Tomita graphs

Conjugating and interchanging the two coordinates sends the graph at c
to the graph at 1/c. This norm-preserving real-linear map transfers the
directional estimates to small positive scales.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def graphFlipValue (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    TomitaGraphHilbert H := WithLp.toLp 2 ![J (ξ 1), J (ξ 0)]

omit [CompleteSpace H] in
private theorem graphFlipValue_norm (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : TomitaGraphHilbert H) :
    ‖graphFlipValue J ξ‖ = ‖ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, graphFlipValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, J.norm_map]
  ring

omit [CompleteSpace H] in
private theorem conjugation_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (r : ℝ) (ξ : H) :
    J (r • ξ) = r • J ξ := by
  change J ((r : ℂ) • ξ) = (r : ℂ) • J ξ
  rw [J.map_smulₛₗ]
  simp

/-- The reciprocal graph symmetry, viewed as a real-linear isometry. -/
def graphReciprocalFlip (J : H ≃ₗᵢ⋆[ℂ] H) :
    TomitaGraphHilbert H →L[ℝ] TomitaGraphHilbert H :=
  LinearMap.mkContinuous
    { toFun := graphFlipValue J
      map_add' := by
        intro ξ η
        ext i
        fin_cases i <;> simp [graphFlipValue, map_add]
      map_smul' := by
        intro r ξ
        ext i
        fin_cases i <;> simp [graphFlipValue, conjugation_real_smul] }
    1 (fun ξ => by
      change ‖graphFlipValue J ξ‖ ≤ 1 * ‖ξ‖
      rw [one_mul, graphFlipValue_norm])

omit [CompleteSpace H] in
@[simp] theorem graphReciprocalFlip_norm (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : TomitaGraphHilbert H) : ‖graphReciprocalFlip J ξ‖ = ‖ξ‖ :=
  graphFlipValue_norm J ξ

/-- Exact reciprocal graph formula on the defining algebra vectors. -/
theorem graphReciprocalFlip_vector (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {c : ℝ} (hc : c ≠ 0) (x : H →L[ℂ] H) :
    graphReciprocalFlip J (rescaledGraphVector J Ω c x) =
      c • rescaledGraphVector J Ω c⁻¹ (star x) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change J (c • J (star x Ω)) = c • (star x Ω)
    rw [conjugation_real_smul, hJ]
  · change J (x Ω) = c • (c⁻¹ • J (star (star x) Ω))
    rw [star_star, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The reciprocal symmetry maps the entire closed graph to the
reciprocal closed graph, by continuity. -/
theorem graphReciprocalFlip_mem (P : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) {ξ : TomitaGraphHilbert H}
    (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    graphReciprocalFlip J ξ ∈ rescaledGraphSubspace P J Ω c⁻¹ := by
  have hh : IsClosed {v : TomitaGraphHilbert H |
      graphReciprocalFlip J v ∈ rescaledGraphSubspace P J Ω c⁻¹} :=
    (Submodule.isClosed_topologicalClosure _).preimage (graphReciprocalFlip J).continuous
  apply closure_minimal (s := Set.range (rescaledGraphMap P J Ω c)) ?_ hh hξ
  rintro _ ⟨x, rfl⟩
  change graphReciprocalFlip J (rescaledGraphVector J Ω c x.val) ∈
    rescaledGraphSubspace P J Ω c⁻¹
  rw [graphReciprocalFlip_vector J hJ Ω hc]
  exact (rescaledGraphSubspace P J Ω c⁻¹).smul_mem c
    (rescaledGraphVector_mem P J Ω c⁻¹ (star x))

private theorem norm_sub_projection_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : Submodule ℂ K) [S.HasOrthogonalProjection] (ξ η : K) (hη : η ∈ S) :
    ‖ξ - S.starProjection ξ‖ ≤ ‖ξ - η‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨η, hη⟩ : S)

private theorem graph_distance_le (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c : ℝ) (ξ η : TomitaGraphHilbert H)
    (hη : η ∈ rescaledGraphSubspace P J Ω c) :
    ‖(1 - rescaledGraphProjection P J Ω c) ξ‖ ≤ ‖ξ - η‖ := by
  change ‖ξ - (rescaledGraphSubspace P J Ω c).starProjection ξ‖ ≤ _
  exact norm_sub_projection_le _ ξ η hη

/-- A directional vector bound at the reciprocal scale gives the same
bound at the original positive scale. -/
theorem graph_directional_reciprocal
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {c : ℝ} (hc : 0 < c) {B : ℝ}
    (hbound : ∀ x : Algebra M,
      ‖(1 - rescaledGraphProjection N J Ω c⁻¹) (rescaledGraphVector J Ω c⁻¹ x.val)‖ ≤
        B * ‖rescaledGraphVector J Ω c⁻¹ x.val‖)
    (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  let ξ := rescaledGraphVector J Ω c⁻¹ (star x.val)
  let q := rescaledGraphProjection N J Ω c⁻¹ ξ
  have hq : q ∈ rescaledGraphSubspace N J Ω c⁻¹ :=
    (rescaledGraphSubspace N J Ω c⁻¹).starProjection_apply_mem ξ
  have hfq : graphReciprocalFlip J q ∈ rescaledGraphSubspace N J Ω c := by
    simpa only [inv_inv] using graphReciprocalFlip_mem N J hJ Ω (inv_ne_zero (ne_of_gt hc)) hq
  have hflip : c • graphReciprocalFlip J ξ = rescaledGraphVector J Ω c x.val := by
    dsimp [ξ]
    rw [graphReciprocalFlip_vector J hJ Ω (inv_ne_zero (ne_of_gt hc)), inv_inv,
      star_star, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  have hnorm : c * ‖ξ‖ = ‖rescaledGraphVector J Ω c x.val‖ := by
    rw [← hflip, norm_smul, Real.norm_eq_abs, abs_of_pos hc, graphReciprocalFlip_norm]
  have hd := graph_distance_le N J Ω c (rescaledGraphVector J Ω c x.val)
    (c • graphReciprocalFlip J q) ((rescaledGraphSubspace N J Ω c).smul_mem c hfq)
  have he : ‖rescaledGraphVector J Ω c x.val - c • graphReciprocalFlip J q‖ = c * ‖ξ - q‖ := by
    rw [← hflip, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      graphReciprocalFlip_norm]
  rw [he] at hd
  have hb := hbound (star x)
  change ‖ξ - q‖ ≤ B * ‖ξ‖ at hb
  calc
    _ ≤ c * ‖ξ - q‖ := hd
    _ ≤ c * (B * ‖ξ‖) := mul_le_mul_of_nonneg_left hb hc.le
    _ = B * ‖rescaledGraphVector J Ω c x.val‖ := by rw [← hnorm]; ring

end

end KadisonKastler

end OAI
