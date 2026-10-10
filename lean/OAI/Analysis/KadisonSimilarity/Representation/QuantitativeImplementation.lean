import OAI.Analysis.KadisonSimilarity.Derivation.RectangularDerivations

namespace OAI

/-!
# Quantitative implementation from a triangular similarity

Conjugating an orthogonal projection gives the implementing corner directly.
The norm bound is the condition number of the given similarity.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed similarity gives a commuting projection with norm bounded by its
condition number. -/
theorem exists_commuting_projection_norm (π : BoundedUnitalHom A H)
    (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a : A, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)))
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ (∀ a, Commute P (π.1 a)) ∧
      ‖P‖ ≤ ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ := by
  let e := ContinuousLinearEquiv.ofUnit S
  let U (a : A) : H →L[ℂ] H :=
    e.toContinuousLinearMap * π.1 a * e.symm.toContinuousLinearMap
  let N : ClosedSubmodule ℂ H := M.mapEquiv e
  have hU : ∀ a, U (star a) = star (U a) := hS
  have hN : ∀ a x, x ∈ N → U a x ∈ N := by
    intro a x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π.1 a y, hM a y hy, by simp [U, mul_apply_eq_comp]⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := e.symm.toContinuousLinearMap.comp (Q.comp e.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (e x)
    rcases h with ⟨y, hy, he⟩
    change e.symm (Q (e x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : e x ∈ N := ⟨x, hx, rfl⟩
    change e.symm (Q (e x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  have hcomm (a : A) : Commute P (π.1 a) := by
    have hq := orthogonal_projection_commutes U hU N hN a
    change P * π.1 a = π.1 a * P
    ext x
    have h := congrArg (fun T : H →L[ℂ] H => e.symm (T (e x))) hq.eq
    simpa [P, Q, U, mul_apply_eq_comp] using h
  refine ⟨P, hmem, hfix, hcomm, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  calc
    ‖P x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖Q (e x)‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ :=
      mul_le_mul_of_nonneg_left (N.toSubmodule.norm_starProjection_apply_le _) (norm_nonneg _)
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm x) (norm_nonneg _)
    _ = (‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖) * ‖x‖ := by
      change ‖(↑S⁻¹ : H →L[ℂ] H)‖ * (‖(S : H →L[ℂ] H)‖ * ‖x‖) = _
      ring

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The implementing upper-right corner inherits the condition-number bound. -/
theorem rectangular_inner_of_similarity_norm
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (S : (RectangularSum F K →L[ℂ] RectangularSum F K)ˣ)
    (hS : ∀ a : A,
      (S : RectangularSum F K →L[ℂ] RectangularSum F K) *
        (rectangularRepresentation ρ σ δ hδ).1 (star a) * ↑S⁻¹ =
      star ((S : RectangularSum F K →L[ℂ] RectangularSum F K) *
        (rectangularRepresentation ρ σ δ hδ).1 a * ↑S⁻¹)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ ‖(S : RectangularSum F K →L[ℂ] RectangularSum F K)‖ *
        ‖(↑S⁻¹ : RectangularSum F K →L[ℂ] RectangularSum F K)‖ := by
  let π := rectangularRepresentation ρ σ δ hδ
  let M : ClosedSubmodule ℂ (RectangularSum F K) :=
    ⟨(WithLp.sndL 2 ℂ F K).ker, (WithLp.sndL 2 ℂ F K).isClosed_ker⟩
  have hM : ∀ a x, x ∈ M → π.1 a x ∈ M := by
    intro a x hx
    change x.snd = 0 at hx
    change (rectangularTriangular (ρ a) (δ a) (σ a) x).snd = 0
    simp [hx]
  obtain ⟨P, hm, hf, hp, hnorm⟩ := exists_commuting_projection_norm π S hS M hM
  let q : K →L[ℂ] F := (WithLp.fstL 2 ℂ F K).comp (P.comp rectangularInr)
  have hzero (x : RectangularSum F K) : (P x).snd = 0 := hm x
  have hfix (x : F) : P (rectangularInl x) = rectangularInl x :=
    hf _ (by change (rectangularInl x).snd = 0; simp [rectangularInl])
  have hdecomp (x : RectangularSum F K) :
      x = rectangularInl x.fst + rectangularInr x.snd := by
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [rectangularInl, rectangularInr]
  have hfst (x : RectangularSum F K) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q, rectangularInl]
  have hqnorm : ‖q‖ ≤ ‖P‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
    intro x
    calc
      ‖q x‖ ≤ ‖P (rectangularInr x)‖ := WithLp.norm_fst_le F _
      _ ≤ ‖P‖ * ‖rectangularInr (F := F) x‖ := P.le_opNorm _
      _ = ‖P‖ * ‖x‖ := by
        change ‖P‖ * ‖WithLp.toLp 2 (0, x)‖ = _
        rw [WithLp.norm_toLp_snd]
  refine ⟨-q, ?_, (by simpa using hqnorm.trans hnorm)⟩
  intro a
  ext x
  have h := congrArg
    (fun T : RectangularSum F K →L[ℂ] RectangularSum F K =>
      (T (rectangularInr x)).fst) (hp a).eq
  change (P (rectangularTriangular (ρ a) (δ a) (σ a) (rectangularInr x))).fst =
    (rectangularTriangular (ρ a) (δ a) (σ a) (P (rectangularInr x))).fst at h
  rw [hfst, rectangularTriangular_fst, rectangularTriangular_snd,
    rectangularTriangular_fst, hzero] at h
  have hq (x : K) : (P (rectangularInr x)).fst = q x := rfl
  rw [hq] at h
  have hfst0 : (rectangularInr (F := F) x).fst = 0 := (rectangularInr_apply x).1
  have hsnd : (rectangularInr (F := F) x).snd = x := (rectangularInr_apply x).2
  simp only [hfst0, hsnd, map_zero, zero_add, add_zero] at h
  change δ a x = (-q) (σ a x) - ρ a ((-q) x)
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end KadisonSimilarity

end

end OAI
