import OAI.Analysis.KadisonKastler.FiniteBimodularBound

namespace OAI

/-! # Comparing tracial conjugations in common position

The two conjugations are supplied as actual conjugate-linear isometries.
Common right-action commutation remains an explicit structural premise;
the distance estimate itself follows from unit-ball approximation and
the proved finite bimodular test.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex-linear comparison operator of two conjugations. -/
def tracialConjugationDefect (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) : H →L[ℂ] H :=
  (J₂ : H →L⋆[ℂ] H).comp (J₁ : H →L⋆[ℂ] H) - 1

omit [CompleteSpace H] in
@[simp]
theorem tracialConjugationDefect_apply (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    tracialConjugationDefect J₁ J₂ ξ = J₂ (J₁ ξ) - ξ := rfl

omit [CompleteSpace H] in
/-- Composing by an involutive isometry identifies the two operator norms. -/
theorem norm_tracialConjugationDefect (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) :
    ‖tracialConjugationDefect J₁ J₂‖ =
      ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ := by
  let D : H →L⋆[ℂ] H := (J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)
  have he (ξ : H) : ‖tracialConjugationDefect J₁ J₂ ξ‖ = ‖D (J₁ ξ)‖ := by
    change ‖J₂ (J₁ ξ) - ξ‖ = ‖J₁ (J₁ ξ) - J₂ (J₁ ξ)‖
    rw [hJ₁ ξ, norm_sub_rev]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro ξ
    rw [he]
    exact (D.le_opNorm (J₁ ξ)).trans_eq (by rw [J₁.norm_map])
  · change ‖D‖ ≤ ‖tracialConjugationDefect J₁ J₂‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ξ
    calc
      ‖D ξ‖ = ‖tracialConjugationDefect J₁ J₂ (J₁ ξ)‖ := by
        rw [he, hJ₁ ξ]
      _ ≤ ‖tracialConjugationDefect J₁ J₂‖ * ‖J₁ ξ‖ :=
        (tracialConjugationDefect J₁ J₂).le_opNorm _
      _ = _ := by rw [J₁.norm_map]

/-- Close unit balls bound the comparison operator on every bounded
algebra vector by twice the Kadison--Kastler tolerance. -/
theorem tracialConjugationDefect_unitBall_bound
    {M N : VonNeumannAlgebra H} (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ y : Algebra N, J₂ (y.val Ω) = (star y).val Ω)
    {b : ℝ} (hb : kkDistance M N < b) (x : Algebra M) (hx : ‖x‖ ≤ 1) :
    ‖tracialConjugationDefect J₁ J₂ (x.val Ω)‖ ≤ 2 * b := by
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx (M := M) (N := N)
    (x := x.val) ⟨x.property, hx⟩ hb
  let z : Algebra N := ⟨y, hy.1⟩
  have hz : J₂ ((star z).val Ω) = z.val Ω := by
    simpa only [star_star] using hN (star z)
  rw [tracialConjugationDefect_apply, hM]
  calc
    _ ≤ ‖J₂ ((star x).val Ω) - J₂ ((star z).val Ω)‖ +
        ‖J₂ ((star z).val Ω) - x.val Ω‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖(star x).val Ω - (star z).val Ω‖ + ‖z.val Ω - x.val Ω‖ := by
      rw [← map_sub, J₂.norm_map, hz]
    _ ≤ ‖(star x).val - (star z).val‖ * ‖Ω‖ + ‖z.val - x.val‖ * ‖Ω‖ := by
      exact add_le_add (( (star x).val - (star z).val).le_opNorm Ω)
        ((z.val - x.val).le_opNorm Ω)
    _ = 2 * ‖x.val - y‖ := by
      change ‖star x.val - star y‖ * ‖Ω‖ + ‖y - x.val‖ * ‖Ω‖ = _
      rw [← star_sub, norm_star, norm_sub_rev y, hΩ]
      ring
    _ ≤ 2 * b := by linarith

/-- The norm-768 tracial-conjugation estimate under common module actions
commuting with the comparison operator. -/
theorem norm_tracialConjugations_sub_le
    {M N : VonNeumannAlgebra H} {R : Type*} [CStarAlgebra R]
    (τ : FaithfulTracialState (Algebra M)) (ι : Algebra M →ₗ[ℂ] H)
    (hι : ∀ x, ‖ι x‖ = traceTwoNorm τ x) (hιdense : DenseRange ι)
    (hτ : FiniteVectorTrace τ) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hιΩ : ∀ x : Algebra M, ι x = x.val Ω)
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₁ : Function.Involutive J₁)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ y : Algebra N, J₂ (y.val Ω) = (star y).val Ω)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ a : Algebra M, (∀ r : R, φ r * a = a * φ r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (L Q : unitary R → unitary (H →L[ℂ] H))
    (hL : ∀ (u : unitary R) (x : Algebra M), ι (φ u * x) = (L u : H →L[ℂ] H) (ι x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), ι (x * φ u) = (Q u : H →L[ℂ] H) (ι x))
    (hTL : ∀ u, Commute (tracialConjugationDefect J₁ J₂) (L u : H →L[ℂ] H))
    (hTQ : ∀ u, Commute (tracialConjugationDefect J₁ J₂) (Q u : H →L[ℂ] H))
    {b : ℝ} (hb : kkDistance M N < b) :
    ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ 768 * b := by
  have hb0 : 0 ≤ b := (kkDistance_nonneg M N).trans hb.le
  have htest (x y : Algebra M) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      ‖inner ℂ (tracialConjugationDefect J₁ J₂ (ι x)) (ι y)‖ ≤ 2 * b := by
    have hTx : ‖tracialConjugationDefect J₁ J₂ (ι x)‖ ≤ 2 * b := by
      rw [hιΩ]
      exact tracialConjugationDefect_unitBall_bound J₁ J₂ Ω hΩ hM hN hb x hx
    have hiy : ‖ι y‖ ≤ 1 := by
      calc
        ‖ι y‖ = ‖y.val Ω‖ := by rw [hιΩ]
        _ ≤ ‖y.val‖ * ‖Ω‖ := y.val.le_opNorm Ω
        _ = ‖y‖ := by rw [hΩ, mul_one]; rfl
        _ ≤ 1 := hy
    calc
      _ ≤ ‖tracialConjugationDefect J₁ J₂ (ι x)‖ * ‖ι y‖ := norm_inner_le_norm _ _
      _ ≤ (2 * b) * 1 := mul_le_mul hTx hiy (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hnorm := opNorm_le_of_irreducible_bimodular_tests τ ι hι hιdense hτ φ hirr
    (tracialConjugationDefect J₁ J₂) L Q hL hQ hTL hTQ htest
  rw [norm_tracialConjugationDefect J₁ J₂ hJ₁] at hnorm
  linarith

end

end KadisonKastler

end OAI
