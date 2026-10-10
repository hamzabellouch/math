import OAI.Analysis.KadisonKastler.BoundedGraphRow

namespace OAI

/-! # Directional graph estimates from actual row approximants

A bounded detecting row in the first algebra is compared with one row
in the second algebra. Only the stated rectangular approximation is
used; no amplification of ordinary Kadison--Kastler distance is assumed.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A detecting row and its actual approximant bound the directional
orthogonal graph defect. -/
theorem graphProjectionDefect_le_of_row
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    {k : ℕ} (hk : 0 < k) {γ : ℝ} (hγ : 0 ≤ γ)
    (X Z : Fin k → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (hZ : ∀ i, Z i ∈ N)
    (hXnorm : ‖operatorRow X‖ ≤ 131072)
    (happrox : ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖)
    (hsignal : ‖(1 - rescaledGraphProjection N J Ω (Real.sqrt (k : ℝ))) *
        rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ))‖ / 16 ≤
      finiteRMS (fun i => ((1 - rescaledGraphProjection N J Ω (Real.sqrt (k : ℝ))) *
        rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ)))
          (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i)))) :
    ‖(1 - rescaledGraphProjection N J Ω (Real.sqrt (k : ℝ))) *
        rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ))‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let A := 1 - rescaledGraphProjection N J Ω (Real.sqrt (k : ℝ))
  let T := A * rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ))
  have hAnorm : ‖A‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ (TomitaGraphHilbert H) -
      (rescaledGraphSubspace N J Ω (Real.sqrt (k : ℝ))).starProjection‖ ≤ 1
    rw [← Submodule.starProjection_orthogonal]
    exact Submodule.starProjection_norm_le _
  have he (i : Fin k) :
      T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i)) =
        A (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i - Z i)) := by
    have hp := rescaledGraphProjection_vector M J Ω (Real.sqrt (k : ℝ)) ⟨X i, hX i⟩
    have hq := rescaledGraphProjection_vector N J Ω (Real.sqrt (k : ℝ)) ⟨Z i, hZ i⟩
    have hs := (rescaledGraphOperatorMap J Ω (Real.sqrt (k : ℝ))).map_sub (X i) (Z i)
    change rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i - Z i) =
      rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i) -
        rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Z i) at hs
    dsimp [T]
    have hAz : A (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Z i)) = 0 := by
      dsimp [A]
      rw [sub_apply, one_apply_eq_self, hq, sub_self]
    rw [mul_apply_eq_comp, hp, hs, map_sub, hAz, sub_zero]
  have hrms : finiteRMS (fun i => T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i))) ≤
      finiteRMS (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i - Z i)) := by
    apply finiteRMS_mono
    intro i
    rw [he]
    calc
      _ ≤ ‖A‖ * ‖rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i - Z i)‖ := A.le_opNorm _
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hAnorm
          (norm_nonneg (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i - Z i)))
  have hrow : operatorRow (fun i => X i - Z i) = operatorRow X - operatorRow Z := by
    ext i j
    rfl
  have hmetric := graphRowRMS_le hk J Ω (fun i => X i - Z i)
  rw [hrow, hΩ, mul_one] at hmetric
  have hdist : ‖operatorRow X - operatorRow Z‖ ≤ γ * 131072 :=
    happrox.trans (mul_le_mul_of_nonneg_left hXnorm hγ)
  have hfinal := hrms.trans (hmetric.trans
    (mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg 2)))
  change ‖T‖ / 16 ≤ _ at hsignal
  change ‖T‖ ≤ _
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- Actual matrix-orbit flattening and complete row approximation give
the directional bound at every integer square rescaling. -/
theorem norm_graphProjectionDefect_le_of_row_approx
    (M N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant)
    (hEN : ∀ n, (E n).algebra ≤ N.toStarSubalgebra)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    {k : ℕ} (hk : 0 < k) {γ : ℝ} (hγ : 0 ≤ γ)
    (happrox : ∀ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) →
      ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
        ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖) :
    ‖(1 - rescaledGraphProjection N J Ω (Real.sqrt (k : ℝ))) *
        rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ))‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let c := Real.sqrt (k : ℝ)
  let T := (1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c
  by_cases hT : T = 0
  · change ‖T‖ ≤ _
    rw [hT, norm_zero]
    positivity
  have hs : T * rescaledGraphProjection M J Ω c = T := by
    dsimp [T]
    have hid : rescaledGraphProjection M J Ω c * rescaledGraphProjection M J Ω c =
        rescaledGraphProjection M J Ω c :=
      (isStarProjection_starProjection (U := rescaledGraphSubspace M J Ω c)).isIdempotentElem.eq
    rw [mul_assoc, hid]
  obtain ⟨X, hX, hXnorm, hsignal⟩ := exists_bounded_graphRow_signal M Ω hΩ d E hmono
    hEM hirr hc J hJ hk T hT hs hcommM hvector (fun j u v hu hv =>
      rescaledGraphProjectionDefect_commutes M N (E j).algebra (hEM j) (hEN j)
        J hJ Ω c (hcommM j) (hcommN j) (hvector j) u v hu hv)
  obtain ⟨Z, hZ, hdist⟩ := happrox X hX
  exact graphProjectionDefect_le_of_row M N J Ω hΩ hk hγ X Z hX hZ hXnorm hdist hsignal

end

end KadisonKastler

end OAI
