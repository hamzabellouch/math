import OAI.Analysis.KadisonKastler.GraphScaleRows

namespace OAI

/-! # Directional graph bounds at all scales at least one

The integer row length is the ceiling of the squared scale. Both its
moment cost and its graph metric remain uniformly controlled.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_bounded_graphRow_signal_scale
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {c : ℝ} (hc : 1 ≤ c) {k : ℕ} (hk : 0 < k)
    (hck : c ^ 2 ≤ (k : ℝ)) (hkc : (k : ℝ) ≤ 2 * c ^ 2)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection M J Ω (c) = T)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ j (u v : unitary (H →L[ℂ] H)),
      (u : H →L[ℂ] H) ∈ (E j).algebra → (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) ∧ ‖operatorRow X‖ ≤ 131072 ∧
      ‖T‖ / 16 ≤ finiteRMS (fun i =>
        T (rescaledGraphVector J Ω (c) (X i))) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hs : T * rescaledGraphProjection M J Ω (Real.sqrt (c ^ 2)) = T := by
    simpa only [Real.sqrt_sq hc0] using hsupport
  obtain ⟨z, hznorm, hzgraph, hzsignal⟩ := exists_bounded_rescaledGraph_signal M Ω hΩ
    d E hmono hEM hirr hcentral J hJ hc2 T hT hs hcomm hvector
      (by simpa only [Real.sqrt_sq hc0] using hinvariant)
  simp only [Real.sqrt_sq hc0] at hzgraph hzsignal
  have hzsize : ‖z.val Ω‖ ^ 2 + k * ‖star z.val Ω‖ ^ 2 ≤ 480 := by
    rw [norm_rescaledGraphVector_sq] at hzgraph
    have hm := mul_le_mul_of_nonneg_right hkc (sq_nonneg ‖star z.val Ω‖)
    nlinarith [sq_nonneg ‖z.val Ω‖]
  obtain ⟨j, ω, hcost⟩ := exists_matrixGraphRow_cost_le_480 M Ω hΩ d E hmono hEM
    hirr hcentral hk z.val z.property hznorm hzsize
  let Y : Fin k → H →L[ℂ] H := matrixGraphRow (E j) z.val ω
  have hY : ∀ i, Y i ∈ M := fun i =>
    M.mul_mem (hEM j (matrixUnitSignedRepresentation_mem (E j) (ω i))) z.property
  have hnorm (i : Fin k) :
      ‖T (rescaledGraphVector J Ω (c) (Y i))‖ =
        ‖T (rescaledGraphVector J Ω (c) z.val)‖ :=
    matrixGraphRow_signal_eq M J hJ Ω _ T (E j) z.val z.property (hcomm j) (hvector j)
      (fun u hu => hinvariant j u 1 hu (E j).algebra.one_mem) ω i
  have hsig : ‖T‖ / 8 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω (c) (Y i))) := by
    rw [finiteRMS_eq_of_norm_eq _ (norm_nonneg _) hnorm]
    exact hzsignal
  refine ⟨clippedGraphRow 131072 Y, clippedGraphRow_mem M _ Y hY,
    norm_clippedGraphRow_le (by norm_num) Y, ?_⟩
  exact clippedGraphRow_signal_le_scale hk J Ω hck T Y hcost hsig


theorem graphProjectionDefect_le_of_row_scale
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    {c : ℝ} {k : ℕ} (hk : 0 < k) (hck : c ^ 2 ≤ (k : ℝ)) {γ : ℝ} (hγ : 0 ≤ γ)
    (X Z : Fin k → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (hZ : ∀ i, Z i ∈ N)
    (hXnorm : ‖operatorRow X‖ ≤ 131072)
    (happrox : ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖)
    (hsignal : ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ / 16 ≤
      finiteRMS (fun i => ((1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c))
          (rescaledGraphVector J Ω (c) (X i)))) :
    ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let A := 1 - rescaledGraphProjection N J Ω (c)
  let T := A * rescaledGraphProjection M J Ω (c)
  have hAnorm : ‖A‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ (TomitaGraphHilbert H) -
      (rescaledGraphSubspace N J Ω (c)).starProjection‖ ≤ 1
    rw [← Submodule.starProjection_orthogonal]
    exact Submodule.starProjection_norm_le _
  have he (i : Fin k) :
      T (rescaledGraphVector J Ω (c) (X i)) =
        A (rescaledGraphVector J Ω (c) (X i - Z i)) := by
    have hp := rescaledGraphProjection_vector M J Ω (c) ⟨X i, hX i⟩
    have hq := rescaledGraphProjection_vector N J Ω (c) ⟨Z i, hZ i⟩
    have hs := (rescaledGraphOperatorMap J Ω (c)).map_sub (X i) (Z i)
    change rescaledGraphVector J Ω (c) (X i - Z i) =
      rescaledGraphVector J Ω (c) (X i) -
        rescaledGraphVector J Ω (c) (Z i) at hs
    dsimp [T]
    have hAz : A (rescaledGraphVector J Ω (c) (Z i)) = 0 := by
      dsimp [A]
      rw [sub_apply, one_apply_eq_self, hq, sub_self]
    rw [mul_apply_eq_comp, hp, hs, map_sub, hAz, sub_zero]
  have hrms : finiteRMS (fun i => T (rescaledGraphVector J Ω (c) (X i))) ≤
      finiteRMS (fun i => rescaledGraphVector J Ω (c) (X i - Z i)) := by
    apply finiteRMS_mono
    intro i
    rw [he]
    calc
      _ ≤ ‖A‖ * ‖rescaledGraphVector J Ω (c) (X i - Z i)‖ := A.le_opNorm _
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hAnorm
          (norm_nonneg (rescaledGraphVector J Ω (c) (X i - Z i)))
  have hrow : operatorRow (fun i => X i - Z i) = operatorRow X - operatorRow Z := by
    ext i j
    rfl
  have hmetric := graphRowRMS_le_scale hk J Ω hck (fun i => X i - Z i)
  rw [hrow, hΩ, mul_one] at hmetric
  have hdist : ‖operatorRow X - operatorRow Z‖ ≤ γ * 131072 :=
    happrox.trans (mul_le_mul_of_nonneg_left hXnorm hγ)
  have hfinal := hrms.trans (hmetric.trans
    (mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg 2)))
  change ‖T‖ / 16 ≤ _ at hsignal
  change ‖T‖ ≤ _
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]


theorem norm_graphProjectionDefect_le_of_row_approx_scale
    (M N : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant)
    (hEN : ∀ n, (E n).algebra ≤ N.toStarSubalgebra)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    {c : ℝ} (hc : 1 ≤ c) {γ : ℝ} (hγ : 0 ≤ γ)
    (happrox : ∀ k : ℕ, ∀ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) →
      ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
        ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖) :
    ‖(1 - rescaledGraphProjection N J Ω (c)) *
        rescaledGraphProjection M J Ω (c)‖ ≤
      (16 * Real.sqrt 2 * 131072) * γ := by
  let k := Nat.ceil (c ^ 2)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hck : c ^ 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hk : 0 < k := by
    have hkR : 0 < (k : ℝ) := lt_of_lt_of_le (by linarith) hck
    exact_mod_cast hkR
  have hkc : (k : ℝ) ≤ 2 * c ^ 2 := by
    have hlt : (k : ℝ) < c ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg c)
    linarith
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
  obtain ⟨X, hX, hXnorm, hsignal⟩ := exists_bounded_graphRow_signal_scale M Ω hΩ d E hmono
    hEM hirr hcentral J hJ hc hk hck hkc T hT hs hcommM hvector (fun j u v hu hv =>
      rescaledGraphProjectionDefect_commutes M N (E j).algebra (hEM j) (hEN j)
        J hJ Ω c (hcommM j) (hcommN j) (hvector j) u v hu hv)
  obtain ⟨Z, hZ, hdist⟩ := happrox k X hX
  exact graphProjectionDefect_le_of_row_scale M N J Ω hΩ hk hck hγ X Z hX hZ hXnorm hdist hsignal


end

end KadisonKastler

end OAI
