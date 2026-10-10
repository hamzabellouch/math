import OAI.Analysis.KadisonKastler.PreparedRightGraphBridge
import OAI.Analysis.KadisonKastler.ProductBoundaryCocycle

namespace OAI

/-! # The actual conjugate right algebra

An involutive conjugate-linear Hilbert isometry transports a concrete von
Neumann algebra to its exact operator image. Conjugating an ambient
contractive projection twice transports injectivity as well. These constructions preserve the represented algebraic operations.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem conjugationOperator_add (J : H ≃ₗᵢ⋆[ℂ] H) (a b : H →L[ℂ] H) :
    conjugationOperator J (a + b) = conjugationOperator J a + conjugationOperator J b := by
  ext ξ
  exact map_add J _ _

omit [CompleteSpace H] in
theorem conjugationOperator_smul (J : H ≃ₗᵢ⋆[ℂ] H) (z : ℂ) (a : H →L[ℂ] H) :
    conjugationOperator J (z • a) = star z • conjugationOperator J a := by
  ext ξ
  exact J.map_smulₛₗ z (a (J ξ))

omit [CompleteSpace H] in
theorem conjugateIsometry_inner (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) :
    inner ℂ (J x) (J y) = star (inner ℂ x y) := by
  have hp : J x + Complex.I • J y = J (x - Complex.I • y) := by
    rw [map_sub, J.map_smulₛₗ]
    simp only [Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hm : J x - Complex.I • J y = J (x + Complex.I • y) := by
    rw [map_add, J.map_smulₛₗ]
    simp only [Complex.conj_I, neg_smul, sub_eq_add_neg]
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
    simp only [← RCLike.re_eq_complex_re]
    rw [
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ),
      re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)]
    rw [← map_add J, ← map_sub J, J.norm_map, J.norm_map]
  · rw [Complex.star_def, Complex.conj_im]
    simp only [← RCLike.im_eq_complex_im]
    rw [
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ),
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (𝕜 := ℂ)]
    simp only [RCLike.I_to_complex]
    rw [hm, hp, J.norm_map, J.norm_map]
    ring

/-- Conjugation by an involutive anti-isometry preserves operator adjoints. -/
theorem conjugationOperator_star (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a : H →L[ℂ] H) :
    conjugationOperator J (star a) = star (conjugationOperator J a) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (conjugationOperator J (star a) x) =
    inner ℂ y ((conjugationOperator J a).adjoint x)
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ y (J (star a (J x))) = inner ℂ (J (a (J y))) x
  have hl := conjugateIsometry_inner J (J y) (star a (J x))
  have hr := conjugateIsometry_inner J (a (J y)) (J x)
  rw [hJ y] at hl
  rw [hJ x] at hr
  rw [hl, hr]
  congr 1
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

omit [CompleteSpace H] in
private theorem centralizer_image_conjugationOperator
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (S : Set (H →L[ℂ] H)) :
    Set.centralizer (conjugationOperator J '' S) =
      conjugationOperator J '' Set.centralizer S := by
  ext x
  constructor
  · intro hx
    refine ⟨conjugationOperator J x, ?_, conjugationOperator_twice J hJ x⟩
    intro y hy
    have he := congrArg (conjugationOperator J) (hx _ ⟨y, hy, rfl⟩)
    rw [conjugationOperator_mul J hJ, conjugationOperator_mul J hJ,
      conjugationOperator_twice J hJ] at he
    exact he
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    rw [← conjugationOperator_mul J hJ, ← conjugationOperator_mul J hJ, hy w hw]

private def conjugateRightStarAlgebra (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := conjugationOperator J '' (R : Set (H →L[ℂ] H))
  zero_mem' := ⟨0, R.zero_mem, by ext ξ; simp [conjugationOperator_apply]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, R.add_mem ha hb, conjugationOperator_add J a b⟩
  one_mem' := ⟨1, R.one_mem, conjugationOperator_one J hJ⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, R.mul_mem ha hb, conjugationOperator_mul J hJ a b⟩
  algebraMap_mem' z := by
    refine ⟨star z • (1 : H →L[ℂ] H), R.toStarSubalgebra.smul_mem R.one_mem _, ?_⟩
    rw [conjugationOperator_smul, star_star, conjugationOperator_one J hJ]
    simp only [Algebra.smul_def, mul_one]
  star_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨star a, R.toStarSubalgebra.star_mem' ha, conjugationOperator_star J hJ a⟩

/-- The actual image `J R J`, as a concrete von Neumann algebra. -/
def conjugateRightAlgebra (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := conjugateRightStarAlgebra J hJ R
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (conjugationOperator J '' (R : Set (H →L[ℂ] H)))) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H))
    rw [centralizer_image_conjugationOperator J hJ,
      centralizer_image_conjugationOperator J hJ, R.centralizer_centralizer]

theorem conjugateRightAlgebra_coe (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) :
    (conjugateRightAlgebra J hJ R : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H)) := rfl

/-- Conjugating a complex-linear map twice restores complex linearity. -/
def conjugateOperatorMap (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun x => conjugationOperator J (E (conjugationOperator J x))
      map_add' := by
        intro x y
        rw [conjugationOperator_add, map_add, conjugationOperator_add]
      map_smul' := by
        intro z x
        change conjugationOperator J (E (conjugationOperator J (z • x))) =
          z • conjugationOperator J (E (conjugationOperator J x))
        rw [conjugationOperator_smul, map_smul, conjugationOperator_smul, star_star] }
    ‖E‖ (fun x => by
      change ‖conjugationOperator J (E (conjugationOperator J x))‖ ≤ ‖E‖ * ‖x‖
      rw [norm_conjugationOperator J hJ]
      exact (E.le_opNorm _).trans_eq (by rw [norm_conjugationOperator J hJ]))

@[simp]
theorem conjugateOperatorMap_apply (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    conjugateOperatorMap J hJ E x = conjugationOperator J (E (conjugationOperator J x)) := rfl

theorem norm_conjugateOperatorMap_le (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    ‖conjugateOperatorMap J hJ E‖ ≤ ‖E‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E)
  intro x
  rw [conjugateOperatorMap_apply, norm_conjugationOperator J hJ]
  exact (E.le_opNorm _).trans_eq (by rw [norm_conjugationOperator J hJ])

/-- An actual ambient contractive projection onto `R` gives one onto `J R J`. -/
theorem isInjective_conjugateRightAlgebra
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (R : VonNeumannAlgebra H) (hR : IsInjective R) :
    IsInjective (conjugateRightAlgebra J hJ R) := by
  obtain ⟨E, hE, hmem, hfix⟩ := hR
  refine ⟨conjugateOperatorMap J hJ E, (norm_conjugateOperatorMap_le J hJ E).trans hE, ?_, ?_⟩
  · intro x
    exact ⟨E (conjugationOperator J x), hmem _, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    rw [conjugateOperatorMap_apply, conjugationOperator_twice J hJ, hfix a ha]

local instance conjugateRightGraphOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance conjugateRightGraphStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance conjugateRightGraphOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance conjugateRightGraphOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The generic preparation theorem needs only injectivity of the common
left algebra; the right algebra and its injectivity are constructed. -/
theorem exists_preparedRight_graph_comparison_of_injective
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N) (hRinj : IsInjective R)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    {ρ : ℝ} (hnear : NearInclusion (conjugateRightAlgebra J hJ R) N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra J hJ R ≤ (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
        (G : Algebra (unitaryConjugateAlgebra (star w) N) →ₗ[ℂ] (H →L[ℂ] H))
        (γ : ℝ),
        (∀ x, F x ∈ unitaryConjugateAlgebra (star w) N) → (∀ x, G x ∈ M) →
        0 ≤ γ →
        CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ →
        CompletelyBoundedBy
          ((unitaryConjugateAlgebra (star w) N).toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M J Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  exact exists_preparedRight_graph_comparison hpub M N R (conjugateRightAlgebra J hJ R)
    J hJ Ω hΩ d E hmono hR hRM hRN hirr hrightM hvector
    (conjugateRightAlgebra_coe J hJ R) (isInjective_conjugateRightAlgebra J hJ R hRinj)
    hnear hρ hgap

end

end KadisonKastler

end OAI
