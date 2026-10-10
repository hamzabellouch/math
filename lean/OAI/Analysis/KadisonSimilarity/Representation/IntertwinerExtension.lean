import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

/-- The actual operator equal to `T` on the range of `J` and zero on its
orthogonal complement. -/
def isometricExtension (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (J.toContinuousLinearMap.comp T).comp J.toContinuousLinearMap.adjoint

theorem isometricExtension_on_range (T : H →L[ℂ] H) (x : H) :
    isometricExtension J T (J x) = J (T x) := by
  have h := congrArg (fun S : H →L[ℂ] H => S x) J.adjoint_comp_self
  change J.toContinuousLinearMap.adjoint (J x) = x at h
  change J (T (J.toContinuousLinearMap.adjoint (J x))) = _
  rw [h]

theorem isometricExtension_sub (T U : H →L[ℂ] H) :
    isometricExtension J (T - U) = isometricExtension J T - isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [isometricExtension, ContinuousLinearMap.comp_apply, sub_apply,
    map_sub, LinearIsometry.coe_toContinuousLinearMap]

theorem isometricExtension_add (T U : H →L[ℂ] H) :
    isometricExtension J (T + U) = isometricExtension J T + isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [isometricExtension, ContinuousLinearMap.comp_apply, add_apply,
    map_add, LinearIsometry.coe_toContinuousLinearMap]

theorem isometricExtension_mul (T U : H →L[ℂ] H) :
    isometricExtension J (T * U) = isometricExtension J T * isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  change J (T (U (J.toContinuousLinearMap.adjoint x))) =
    isometricExtension J T (J (U (J.toContinuousLinearMap.adjoint x)))
  exact (isometricExtension_on_range J T _).symm

theorem isometricExtension_star (T : H →L[ℂ] H) :
    isometricExtension J (star T) = star (isometricExtension J T) := by
  simp only [isometricExtension, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem isometricExtension_injective : Function.Injective (isometricExtension J) := by
  intro T U h
  apply ContinuousLinearMap.ext
  intro x
  apply J.injective
  rw [← isometricExtension_on_range J T, ← isometricExtension_on_range J U, h]

theorem isometricExtension_norm (T : H →L[ℂ] H) : ‖isometricExtension J T‖ = ‖T‖ := by
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [LinearIsometry.coe_toContinuousLinearMap, J.norm_map, one_mul] using
      (le_rfl : ‖x‖ ≤ ‖x‖)
  have hJa : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hJ
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖J (T (J.toContinuousLinearMap.adjoint x))‖ ≤ _
    rw [J.norm_map]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((J.toContinuousLinearMap.adjoint.le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right hJa (norm_nonneg x))) (norm_nonneg T))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖T x‖ = ‖isometricExtension J T (J x)‖ := by
        rw [isometricExtension_on_range, J.norm_map]
      _ ≤ ‖isometricExtension J T‖ * ‖J x‖ := (isometricExtension J T).le_opNorm _
      _ = ‖isometricExtension J T‖ * ‖x‖ := by rw [J.norm_map]

/-- Compressing an operator supported on the isometric range and extending
it back recovers the original operator. -/
theorem isometricExtension_compression
    (Q : K →L[ℂ] K)
    (hleft : isometricExtension J 1 * Q = Q)
    (hright : Q * isometricExtension J 1 = Q) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap) = Q := by
  have hl (x : K) : J (J.toContinuousLinearMap.adjoint (Q x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hleft
  have hr (x : K) : Q (J (J.toContinuousLinearMap.adjoint x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hright
  apply ContinuousLinearMap.ext
  intro x
  change J (J.toContinuousLinearMap.adjoint
    (Q (J (J.toContinuousLinearMap.adjoint x)))) = Q x
  rw [hr, hl]

/-- Star-compatible intertwining transports commutation to the extension. -/
theorem isometricExtension_commutes
    (S : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hJ : J.toContinuousLinearMap.comp S = R.comp J.toContinuousLinearMap)
    (hJstar : J.toContinuousLinearMap.comp (star S) = (star R).comp J.toContinuousLinearMap)
    (T : H →L[ℂ] H) (hT : T * S = S * T) :
    isometricExtension J T * R = R * isometricExtension J T := by
  have ha : S.comp J.toContinuousLinearMap.adjoint =
      J.toContinuousLinearMap.adjoint.comp R := by
    have h := congrArg ContinuousLinearMap.adjoint hJstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hTx (x : H) : T (S x) = S (T x) := congrArg (fun L : H →L[ℂ] H => L x) hT
  have hJx (x : H) : J (S x) = R (J x) :=
    congrArg (fun L : H →L[ℂ] K => L x) hJ
  have hax (x : K) : S (J.toContinuousLinearMap.adjoint x) =
      J.toContinuousLinearMap.adjoint (R x) :=
    congrArg (fun L : K →L[ℂ] H => L x) ha
  apply ContinuousLinearMap.ext
  intro x
  change J (T (J.toContinuousLinearMap.adjoint (R x))) =
    R (J (T (J.toContinuousLinearMap.adjoint x)))
  rw [← hax, hTx, hJx]

/-- A star intertwiner transports the whole represented commutant. -/
theorem isometricExtension_commutes_representations
    {A : Type*} [CStarAlgebra A]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hJ : ∀ a, J.toContinuousLinearMap.comp (σ a) = (ρ a).comp J.toContinuousLinearMap)
    (T : H →L[ℂ] H) (hT : ∀ a, T * σ a = σ a * T) (a : A) :
    isometricExtension J T * ρ a = ρ a * isometricExtension J T := by
  apply isometricExtension_commutes J (σ a) (ρ a) (hJ a) ?_ T (hT a)
  simpa only [map_star] using hJ (star a)

/-- Pointwise intertwining is sufficient; form the equality of bounded
operators before specializing to a concrete L² model. -/
theorem isometricExtension_commutes_representations_of_apply
    {A : Type*} [CStarAlgebra A]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hJ : ∀ a x, J (σ a x) = ρ a (J x))
    (T : H →L[ℂ] H) (hT : ∀ a, T * σ a = σ a * T) (a : A) :
    isometricExtension J T * ρ a = ρ a * isometricExtension J T :=
  isometricExtension_commutes_representations J σ ρ
    (fun b => ContinuousLinearMap.ext (hJ b)) T hT a

/-- Compression through a star intertwiner preserves commutation with the
represented algebra. No support hypothesis is required. -/
theorem isometricCompression_commutes_representations_of_apply
    {A : Type*} [CStarAlgebra A]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hJ : ∀ a x, J (σ a x) = ρ a (J x))
    (Q : K →L[ℂ] K) (hQ : ∀ a, Q * ρ a = ρ a * Q) (a : A) :
    ((J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap) * σ a =
      σ a * ((J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap) := by
  have hs : J.toContinuousLinearMap.comp (star (σ a)) =
      (star (ρ a)).comp J.toContinuousLinearMap := by
    simpa only [map_star] using
      (ContinuousLinearMap.ext (hJ (star a)) :
        J.toContinuousLinearMap.comp (σ (star a)) =
          (ρ (star a)).comp J.toContinuousLinearMap)
  have ha : (σ a).comp J.toContinuousLinearMap.adjoint =
      J.toContinuousLinearMap.adjoint.comp (ρ a) := by
    have h := congrArg ContinuousLinearMap.adjoint hs
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hax (y : K) : σ a (J.toContinuousLinearMap.adjoint y) =
      J.toContinuousLinearMap.adjoint (ρ a y) :=
    congrArg (fun L : K →L[ℂ] H => L y) ha
  have hQx (y : K) : Q (ρ a y) = ρ a (Q y) :=
    congrArg (fun L : K →L[ℂ] K => L y) (hQ a)
  apply ContinuousLinearMap.ext
  intro x
  change J.toContinuousLinearMap.adjoint (Q (J (σ a x))) =
    σ a (J.toContinuousLinearMap.adjoint (Q (J x)))
  rw [hJ, hQx, ← hax]

end KadisonSimilarity

end

end OAI
