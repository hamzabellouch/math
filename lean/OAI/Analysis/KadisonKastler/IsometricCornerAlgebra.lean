import OAI.Analysis.KadisonSimilarity.Representation.CompressedBicommutant
import OAI.Analysis.KadisonKastler.IsometryRangeCoordinates

namespace OAI

/-! # The von Neumann algebra on a reducing isometric range -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (J : E →ₗᵢ[ℂ] H)

def rangeCompression (T : H →L[ℂ] H) : E →L[ℂ] E :=
  J.toContinuousLinearMap.adjoint.comp (T.comp J.toContinuousLinearMap)

theorem rangeCompression_intertwines_apply
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, isometricExtension J 1 * a.val = a.val * isometricExtension J 1)
    (a : A) (v : E) : J (rangeCompression J a v) = a.val (J v) := by
  have h := congrArg (fun T : H →L[ℂ] H => T (J v)) (hA a)
  change J (J.toContinuousLinearMap.adjoint (a.val (J v))) = a.val (isometricExtension J 1 (J v)) at h
  simpa only [rangeCompression, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, isometricExtension_on_range,
    one_apply_eq_self] using h

def rangeCompressionStarHom (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, isometricExtension J 1 * a.val = a.val * isometricExtension J 1) :
    A →⋆ₐ[ℂ] (E →L[ℂ] E) where
  toFun a := rangeCompression J a
  map_zero' := by ext v; simp [rangeCompression]
  map_one' := by
    ext v
    exact isometry_adjoint_self_apply J v
  map_add' a b := by ext v; simp [rangeCompression]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro v
    change J.toContinuousLinearMap.adjoint (a.val (b.val (J v))) =
      J.toContinuousLinearMap.adjoint (a.val (J (rangeCompression J b v)))
    rw [rangeCompression_intertwines_apply J A hA]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro v
    change J.toContinuousLinearMap.adjoint (c • J v) = c • v
    rw [map_smul, isometry_adjoint_self_apply]
  map_star' a := by
    simp only [rangeCompression, StarMemClass.coe_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem rangeCompressionStarHom_intertwines (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, isometricExtension J 1 * a.val = a.val * isometricExtension J 1)
    (a : A) : J.toContinuousLinearMap.comp (rangeCompressionStarHom J A hA a) =
      a.val.comp J.toContinuousLinearMap := by
  ext v
  exact rangeCompression_intertwines_apply J A hA a v

variable (M : VonNeumannAlgebra H) (hJM : isometricExtension J 1 ∈ M)

include hJM in
theorem rangeProjection_commutes_commutant (a : M.commutant.toStarSubalgebra) :
    isometricExtension J 1 * a.val = a.val * isometricExtension J 1 :=
  (VonNeumannAlgebra.mem_commutant_iff.mp a.property) _ hJM

def isometricCornerAlgebra : VonNeumannAlgebra E :=
  starSubalgebraCommutant (rangeCompressionStarHom J M.commutant.toStarSubalgebra
    (rangeProjection_commutes_commutant J M hJM)).range

theorem mem_isometricCornerAlgebra_iff (T : E →L[ℂ] E) :
    T ∈ isometricCornerAlgebra J M hJM ↔ isometricExtension J T ∈ M := by
  let σ := rangeCompressionStarHom J M.commutant.toStarSubalgebra
    (rangeProjection_commutes_commutant J M hJM)
  have hmem : T ∈ isometricCornerAlgebra J M hJM ↔ ∀ a : M.commutant.toStarSubalgebra,
      σ a * T = T * σ a := by
    change T ∈ starSubalgebraCommutant σ.range ↔ _
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    constructor
    · intro h a
      exact h (σ a) ⟨a, rfl⟩
    · intro h _ ha
      obtain ⟨a, rfl⟩ := ha
      exact h a
  rw [hmem]
  conv_rhs => rw [← M.commutant_commutant]
  constructor
  · intro h
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    let a' : M.commutant.toStarSubalgebra := ⟨a, ha⟩
    have hJ := rangeCompressionStarHom_intertwines J _
      (rangeProjection_commutes_commutant J M hJM) a'
    have hJs := rangeCompressionStarHom_intertwines J _
      (rangeProjection_commutes_commutant J M hJM) (star a')
    rw [map_star] at hJs
    exact (isometricExtension_commutes J (σ a') a hJ hJs T (h a').symm).symm
  · intro h a
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp h a.val a.property
    exact (compression_commutes_of_isometricExtension_commutes J T a.val hc.symm).symm

end

end KadisonKastler

end OAI
