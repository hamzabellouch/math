import OAI.Analysis.KadisonKastler.SpectralClipping
import OAI.Analysis.KadisonKastler.ClippedDrift

namespace OAI

/-!
# Spectrally clipped coefficient columns

The actual cutoff preserves the coefficient-column bound, right support,
and the relevant quotient image. The final theorem substitutes that
cutoff directly into the coefficient drift estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

universe u

section Abstract

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ω : Type*} [Fintype ω]

theorem sum_spectralClip_star_mul_le (K : ω → A) (β : ω → ℝ) (hβ : ∀ w, 0 < β w) :
    (∑ w, star (spectralClip (β w) (K w)) * spectralClip (β w) (K w)) ≤
      ∑ w, star (K w) * K w :=
  Finset.sum_le_sum (fun w _ => spectralClip_star_mul_self_le (hβ w) (K w))

theorem sum_discarded_star_mul_le (K : ω → A) (β : ω → ℝ) (hβ : ∀ w, 0 < β w) :
    (∑ w, star (K w - spectralClip (β w) (K w)) * (K w - spectralClip (β w) (K w))) ≤
      ∑ w, star (K w) * K w :=
  Finset.sum_le_sum (fun w _ => spectralClip_discard_star_mul_self_le (hβ w) (K w))

theorem spectralClip_star_column_le_one (K : ω → A) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (hK : (∑ w, star (K w) * K w) ≤ 1) :
    (∑ w, star (spectralClip (β w) (K w)) * spectralClip (β w) (K w)) ≤ 1 :=
  (sum_spectralClip_star_mul_le K β hβ).trans hK

theorem discarded_star_column_le_one (K : ω → A) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (hK : (∑ w, star (K w) * K w) ≤ 1) :
    (∑ w, star (K w - spectralClip (β w) (K w)) * (K w - spectralClip (β w) (K w))) ≤ 1 :=
  (sum_discarded_star_mul_le K β hβ).trans hK

end Abstract

section MatrixMap

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise application of a unital star homomorphism to square matrices. -/
def coefficientMatrixMap (π : A →⋆ₐ[ℂ] B) :
    CStarMatrix n n A →⋆ₐ[ℂ] CStarMatrix n n B where
  toFun := CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom
  map_one' := by
    apply CStarMatrix.ext
    intro i j
    simp [CStarMatrix.mapₙₐ, CStarMatrix.one_apply]
  map_mul' := map_mul (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  map_zero' := map_zero (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  map_add' := map_add (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)
  commutes' z := by
    apply CStarMatrix.ext
    intro i j
    change π (if i = j then algebraMap ℂ A z else 0) =
      if i = j then algebraMap ℂ B z else 0
    by_cases hij : i = j
    · simpa only [hij, ite_true] using AlgHomClass.commutes π z
    · simp [hij]
  map_star' := map_star (CStarMatrix.mapₙₐ π.toNonUnitalStarAlgHom)

@[simp]
theorem coefficientMatrixMap_apply (π : A →⋆ₐ[ℂ] B) (K : CStarMatrix n n A) (i j : n) :
    coefficientMatrixMap π K i j = π (K i j) := rfl

end MatrixMap

section Operators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance clippedCoefficientOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance clippedCoefficientOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Operator star-square domination is pointwise domination of norms. -/
theorem norm_apply_le_of_star_mul_self_le (X Y : H →L[ℂ] H)
    (hXY : star X * X ≤ star Y * Y) (z : H) : ‖X z‖ ≤ ‖Y z‖ := by
  let D := CFC.sqrt (star Y * Y - star X * X)
  have hD : star D * D = star Y * Y - star X * X := by
    rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hXY)]
  have hsum : star Y * Y = star X * X + star D * D := by rw [hD]; abel
  have hnorm (T : H →L[ℂ] H) :
      (inner ℂ ((star T * T) z) z).re = ‖T z‖ ^ 2 := by
    exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T z).symm
  have h := congrArg (fun T : H →L[ℂ] H => (inner ℂ (T z) z).re) hsum
  simp only [_root_.add_apply, inner_add_left, Complex.add_re, hnorm] at h
  nlinarith [sq_nonneg ‖D z‖, norm_nonneg (X z), norm_nonneg (Y z)]

/-- A pointwise star-square bound preserves any vector-column bound. -/
theorem column_contract_of_star_mul_self_le {ω : Type*} [Fintype ω]
    (K L : ω → H →L[ℂ] H) (hLK : ∀ w, star (L w) * L w ≤ star (K w) * K w)
    (hK : ∀ z : H, ‖WithLp.toLp 2 (fun w => K w z)‖ ≤ ‖z‖) (z : H) :
    ‖WithLp.toLp 2 (fun w => L w z)‖ ≤ ‖z‖ := by
  apply le_trans _ (hK z)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro w _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_star_mul_self_le _ _ (hLK w) z) 2

variable {n : ℕ}

theorem coefficient_hilbertMatrixHom_apply
    (K : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    (hilbertMatrixHom (H := H) (n := Fin n)) K = hilbertMatrix K := rfl

local instance clippedCoefficientMatrixOrder :
    PartialOrder (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) := CStarAlgebra.spectralOrder _
local instance clippedCoefficientMatrixStarOrder :
    StarOrderedRing (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) := CStarAlgebra.spectralOrderedRing _

def clippedCoefficients {ω : Type*}
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ) (w : ω) :=
  spectralClip (β w) (K w)

theorem clippedCoefficients_norm {ω : Type*}
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (w : ω) : ‖clippedCoefficients K β w‖ ≤ β w :=
  spectralClip_norm_le (hβ w) (K w)

theorem clippedCoefficients_support {ω : Type*}
    (K P : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (hKP : ∀ w, K w = K w * P w) (w : ω) :
    clippedCoefficients K β w = clippedCoefficients K β w * P w :=
  (spectralClip_mul_right_eq (hβ w) (K w) (P w) (hKP w).symm).symm

theorem clippedCoefficients_column_contract {ω : Type*} [Fintype ω]
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w)
    (hK : ∀ z : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w) z)‖ ≤ ‖z‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun w => hilbertMatrix (clippedCoefficients K β w) z)‖ ≤ ‖z‖ := by
  apply column_contract_of_star_mul_self_le (fun w => hilbertMatrix (K w)) _ _ hK
  intro w
  have h := OrderHomClass.mono (hilbertMatrixHom (H := H) (n := Fin n))
    (spectralClip_star_mul_self_le (hβ w) (K w))
  simpa only [map_mul, map_star, coefficient_hilbertMatrixHom_apply, clippedCoefficients] using h

theorem discardedCoefficients_column_contract {ω : Type*} [Fintype ω]
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w)
    (hK : ∀ z : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w) z)‖ ≤ ‖z‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w - clippedCoefficients K β w) z)‖ ≤ ‖z‖ := by
  apply column_contract_of_star_mul_self_le (fun w => hilbertMatrix (K w)) _ _ hK
  intro w
  have h := OrderHomClass.mono (hilbertMatrixHom (H := H) (n := Fin n))
    (spectralClip_discard_star_mul_self_le (hβ w) (K w))
  simpa only [map_mul, map_star, coefficient_hilbertMatrixHom_apply, clippedCoefficients] using h

local instance clippedCoefficientEntryOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance clippedCoefficientEntryStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

local instance clippedCoefficientAlgebraOrder (M : VonNeumannAlgebra H) :
    PartialOrder (CStarMatrix (Fin n) (Fin n) (Algebra M)) := CStarAlgebra.spectralOrder _
local instance clippedCoefficientAlgebraStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (CStarMatrix (Fin n) (Fin n) (Algebra M)) := CStarAlgebra.spectralOrderedRing _

/-- Applying the spectral cutoff preserves entrywise membership in the
original von Neumann algebra. -/
theorem spectralClip_entry_mem (M : VonNeumannAlgebra H)
    (K : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (hK : ∀ i j, K i j ∈ M)
    {β : ℝ} (hβ : 0 < β) (i j : Fin n) : spectralClip β K i j ∈ M := by
  let K₀ : CStarMatrix (Fin n) (Fin n) (Algebra M) :=
    CStarMatrix.ofMatrix (fun i j => ⟨K i j, hK i j⟩)
  let π := coefficientMatrixMap (n := Fin n) M.toStarSubalgebra.subtype
  have hπ : π K₀ = K := by apply CStarMatrix.ext; intro i j; rfl
  have heq := map_spectralClip π hβ K₀
  rw [hπ] at heq
  rw [← heq]
  exact (spectralClip β K₀ i j).property

theorem clippedCoefficients_entry_mem {ω : Type*} (M : VonNeumannAlgebra H)
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (hK : ∀ w i j, K w i j ∈ M) (w : ω) (i j : Fin n) :
    clippedCoefficients K β w i j ∈ M :=
  spectralClip_entry_mem M (K w) (hK w) (hβ w) i j

theorem clippedCoefficients_quotient_error {ω : Type*}
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ] B)
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (β : ω → ℝ)
    (hβ : ∀ w, 0 < β w) (hπ : ∀ w, ‖π (K w)‖ ≤ β w) (w : ω) :
    π (K w - clippedCoefficients K β w) = 0 :=
  map_sub_spectralClip_eq_zero π (hβ w) (K w) (hπ w)

/-- The drift theorem applied to the actual spectral cutoff of the original
coefficient family, with its column and support bounds proved above. -/
theorem spectralClipped_matrixCommutator_drift_le_sixty_six {ω : Type*} [Fintype ω]
    {q : ℕ} (M : VonNeumannAlgebra H)
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (E : Generator.MatrixUnitSystem (Fin q) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (S : ω → Finset (Fin n × Fin q)) (hS : ∀ w, (S w).card ≤ q)
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hKmem : ∀ w i j, K w i j ∈ M)
    (hKsupport : ∀ w, K w = K w * supportProjection E (S w))
    (β : ω → ℝ) (hβpos : ∀ w, 0 < β w)
    (hKcontract : ∀ z : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w) z)‖ ≤ ‖z‖)
    (hβ : ∀ a : Fin n × Fin q, (∑ w : ω, if a ∈ S w then β w ^ 2 else 0) ≤ 64)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun w =>
      hilbertMatrix (matrixCommutator h (clippedCoefficients K β w)) z)‖ ≤
      66 * δ * ‖z‖ := by
  exact clipped_matrixCommutator_drift_le_sixty_six M hPublished E hE S hS
    (clippedCoefficients K β) (clippedCoefficients_entry_mem M K β hβpos hKmem)
    (clippedCoefficients_support K (fun w => supportProjection E (S w)) β hβpos hKsupport)
    β (clippedCoefficients_norm K β hβpos)
    (clippedCoefficients_column_contract K β hβpos hKcontract) hβ h hδ hb z

end Operators

end

end KadisonKastler

end OAI
