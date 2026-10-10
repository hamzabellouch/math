import OAI.Analysis.KadisonSimilarity.Tracial.MatrixArrayFlattening
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-!
Finite amplification is reduced to centered symmetry tests on square Hilbert
arrays. The operator replacement and its symmetry bound remain explicit local
hypotheses; the padding, dilation, coordinate change, and perturbation losses
are all proved here.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual diagonal amplification of a star representation. -/
def amplifiedScalarRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    A →⋆ₐ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun a := amplify (σ a) n
  map_zero' := by ext x i; simp [amplify_apply]
  map_one' := by ext x i; simp [amplify_apply]
  map_add' a b := by ext x i; simp [amplify_apply]
  map_mul' a b := by ext x i; simp [amplify_apply, mul_apply_eq_comp]
  commutes' c := by
    ext x i
    simp [amplify_apply, Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    change amplify (σ (star a)) n = (amplify (σ a) n).adjoint
    rw [adjoint_amplify, map_star, ContinuousLinearMap.star_eq_adjoint]

@[simp] theorem amplifiedScalarRepresentation_apply
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) (a : A) :
    amplifiedScalarRepresentation σ n a = amplify (σ a) n := rfl

/-- Matrix padding and multiplicity padding preserve the actual represented
commutator, with independent injections on the two indices. -/
theorem norm_represented_commutator_pad_both {r m s t : ℕ}
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : Fin r ↪ Fin m) (f : Fin s ↪ Fin t)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : CStarMatrix (Fin s) (Fin s) A) :
    ‖commutator (amplify (padArrayOperator e Y) t)
      (representedMatrix (amplifiedScalarRepresentation σ m) (cstarMatrixPadding f X))‖ =
    ‖commutator (amplify Y s) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ := by
  change ‖commutator (amplify (padArrayOperator e Y) t)
    (matrixOperator (fun i j => amplifiedScalarRepresentation σ m (cstarMatrixPadding f X i j)))‖ = _
  rw [representedPadding_entries]
  exact norm_commutator_pad_both e f Y (fun i j => σ (X i j))

variable [PartialOrder A] [StarOrderedRing A]

/-- The represented flattened symmetry is contractive even for a degenerate
representation, since it is the image of an actual unitary. -/
theorem norm_represented_flattened_symmetry_le {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX))‖ ≤ 1 := by
  let φ := (representedMatrixHom σ (4 * n)).comp
    (fourfoldMatrixFlatten (A := A) n).toStarAlgHom
  let u := Unitary.map (StarMonoidHom.ofClass φ) (contractionSymmetryUnitary X hX)
  change ‖(u : HilbertCopies H (4 * n) →L[ℂ] HilbertCopies H (4 * n))‖ ≤ 1
  exact (Unitary.linearIsometryEquiv u).toLinearIsometry.norm_toContinuousLinearMap_le

/-- Restoring the original operator after a norm-small replacement loses at
most twice that distance on the flattened unitary test. -/
theorem flattened_symmetry_bound_of_approximation {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies H (4 * n) →L[ℂ] HilbertCopies H (4 * n))
    {η B : ℝ} (hclose : ‖Y₀ - amplify Y (4 * n)‖ ≤ η)
    (hbound : ‖commutator Y₀
      (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ ≤ B) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ B + 2 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have hnorm := norm_represented_flattened_symmetry_le σ X hX
  have hc : ‖amplify Y (4 * n) - Y₀‖ ≤ η := by
    rwa [norm_sub_rev]
  calc
    _ ≤ ‖commutator (amplify Y (4 * n))
      (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ :=
        norm_amplified_commutator_le_flattened_symmetry σ Y X hX
    _ ≤ B + 2 * η *
      ‖representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX))‖ :=
        norm_commutator_le_of_approx _ _ _ hbound hc
    _ ≤ B + 2 * η := by nlinarith

/-- A test of arbitrary matrix size and multiplicity is controlled by one
centered symmetry test in a square array. The symmetry bound is an explicit
hypothesis, rather than an assumed conclusion about all matrix tests. -/
theorem finite_amplification_bound_of_one_symmetry {r h n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin (4 * n)) (f : Fin h ↪ Fin n)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies (HilbertCopies H (4 * n)) (4 * n) →L[ℂ]
      HilbertCopies (HilbertCopies H (4 * n)) (4 * n))
    {η B : ℝ}
    (hclose : ‖Y₀ - amplify (padArrayOperator e Y) (4 * n)‖ ≤ η)
    (hbound : ‖commutator Y₀
      (representedMatrix (amplifiedScalarRepresentation σ (4 * n))
        (fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
          (by simpa only [norm_cstarMatrixPadding] using hX))))‖ ≤ B) :
    ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤
      B + 2 * η := by
  rw [← norm_represented_commutator_pad_both σ e f Y X]
  exact flattened_symmetry_bound_of_approximation
    (amplifiedScalarRepresentation σ (4 * n)) (padArrayOperator e Y)
    (cstarMatrixPadding f X) (by simpa only [norm_cstarMatrixPadding] using hX)
    Y₀ hclose hbound

omit [CompleteSpace H] in
/-- Amplifying the replacement does not enlarge its norm distance. -/
theorem norm_amplify_sub_le (S T : H →L[ℂ] H) (n : ℕ) :
    ‖amplify S n - amplify T n‖ ≤ ‖S - T‖ := by
  have h : amplify S n - amplify T n = amplify (S - T) n := by
    ext x i
    simp only [sub_apply, PiLp.sub_apply, amplify_apply]
  rw [h]
  exact norm_amplify_le (S - T) n

/-- The manuscript's replacement lives on the multiplicity space; its
amplification supplies the square-array replacement without further loss. -/
theorem finite_amplification_bound_of_multiplicity_approximation
    {r h n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : Fin r ↪ Fin (4 * n)) (f : Fin h ↪ Fin n)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies H (4 * n) →L[ℂ] HilbertCopies H (4 * n))
    {η B : ℝ} (hclose : ‖Y₀ - padArrayOperator e Y‖ ≤ η)
    (hbound : ‖commutator (amplify Y₀ (4 * n))
      (representedMatrix (amplifiedScalarRepresentation σ (4 * n))
        (fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
          (by simpa only [norm_cstarMatrixPadding] using hX))))‖ ≤ B) :
    ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤
      B + 2 * η := by
  exact finite_amplification_bound_of_one_symmetry σ e f Y X hX (amplify Y₀ (4 * n))
    ((norm_amplify_sub_le Y₀ (padArrayOperator e Y) (4 * n)).trans hclose) hbound

/-- The symmetry appearing in the preceding reduction is selfadjoint,
squares to one, and is centered for the actual normalized matrix trace. -/
theorem padded_flattened_symmetry_properties {h n : ℕ} [NeZero n]
    (τ : A →ₚ[ℂ] ℂ) (f : Fin h ↪ Fin n)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1) :
    let S := fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
      (by simpa only [norm_cstarMatrixPadding] using hX))
    star S = S ∧ S * S = 1 ∧ normalizedMatrixTrace τ (4 * n) S = 0 := by
  dsimp only
  refine ⟨?_, ?_, normalizedMatrixTrace_flattened_contractionSymmetry n τ _ _⟩
  · rw [← map_star, contractionSymmetryUnitary_star]
  · rw [← map_mul, contractionSymmetryUnitary_sq, map_one]

/-- Uniform centered-square symmetry bounds, together with the actual norm
approximation, control every finite matrix amplification. This theorem is a
reduction: its symmetry bound must be proved separately in the application. -/
theorem finite_amplification_bound_of_centered_tests {r : ℕ}
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies H r →L[ℂ] HilbertCopies H r) {η B : ℝ}
    (hconstant : 0 ≤ B + 2 * η)
    (hreplace : ∀ (n : ℕ) [NeZero n], ∀ e : Fin r ↪ Fin (4 * n),
      ∃ Y₀ : HilbertCopies (HilbertCopies H (4 * n)) (4 * n) →L[ℂ]
          HilbertCopies (HilbertCopies H (4 * n)) (4 * n),
        ‖Y₀ - amplify (padArrayOperator e Y) (4 * n)‖ ≤ η ∧
        ∀ S : CStarMatrix (Fin (4 * n)) (Fin (4 * n)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * n) S = 0 →
          ‖commutator Y₀ (representedMatrix (amplifiedScalarRepresentation σ (4 * n)) S)‖ ≤ B)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) X)‖ ≤
      (B + 2 * η) * ‖X‖ := by
  by_cases hh : h = 0
  · subst h
    have hz : commutator (amplify Y 0)
        (representedMatrix (amplifiedScalarRepresentation σ r) X) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact mul_nonneg hconstant (norm_nonneg X)
  have : NeZero h := ⟨hh⟩
  have hunit (Z : CStarMatrix (Fin h) (Fin h) A) (hZ : ‖Z‖ ≤ 1) :
      ‖commutator (amplify Y h) (representedMatrix (amplifiedScalarRepresentation σ r) Z)‖ ≤
        B + 2 * η := by
    let n := max r h + 1
    have hn : 0 < n := by dsimp [n]; omega
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let e : Fin r ↪ Fin (4 * n) := Fin.castLEEmb (by dsimp [n]; omega)
    let f : Fin h ↪ Fin n := Fin.castLEEmb (by dsimp [n]; omega)
    obtain ⟨Y₀, hclose, htest⟩ := hreplace n e
    apply finite_amplification_bound_of_one_symmetry σ e f Y Z hZ Y₀ hclose
    let hnorm : ‖cstarMatrixPadding f Z‖ ≤ 1 := by
      simpa only [norm_cstarMatrixPadding] using hZ
    obtain ⟨hstar, hsquare, htrace⟩ := padded_flattened_symmetry_properties τ f Z hZ
    exact htest (fourfoldMatrixFlatten n (contractionSymmetryUnitary _ hnorm))
      hstar hsquare htrace
  let ρ := representedMatrixHom (amplifiedScalarRepresentation σ r) h
  let δ := cornerCommutator ρ ρ (amplify Y h)
  have hδ : ‖δ‖ ≤ B + 2 * η := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hconstant
    intro Z hZ
    exact hunit Z hZ.le
  exact (δ.le_opNorm X).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg X))

end KadisonSimilarity

end

end OAI
