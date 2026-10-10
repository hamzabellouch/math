import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryExtraction
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-! # The concrete von Neumann algebra of finite operator matrices

The commutant of the diagonally amplified commutant consists exactly of
operator matrices with entries in the original von Neumann algebra. This
constructs the normal matrix realization used by spectral rounding.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded coordinate blocks, packaged as an actual matrix. -/
def matrixOfOperator {n : ℕ} (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    Matrix (Fin n) (Fin n) (H →L[ℂ] H) :=
  Matrix.of (fun i j => matrixEntryCompression i j T)

omit [CompleteSpace H] in
@[simp] theorem matrixOfOperator_apply {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) (i j : Fin n) :
    matrixOfOperator T i j = matrixEntryCompression i j T := rfl

omit [CompleteSpace H] in
/-- Every finite operator array is recovered from its coordinate blocks. -/
theorem matrixOperator_entryCompressions {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    matrixOperator (matrixOfOperator T) = T := by
  have hdecompose (x : HilbertCopies H n) :
      (∑ j : Fin n, PiLp.single 2 j (x j)) = x := by
    ext i
    simp
  ext x i
  change (matrixOperator (matrixOfOperator T) x) i = (T x) i
  rw [matrixOperator_apply]
  change (∑ j : Fin n, T (PiLp.single 2 j (x j)) i) = T x i
  have ht := congrArg ((PiLp.proj 2 (fun _ : Fin n => H) i).comp T) (hdecompose x)
  simpa only [map_sum, ContinuousLinearMap.comp_apply, PiLp.proj_apply] using ht

omit [CompleteSpace H] in
/-- A diagonal operator acts on a coordinate inclusion by the original operator. -/
theorem amplify_single {n : ℕ} (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    amplify T n (PiLp.single 2 j x) = PiLp.single 2 j (T x) := by
  ext i
  by_cases hij : i = j
  · subst i
    simp only [amplify_apply, PiLp.single_eq_same]
  · simp only [amplify_apply, PiLp.single_apply, ite_eq_right hij, map_zero]

omit [CompleteSpace H] in
/-- Diagonal commutation is equivalent to commutation of every matrix entry. -/
theorem amplify_commutes_iff_entries {n : ℕ} (A : H →L[ℂ] H)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    amplify A n * T = T * amplify A n ↔
      ∀ i j, A * matrixEntryCompression i j T = matrixEntryCompression i j T * A := by
  constructor
  · intro h i j
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun S : HilbertCopies H n →L[ℂ] HilbertCopies H n =>
      S (PiLp.single 2 j x) i) h
    simpa only [mul_apply_eq_comp, amplify_apply, amplify_single,
      matrixEntryCompression_apply] using hi
  · intro h
    conv_lhs => rw [← matrixOperator_entryCompressions T]
    conv_rhs => rw [← matrixOperator_entryCompressions T]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change A ((matrixOperator (matrixOfOperator T) x) i) =
      (matrixOperator (matrixOfOperator T) (amplify A n x)) i
    simp only [matrixOperator_apply, matrixOfOperator_apply, map_sum, amplify_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun S : H →L[ℂ] H => S (x j)) (h i j)

/-- The diagonal copy of the commutant, viewed just as a set of operators. -/
def amplifiedCommutantSet (P : VonNeumannAlgebra H) (n : ℕ) :
    Set (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  (fun T => amplify T n) '' (P.commutant : Set (H →L[ℂ] H))

/-- Finite matrices over `P`, constructed as an actual double-commutant algebra. -/
def matrixVonNeumann (P : VonNeumannAlgebra H) (n : ℕ) :
    VonNeumannAlgebra (HilbertCopies H n) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (amplifiedCommutantSet P n)
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (Set.centralizer (amplifiedCommutantSet P n ∪ star (amplifiedCommutantSet P n)))) = _
    exact Set.centralizer_centralizer_centralizer _

/-- The extra star tests in the centralizer are redundant for this set. -/
theorem mem_matrixVonNeumann_iff_commutes (P : VonNeumannAlgebra H) {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    T ∈ matrixVonNeumann P n ↔ ∀ A ∈ P.commutant, amplify A n * T = T * amplify A n := by
  change T ∈ StarSubalgebra.centralizer ℂ (amplifiedCommutantSet P n) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h A hA
    exact (h (amplify A n) ⟨A, hA, rfl⟩).1
  · intro h B hB
    obtain ⟨A, hA, rfl⟩ := hB
    refine ⟨h A hA, ?_⟩
    simpa only [ContinuousLinearMap.star_eq_adjoint, adjoint_amplify] using h (star A) (star_mem hA)

/-- Membership is exactly entrywise membership in the original algebra. -/
theorem mem_matrixVonNeumann_iff_entries (P : VonNeumannAlgebra H) {n : ℕ}
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) :
    T ∈ matrixVonNeumann P n ↔ ∀ i j, matrixEntryCompression i j T ∈ P := by
  rw [mem_matrixVonNeumann_iff_commutes]
  simp only [amplify_commutes_iff_entries]
  constructor
  · intro h i j
    rw [← P.commutant_commutant]
    exact VonNeumannAlgebra.mem_commutant_iff.mpr (fun A hA => h A hA i j)
  · intro h A hA i j
    exact VonNeumannAlgebra.mem_commutant_iff.mp
      (show matrixEntryCompression i j T ∈ P.commutant.commutant by
        rw [P.commutant_commutant]
        exact h i j) A hA

/-- The usual matrix-operator action has exactly the same entrywise criterion. -/
theorem matrixOperator_mem_matrixVonNeumann_iff (P : VonNeumannAlgebra H) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator X ∈ matrixVonNeumann P n ↔ ∀ i j, X i j ∈ P := by
  rw [mem_matrixVonNeumann_iff_entries]
  simp only [matrixEntryCompression_matrixOperator]

section Represented
variable {A : Type*} [CStarAlgebra A]

/-- A faithful representation remains faithful on finite matrices. -/
theorem representedMatrixHom_injective (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : Function.Injective σ) (n : ℕ) : Function.Injective (representedMatrixHom σ n) := by
  intro X Y h
  ext i j
  apply hσ
  calc
    σ (X i j) = matrixEntryCompression i j (representedMatrixHom σ n X) :=
      (matrixEntryCompression_matrixOperator (fun k l => σ (X k l)) i j).symm
    _ = matrixEntryCompression i j (representedMatrixHom σ n Y) :=
      congrArg (matrixEntryCompression i j) h
    _ = σ (Y i j) :=
      matrixEntryCompression_matrixOperator (fun k l => σ (Y k l)) i j

/-- A normal represented range has its actual matrix von Neumann range. -/
theorem representedMatrixHom_range (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (P : VonNeumannAlgebra H) (hσ : σ.range = P.toStarSubalgebra) (n : ℕ) :
    (representedMatrixHom σ n).range = (matrixVonNeumann P n).toStarSubalgebra := by
  classical
  apply SetLike.ext
  intro T
  constructor
  · rintro ⟨X, rfl⟩
    apply (matrixOperator_mem_matrixVonNeumann_iff P (fun i j => σ (X i j))).mpr
    intro i j
    change σ (X i j) ∈ P.toStarSubalgebra
    rw [← hσ]
    exact ⟨X i j, rfl⟩
  · intro hT
    have he (i j : Fin n) : ∃ a : A, σ a = matrixEntryCompression i j T := by
      have hm := (mem_matrixVonNeumann_iff_entries P T).mp hT i j
      change matrixEntryCompression i j T ∈ P.toStarSubalgebra at hm
      rw [← hσ] at hm
      exact hm
    choose a ha using he
    let X : Matrix (Fin n) (Fin n) A := Matrix.of a
    refine ⟨CStarMatrix.ofMatrix X, ?_⟩
    change matrixOperator (fun i j => σ (X i j)) = T
    have hX : (fun i j => σ (X i j)) = (fun i j => matrixEntryCompression i j T) := by
      funext i j
      exact ha i j
    rw [hX]
    exact matrixOperator_entryCompressions T

/-- Scalar matrix units act as the coordinate matrix units. -/
theorem representedMatrixHom_single_one (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {n : ℕ} (i j : Fin n) :
    representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.single i j (1 : A))) =
      copyMatrixUnit i j := by
  ext x k
  change (matrixOperator (Matrix.of (fun k l => σ ((CStarMatrix.ofMatrix
    (Matrix.single i j (1 : A))) k l))) x) k = (PiLp.single 2 i (x j) : HilbertCopies H n) k
  rw [matrixOperator_apply]
  by_cases hki : k = i
  · subst k
    rw [Finset.sum_eq_single j]
    · simp [Matrix.single_apply]
    · intro l _ hlj
      simp [Matrix.single_apply, Ne.symm hlj]
    · simp
  · simp [Matrix.single_apply, hki, Ne.symm hki, apply_ite]

/-- Constant diagonal matrices represent the diagonal amplification. -/
theorem representedMatrixHom_diagonal (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (n : ℕ) (a : A) :
    representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => a))) =
      amplify (σ a) n := by
  ext x i
  change (matrixOperator (Matrix.of (fun k l => σ ((CStarMatrix.ofMatrix
    (Matrix.diagonal (fun _ : Fin n => a))) k l))) x) i = (σ a) (x i)
  rw [matrixOperator_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal_apply, Ne.symm hji]
  · simp

/-- A matrix commutant element has one repeated diagonal block, which
commutes with the original represented algebra. -/
theorem matrixRange_commutant_is_diagonal
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} [NeZero n]
    (T : HilbertCopies H n →L[ℂ] HilbertCopies H n)
    (hT : T ∈ Set.centralizer ((representedMatrixHom σ n).range :
      Set (HilbertCopies H n →L[ℂ] HilbertCopies H n))) :
    ∃ B : H →L[ℂ] H, T = amplify B n ∧
      B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
  let i : Fin n := 0
  let B := copyCorner i T
  have hTi (j : Fin n) : T.comp (copyMatrixUnit i j) = (copyMatrixUnit i j).comp T := by
    have h := hT
      (representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.single i j (1 : A))))
      ⟨_, rfl⟩
    rw [representedMatrixHom_single_one] at h
    exact h.symm
  have hdiag : T = amplify B n := eq_mapCopies_of_matrixUnit_intertwining i T hTi
  refine ⟨B, hdiag, ?_⟩
  rintro C ⟨a, rfl⟩
  have h := hT
    (representedMatrixHom σ n (CStarMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => a))))
    ⟨_, rfl⟩
  rw [representedMatrixHom_diagonal] at h
  exact (amplify_commutes_iff_entries (σ a) T).mp h i i

/-- Every amplified scalar commutant element commutes with the represented
matrix algebra. -/
theorem amplify_mem_matrixRange_commutant
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) (B : H →L[ℂ] H)
    (hB : B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H))) :
    amplify B n ∈ Set.centralizer ((representedMatrixHom σ n).range :
      Set (HilbertCopies H n →L[ℂ] HilbertCopies H n)) := by
  rintro T ⟨X, rfl⟩
  apply Eq.symm
  apply (amplify_commutes_iff_entries B (representedMatrixHom σ n X)).mpr
  intro i j
  have he : matrixEntryCompression i j (representedMatrixHom σ n X) = σ (X i j) :=
    matrixEntryCompression_matrixOperator (Matrix.of (fun k l => σ (X k l))) i j
  rw [he]
  exact (hB (σ (X i j)) ⟨_, rfl⟩).symm

/-- Taking the scalar bicommutant does not change its commutant. -/
theorem mem_representation_commutant_iff (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : H →L[ℂ] H) :
    B ∈ (representationVonNeumannAlgebra σ).commutant ↔
      B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
  change B ∈ (starSubalgebraCommutant σ.range).commutant.commutant ↔ _
  rw [VonNeumannAlgebra.commutant_commutant]
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]

variable [PartialOrder A] [StarOrderedRing A]

/-- Finite matrices commute with passage to the represented bicommutant.
This supplies the actual matrix membership needed by Kaplansky density. -/
theorem representationVonNeumannAlgebra_matrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (n : ℕ) [NeZero n] :
    representationVonNeumannAlgebra (representedMatrixHom σ n) =
      matrixVonNeumann (representationVonNeumannAlgebra σ) n := by
  apply VonNeumannAlgebra.ext
  intro T
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
  constructor
  · intro hT
    apply (mem_matrixVonNeumann_iff_commutes _ T).mpr
    intro B hB
    exact hT (amplify B n) (amplify_mem_matrixRange_commutant σ n B
      ((mem_representation_commutant_iff σ B).mp hB))
  · intro hT S hS
    obtain ⟨B, rfl, hB⟩ := matrixRange_commutant_is_diagonal σ S hS
    exact (mem_matrixVonNeumann_iff_commutes _ T).mp hT B
      ((mem_representation_commutant_iff σ B).mpr hB)

/-- Entrywise bicommutant membership for an arbitrary represented algebra. -/
theorem matrixOperator_mem_representationVonNeumannAlgebra_iff
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator X ∈ representationVonNeumannAlgebra (representedMatrixHom σ n) ↔
      ∀ i j, X i j ∈ representationVonNeumannAlgebra σ := by
  rw [representationVonNeumannAlgebra_matrix, matrixOperator_mem_matrixVonNeumann_iff]


end Represented

section Concrete
variable (P : VonNeumannAlgebra H)
local instance matrixRange_closed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem subtype_range_eq : P.toStarSubalgebra.subtype.range = P.toStarSubalgebra := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The usual C-star matrix algebra over `P` is star-isomorphic to its
constructed concrete von Neumann realization. -/
def matrixVonNeumannEquiv (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra ≃⋆ₐ[ℂ]
      (matrixVonNeumann P n).toStarSubalgebra := by
  let f := representedMatrixHom P.toStarSubalgebra.subtype n
  have hrange : f.range = (matrixVonNeumann P n).toStarSubalgebra :=
    representedMatrixHom_range P.toStarSubalgebra.subtype P (subtype_range_eq P) n
  let g := f.codRestrict (matrixVonNeumann P n).toStarSubalgebra (fun X => by
    rw [← hrange]
    exact ⟨X, rfl⟩)
  let : Module ℂ (matrixVonNeumann P n).toStarSubalgebra :=
    SMulMemClass.toModule (matrixVonNeumann P n).toStarSubalgebra
  refine StarAlgEquiv.ofBijective (R := ℂ)
    (A := CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra)
    (B := (matrixVonNeumann P n).toStarSubalgebra) g ?_
  constructor
  · exact (StarAlgHom.injective_codRestrict _ _ _).mpr
      (representedMatrixHom_injective P.toStarSubalgebra.subtype Subtype.val_injective n)
  · intro T
    have hT : (T : HilbertCopies H n →L[ℂ] HilbertCopies H n) ∈ f.range := by
      rw [hrange]
      exact T.property
    obtain ⟨X, hX⟩ := hT
    exact ⟨X, Subtype.ext hX⟩

end Concrete
end KadisonSimilarity

end

end OAI
