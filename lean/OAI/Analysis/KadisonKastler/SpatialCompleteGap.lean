import OAI.Analysis.KadisonKastler.SpatialMatrixAmplification

namespace OAI

/-! # Complete proximity of spatial products with matrix-generated factors

The finite-stage approximants retain all matrix levels.  Kaplansky
density and weak compactness extend the same bound to the spatial
products.  Only the original complete proximity hypothesis is used.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

local instance spatialCompleteOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialCompleteStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance spatialCompleteTargetOrder :
    PartialOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
local instance spatialCompleteTargetStarOrder :
    StarOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)

/-- A matrix over a finite spatial image has an exact matrix preimage,
with the same norm at the outer matrix level. -/
theorem exists_spatialMatrixAmplification_of_mem
    (M : VonNeumannAlgebra H) (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (T : CStarMatrix ι ι (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hT : ∀ i j, T i j ∈ spatialMatrixAlgebra M E) (hn : ‖T‖ ≤ 1) :
    ∃ X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)),
      (∀ i j a b, X i j a b ∈ M) ∧ ‖X‖ ≤ 1 ∧ spatialMatrixAmplification E X = T := by
  have hex : ∀ i j, ∃ Z : CStarMatrix κ κ (Algebra M),
      spatialMatrixAlgebraHom M E Z = T i j := by
    intro i j
    obtain ⟨Z, hZ⟩ := hT i j
    exact ⟨Z, hZ⟩
  choose Z hZ using hex
  let X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)) :=
    CStarMatrix.ofMatrix fun i j => coefficientMatrixMap M.toStarSubalgebra.subtype (Z i j)
  have he : spatialMatrixAmplification E X = T := by
    apply CStarMatrix.ext
    intro i j
    exact hZ i j
  refine ⟨X, (fun i j a b => (Z i j a b).property), ?_, he⟩
  rw [← norm_spatialMatrixAmplification E X, he]
  exact hn

variable {s : ℕ → ℕ} (E : ∀ n, MatrixUnitSystem (Fin (s n)) (K →L[ℂ] K))

omit [Nontrivial K] in
/-- The amplified increasing spatial images generate precisely the
matrix von Neumann algebra of the spatial product. -/
theorem generated_matrix_spatial_union
    (M : VonNeumannAlgebra H) (hK : PublishedKaplanskyDensity.{u})
    (hE : Monotone (fun n => (E n).algebra)) :
    generatedVonNeumannAlgebra
        (⨆ n, matrixOperatorAlgebra (ι := ι) (spatialMatrixAlgebra M (E n))) =
      matrixVonNeumann (ι := ι)
        (spatialProductAlgebra M (generatedVonNeumannAlgebra (⨆ n, (E n).algebra))) := by
  have hmono : Monotone (fun n => spatialMatrixAlgebra M (E n)) :=
    fun i j hij => spatialMatrixAlgebra_mono M (E i) (E j) (hE hij)
  rw [← matrixOperatorAlgebra_iSup _ hmono, generated_matrixOperatorAlgebra,
    generated_spatialMatrixAlgebra_eq_product M E hK hE]

private theorem amplified_spatial_test_approx
    {M N : VonNeumannAlgebra H} {γ : ℝ} (h : MatrixNearInclusion M N γ)
    (hs : ∀ n, 0 < s n) (hE : Monotone (fun n => (E n).algebra))
    (a : {a : ↥(⨆ n, matrixOperatorAlgebra (ι := ι) (spatialMatrixAlgebra M (E n))) //
      ‖a‖ ≤ 1}) :
    ∃ b ∈ unitBall (matrixVonNeumann (ι := ι) (spatialProductAlgebra N
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))),
      ‖(a.val : FiniteHilbert ι (SpatialHilbert H K) →L[ℂ]
        FiniteHilbert ι (SpatialHilbert H K)) - b‖ ≤ γ := by
  classical
  have hmono : Monotone (fun n =>
      matrixOperatorAlgebra (ι := ι) (spatialMatrixAlgebra M (E n))) :=
    fun i j hij => matrixOperatorAlgebra_mono
      (spatialMatrixAlgebra_mono M (E i) (E j) (hE hij))
  have hamem := a.val.property
  change (a.val : FiniteHilbert ι (SpatialHilbert H K) →L[ℂ]
      FiniteHilbert ι (SpatialHilbert H K)) ∈
    ((⨆ n, matrixOperatorAlgebra (ι := ι) (spatialMatrixAlgebra M (E n)) :
      StarSubalgebra ℂ _) : Set _) at hamem
  rw [StarSubalgebra.coe_iSup_of_directed hmono.directed_le] at hamem
  obtain ⟨n, han⟩ := Set.mem_iUnion.mp hamem
  let : NeZero (s n) := ⟨(hs n).ne'⟩
  let A : CStarMatrix ι ι (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    CStarMatrix.ofMatrix fun i j => operatorEntry (a.val : FiniteHilbert ι (SpatialHilbert H K) →L[ℂ]
      FiniteHilbert ι (SpatialHilbert H K)) i j
  have hA : ∀ i j, A i j ∈ spatialMatrixAlgebra M (E n) :=
    (mem_matrixOperatorAlgebra_iff _ _).mp han
  have hAn : ‖A‖ ≤ 1 := by
    rw [← norm_hilbertMatrix A, hilbertMatrix_operatorEntries]
    exact a.property
  obtain ⟨X, hX, hXn, hXA⟩ := exists_spatialMatrixAmplification_of_mem M (E n) A hA hAn
  obtain ⟨Y, hY, hYn, hXY⟩ := h.spatialMatrixAmplification_approx (E n) X hX hXn
  refine ⟨hilbertMatrix (spatialMatrixAmplification (E n) Y), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_matrixVonNeumann_iff_entries]
    intro i j
    rw [operatorEntry_hilbertMatrix, spatialMatrixAmplification_apply]
    apply spatialMatrixHom_mem N _ (E n) _ (Y i j) (hY i j)
    intro r t
    exact subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun n => (E n).algebra) n) ((E n).entry_mem r t))
  · rw [norm_hilbertMatrix, norm_spatialMatrixAmplification]
    exact hYn
  · have haeq : hilbertMatrix (spatialMatrixAmplification (E n) X) =
        (a.val : FiniteHilbert ι (SpatialHilbert H K) →L[ℂ]
          FiniteHilbert ι (SpatialHilbert H K)) := by
      rw [hXA]
      exact hilbertMatrix_operatorEntries _
    rw [← haeq]
    change ‖hilbertMatrixHom (H := SpatialHilbert H K) (n := ι)
        (spatialMatrixAmplification (E n) X) -
      hilbertMatrixHom (H := SpatialHilbert H K) (n := ι)
        (spatialMatrixAmplification (E n) Y)‖ ≤ γ
    rw [← map_sub]
    change ‖hilbertMatrix (spatialMatrixAmplification (E n) X -
      spatialMatrixAmplification (E n) Y)‖ ≤ γ
    rw [norm_hilbertMatrix]
    exact hXY

/-- Matrix unit-ball proximity is preserved by the spatial product with
the von Neumann algebra generated by increasing finite matrix stages. -/
theorem MatrixNearInclusion.spatialProduct
    (hK : PublishedKaplanskyDensity.{u})
    {M N : VonNeumannAlgebra H} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : MatrixNearInclusion M N γ)
    (hs : ∀ n, 0 < s n) (hE : Monotone (fun n => (E n).algebra)) :
    MatrixNearInclusion
      (spatialProductAlgebra M (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))
      (spatialProductAlgebra N (generatedVonNeumannAlgebra (⨆ n, (E n).algebra))) γ := by
  intro n X hX hn
  let S := ⨆ m, matrixOperatorAlgebra (ι := Fin n) (spatialMatrixAlgebra M (E m))
  have hdense : WeakUnitBallDense
      (fun a : {a : S // ‖a‖ ≤ 1} =>
        (a.val : FiniteHilbert (Fin n) (SpatialHilbert H K) →L[ℂ]
          FiniteHilbert (Fin n) (SpatialHilbert H K)))
      (matrixVonNeumann (ι := Fin n) (spatialProductAlgebra M
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))) := by
    rw [← generated_matrix_spatial_union (ι := Fin n) E M hK hE]
    exact hK.weakUnitBallDense S
  have hXm : hilbertMatrix X ∈ unitBall
      (matrixVonNeumann (ι := Fin n) (spatialProductAlgebra M
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))) := by
    refine ⟨?_, ?_⟩
    · rw [mem_matrixVonNeumann_iff_entries]
      intro i j
      simpa only [operatorEntry_hilbertMatrix] using hX i j
    · simpa only [norm_hilbertMatrix] using hn
  obtain ⟨b, hb, hdist⟩ := exists_unitBall_approx_of_weakly_dense_tests _ hdense hγ
    (amplified_spatial_test_approx (ι := Fin n) E h hs hE) (hilbertMatrix X) hXm
  let Y : CStarMatrix (Fin n) (Fin n)
      (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    CStarMatrix.ofMatrix fun i j => operatorEntry b i j
  have hY : hilbertMatrix Y = b := hilbertMatrix_operatorEntries b
  refine ⟨Y, ?_, ?_, ?_⟩
  · exact (mem_matrixVonNeumann_iff_entries _ b).mp hb.1
  · rw [← norm_hilbertMatrix Y, hY]
    exact hb.2
  · rw [← norm_hilbertMatrix (X - Y)]
    change ‖hilbertMatrixHom (H := SpatialHilbert H K) (n := Fin n) (X - Y)‖ ≤ γ
    rw [map_sub]
    change ‖hilbertMatrix X - hilbertMatrix Y‖ ≤ γ
    rwa [hY]

end

end KadisonKastler

end OAI
