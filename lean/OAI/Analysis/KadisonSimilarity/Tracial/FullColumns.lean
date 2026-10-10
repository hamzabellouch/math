import OAI.Analysis.KadisonSimilarity.Derivation.RectangularDerivations

namespace OAI

/-!
# Extending a corner intertwiner through finitely many matrix units

These are the matrix-coordinate steps of `lem:full-column`: coordinatewise
amplification preserves the error norm and intertwines a full operator matrix
as soon as it intertwines each entry. The geometric construction of the
corner and its matrix-unit coordinates is still required.
-/

noncomputable section

namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Positive finite amplification of a rectangular operator preserves its norm. -/
theorem norm_mapCopies (T : K →L[ℂ] F) {n : ℕ} (hn : 0 < n) :
    ‖mapCopies T n‖ = ‖T‖ := by
  apply le_antisymm (norm_mapCopies_le T n)
  apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (mapCopies T n))
  intro x
  let i : Fin n := ⟨0, hn⟩
  have hmap : mapCopies T n (PiLp.single 2 i x) = PiLp.single 2 i (T x) := by
    ext j
    by_cases h : j = i
    · subst j
      simp only [mapCopies_apply, PiLp.single_eq_same]
    · simp only [mapCopies_apply, PiLp.single_apply, ite_eq_right h, map_zero]
  have h := (mapCopies T n).le_opNorm (PiLp.single 2 i x)
  simpa only [hmap, PiLp.norm_single] using h

@[simp] theorem mapCopies_sub (S T : K →L[ℂ] F) (n : ℕ) :
    mapCopies (S - T) n = mapCopies S n - mapCopies T n := by
  ext x i
  simp only [mapCopies_apply, sub_apply, PiLp.sub_apply]

/-- In the matrix-unit coordinates the error bound has no dimension factor. -/
theorem norm_mapCopies_sub (S T : K →L[ℂ] F) {n : ℕ} (hn : 0 < n) :
    ‖mapCopies S n - mapCopies T n‖ = ‖S - T‖ := by
  rw [← mapCopies_sub, norm_mapCopies _ hn]

/-- Entrywise intertwining suffices for intertwining the full matrix algebra. -/
theorem mapCopies_intertwines_matrix (T : K →L[ℂ] F) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] K))
    (Y : Matrix (Fin n) (Fin n) (F →L[ℂ] F))
    (hXY : ∀ i j, T.comp (X i j) = (Y i j).comp T) :
    (mapCopies T n).comp (matrixOperator X) =
      (matrixOperator Y).comp (mapCopies T n) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, mapCopies_apply, matrixOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun L : K →L[ℂ] F => L (x j)) (hXY i j)

/-- Changing isometric domain coordinates preserves the operator norm. -/
theorem norm_comp_isometricCoordinates (T : K →L[ℂ] F) (U : E ≃ₗᵢ[ℂ] K) :
    ‖T.comp U.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    change ‖T (U x)‖ ≤ ‖T‖ * ‖x‖
    simpa only [LinearIsometryEquiv.norm_map] using T.le_opNorm (U x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (T.comp U.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (U.symm x)
    simpa using h

/-- Isometric codomain coordinates also preserve the operator norm. -/
theorem norm_isometricCoordinates_comp (T : K →L[ℂ] F) (V : F ≃ₗᵢ[ℂ] E) :
    ‖V.toContinuousLinearEquiv.toContinuousLinearMap.comp T‖ = ‖T‖ := by
  exact V.toLinearIsometry.norm_toContinuousLinearMap_comp

end KadisonSimilarity

end

end OAI
