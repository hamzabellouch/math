import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixColumns

namespace OAI

/-! The full-column estimate in the concrete tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

section Coordinates
variable {P C H D F K : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace F] [CompleteSpace K] in
private theorem mapCopies_single (T : K →L[ℂ] F) {n : ℕ} (i : Fin n) (x : K) :
    mapCopies T n (PiLp.single 2 i x) = PiLp.single 2 i (T x) := by
  ext j
  simp only [mapCopies_apply, PiLp.single_apply]
  split_ifs <;> simp

/-- Diagonal extension agrees with the given corner map on every column. -/
theorem extend_column
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (Lr : P →⋆ₐ[ℂ] (D →L[ℂ] D))
    (ρ : C →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (U : FiniteOrthogonalColumns F H n) (V : FiniteOrthogonalColumns K D n)
    (entry : P → Matrix (Fin n) (Fin n) C)
    (hU : ∀ a i j, ρ (entry a i j) =
      (U.inclusion i).adjoint.comp ((L a).comp (U.inclusion j)))
    (hV : ∀ a i j, σ (entry a i j) =
      (V.inclusion i).adjoint.comp ((Lr a).comp (V.inclusion j)))
    (T : K →L[ℂ] F) (i : Fin n) (x : K) :
    (fullColumnCoordinatesOfColumns L Lr ρ σ U V entry hU hV).extend T
      (V.inclusion i x) = U.inclusion i (T x) := by
  change U.unitary (mapCopies T n (V.unitary.symm (V.inclusion i x))) = _
  rw [← V.unitary_single, V.unitary.symm_apply_apply, mapCopies_single,
    U.unitary_single]

omit [CompleteSpace H] in
/-- Equality on a complete finite family of columns determines an operator. -/
theorem FiniteOrthogonalColumns.ext_on_columns {n : ℕ}
    (V : FiniteOrthogonalColumns K D n) (S T : D →L[ℂ] H)
    (h : ∀ i x, S (V.inclusion i x) = T (V.inclusion i x)) : S = T := by
  ext x
  obtain ⟨z, rfl⟩ := V.unitary.surjective x
  simp only [FiniteOrthogonalColumns.unitary_apply, sumColumns_apply, map_sum, h]

end Coordinates

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

include he in
/-- Commutation with the left corner projection makes output compression exact. -/
theorem inclusion_cornerRestriction (Y : H →L[ℂ] H)
    (hYe : Y.comp (G.left e) = (G.left e).comp Y) (x : G.corner e r) :
    ((G.cornerRestriction e r Y x : G.corner e 1) : H) = Y (x : H) := by
  change ((G.corner e 1).toSubmodule.subtypeL.comp
    (G.corner e 1).toSubmodule.subtypeL.adjoint) (Y (x : H)) = _
  rw [G.corner_inclusion_adjoint e 1 he (IsStarProjection.one P),
    cornerProjection, G.right_one, ContinuousLinearMap.comp_id]
  have h := congrArg (fun T : H →L[ℂ] H => T (x : H)) hYe
  simpa only [ContinuousLinearMap.comp_apply, ((G.mem_corner e r x).mp x.property).1]
    using h.symm

/-- Matrix commutation extends the actual compressed operator to the full column. -/
theorem extend_cornerRestriction (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (Y : H →L[ℂ] H) (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYv : ∀ i, Y.comp (G.left (v i)) = (G.left (v i)).comp Y) :
    (G.fullColumnCoordinates e he r hr v hv hsum).extend
      (G.cornerRestriction e r Y) = Y.comp (G.corner 1 r).toSubmodule.subtypeL := by
  apply (G.supportedCornerColumns e he r hr v hv hsum).ext_on_columns
  intro i x
  have hc := extend_column G.left (G.rightColumnRepresentation r)
    (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
    (G.ambientCornerColumns e he v hv hsum)
    (G.supportedCornerColumns e he r hr v hv hsum)
    (cornerMatrixEntry e he v hv)
    (G.ambientCornerColumns_entry e he v hv hsum)
    (G.supportedCornerColumns_entry e he r hr v hv hsum)
    (G.cornerRestriction e r Y) i x
  refine hc.trans ?_
  change G.left (v i) ((G.cornerRestriction e r Y x : G.corner e 1) : H) =
    Y (G.left (v i) (x : H))
  rw [G.inclusion_cornerRestriction e he r Y hYe]
  exact (congrArg (fun T : H →L[ℂ] H => T (x : H)) (hYv i)).symm

/-- The paper's full-column conclusion, with all corner representations and
matrix coordinates constructed from the tracial geometry. Its only analytic
inputs are the explicitly cited cyclic results and tracial commutation. -/
theorem full_column
    (hfaithful : Function.Injective G.vector)
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    {n : ℕ} (hn : 0 < n) (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (Y : H →L[ℂ] H) (hYe : Y.comp (G.left e) = (G.left e).comp Y)
    (hYv : ∀ i, Y.comp (G.left (v i)) = (G.left (v i)).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful)) :
    ∃ b : P, r * b = b ∧
      ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤
        (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨T, hT, hnorm⟩ := G.exists_corrected_corner e he r τ comparison hr hτ
    Y hε hY published
  let c := G.fullColumnCoordinates e he r hr v hv hsum
  have hpr : (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp
      (G.corner 1 r).toSubmodule.subtypeL = ContinuousLinearMap.id ℂ (G.corner 1 r) := by
    have hI : (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp
        (G.corner 1 r).toSubmodule.subtypeL = 1 :=
      (G.corner 1 r).toSubmodule.subtypeₗᵢ.adjoint_comp_self
    change _ = 1
    exact hI
  obtain ⟨b, hb, hTb⟩ := exists_supported_right_multiplier G.left
    (G.rightColumnRepresentation r) (G.faithfulRightAction hfaithful) r
    (G.corner 1 r).toSubmodule.subtypeL (G.corner 1 r).toSubmodule.subtypeL.adjoint
    hpr (G.rightColumn_projection r hr) (G.rightColumn_adjoint_intertwines r)
    commutation (c.extend T) (c.extend_intertwines T hT)
  refine ⟨b, hb, ?_⟩
  change ‖(Y - (G.faithfulRightAction hfaithful).right b).comp _‖ ≤ _
  rw [ContinuousLinearMap.sub_comp, hTb,
    ← G.extend_cornerRestriction e he r hr v hv hsum Y hYe hYv]
  exact (c.norm_extend_sub hn _ _).le.trans hnorm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
