import OAI.Analysis.KadisonKastler.RowEnergy

namespace OAI

/-! Complete norm control of the finite row energies. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance rowEnergyBoundsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowEnergyBoundsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowEnergyBoundsOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rowEnergyBoundsOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem algebraRow_norm_le_one {M : VonNeumannAlgebra H}
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) : ‖algebraRow r‖ ≤ 1 := by
  have hprod : algebraRow r * (algebraRow r).conjTranspose =
      (1 : CStarMatrix (Fin 1) (Fin 1) (Algebra M)) := by
    ext1 i j
    fin_cases i
    fin_cases j
    simpa only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply,
      algebraRow_apply, CStarMatrix.one_apply, ite_eq_left] using hr
  apply (rectangular_row_and_column_contract (algebraRow r) ?_).1
  rw [hprod]
  have h := CStarRing.norm_star_mul_self
    (x := (1 : CStarMatrix (Fin 1) (Fin 1) (Algebra M)))
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : CStarMatrix (Fin 1) (Fin 1) (Algebra M))]

theorem rowAdjointVector_map_bound {M : VonNeumannAlgebra H}
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ}
    (hc : 0 ≤ c) (hF : CompletelyBoundedBy F c) (ξ : H) :
    ‖rowAdjointVector (fun i => F (r i)) ξ‖ ≤ c * ‖ξ‖ := by
  let e := M.toStarSubalgebra.subtype
  let Y := CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ F (algebraRow r))
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  have hY : ‖Y‖ ≤ c := by
    change ‖CStarMatrix.mapₗ e.toAlgHom.toLinearMap
      (CStarMatrix.mapₗ F (algebraRow r))‖ ≤ c
    rw [he 1 n]
    exact (hF.finite _).trans ((mul_le_mul_of_nonneg_left
      (algebraRow_norm_le_one r hr) hc).trans_eq (mul_one c))
  have hv : rectangularHilbertMatrix Y.conjTranspose (tupleSingle 0 ξ) =
      rowAdjointVector (fun i => F (r i)) ξ := by
    ext i
    simp [rectangularHilbertMatrix_apply, CStarMatrix.conjTranspose_apply,
      Y, e, rowAdjointVector, tupleSingle_apply]
  have h := (rectangularHilbertMatrix Y.conjTranspose).le_opNorm (tupleSingle 0 ξ)
  rw [hv, norm_tupleSingle, norm_rectangularHilbertMatrix, norm_rectangular_star] at h
  exact h.trans (mul_le_mul_of_nonneg_right hY (norm_nonneg ξ))

theorem CompletelyBoundedBy.rowEnergy {M : VonNeumannAlgebra H}
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ} (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    {n : ℕ} (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (ξ : H) :
    rowEnergy F r ξ ≤ c ^ 2 * ‖ξ‖ ^ 2 := by
  have h := rowAdjointVector_map_bound r hr hc hF ξ
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg ξ))).2 h
  rw [mul_pow, PiLp.norm_sq_eq_of_L2] at hs
  exact hs

end

end KadisonKastler

end OAI
