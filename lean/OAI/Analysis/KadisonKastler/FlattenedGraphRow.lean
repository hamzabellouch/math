import OAI.Analysis.KadisonKastler.GraphRowMetric

namespace OAI

/-! # A bounded replicated row retaining the graph signal

A single cutoff of the row square preserves algebra membership and loses
at most one thirty-second of the graph signal in normalized mean square.
The cutoff and the row norm are independent of the row length.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance flattenedRowOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance flattenedRowStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem clippedGraphRow_mem (M : VonNeumannAlgebra H) {I : Type*} [Fintype I]
    (β : ℝ) (Y : I → H →L[ℂ] H) (hY : ∀ i, Y i ∈ M) (i : I) :
    clippedGraphRow β Y i ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra M
  have hA : graphRowSquare Y ∈ M := by
    exact M.toStarSubalgebra.sum_mem (fun i _ =>
      M.mul_mem (hY i) (M.toStarSubalgebra.star_mem' (hY i)))
  have hS : CFC.sqrt (graphRowSquare Y) ∈ M.toStarSubalgebra := by
    rw [CFC.sqrt_eq_real_sqrt _ (graphRowSquare_nonneg Y), cfcₙ_eq_cfc]
    exact cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
      (s := M.toStarSubalgebra) _ hA
  exact M.mul_mem (cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
    (s := M.toStarSubalgebra) _ hS) (hY i)

/-- The common row cutoff has small graph error at the fixed cutoff. -/
theorem clippedGraphRow_error_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (Y : Fin k → H →L[ℂ] H)
    (hcost : graphRowCost Ω Y ≤ 16777216) :
    finiteRMS (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
      (Y i - clippedGraphRow 131072 Y i)) ≤ 1 / 32 := by
  have h := clippedGraphRow_graph_error_le hk J Ω (by norm_num : (0 : ℝ) < 131072) Y
  rw [← finiteRMS_sq] at h
  have hc := h.trans (div_le_div_of_nonneg_right hcost (by norm_num))
  nlinarith [finiteRMS_nonneg (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
    (Y i - clippedGraphRow 131072 Y i))]

/-- A uniformly nonzero row signal survives the same cutoff used for its
operator norm bound. -/
theorem clippedGraphRow_signal_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (Y : Fin k → H →L[ℂ] H) (hcost : graphRowCost Ω Y ≤ 16777216)
    (hsignal : ‖T‖ / 8 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i)))) :
    ‖T‖ / 16 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (clippedGraphRow 131072 Y i))) := by
  let v := fun i => T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (clippedGraphRow 131072 Y i))
  let w := fun i => T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
    (Y i - clippedGraphRow 131072 Y i))
  have he : (fun i => T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i))) =
      (fun i => v i + w i) := by
    funext i
    have h := (rescaledGraphOperatorMap J Ω (Real.sqrt (k : ℝ))).map_sub
      (Y i) (clippedGraphRow 131072 Y i)
    change rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i - clippedGraphRow 131072 Y i) =
      rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i) -
        rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (clippedGraphRow 131072 Y i) at h
    dsimp [v, w]
    rw [h, map_sub]
    abel
  have hw : finiteRMS w ≤ ‖T‖ * (1 / 32) :=
    (finiteRMS_apply_le T _).trans (mul_le_mul_of_nonneg_left
      (clippedGraphRow_error_le hk J Ω Y hcost) (norm_nonneg T))
  rw [he] at hsignal
  have ht := finiteRMS_add_le v w
  change ‖T‖ / 16 ≤ finiteRMS v
  nlinarith [norm_nonneg T]

/-- Every left matrix translate of an algebra element has exactly the
same graph signal when the actual graph action commutes with the defect. -/
theorem matrixGraphRow_signal_eq (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (z : H →L[ℂ] H) (hz : z ∈ M)
    (hcomm : ∀ a, a ∈ E.algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ a, a ∈ E.algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ E.algebra →
      T * (rescaledGraphAction J hJ u 1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u 1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T)
    {I : Type*} (ω : I → SignedPermutation (Fin d)) (i : I) :
    ‖T (rescaledGraphVector J Ω c (matrixGraphRow E z ω i))‖ =
      ‖T (rescaledGraphVector J Ω c z)‖ := by
  let u := matrixUnitSignedRepresentation E (ω i)
  have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E _
  have hus := E.algebra.star_mem' hu
  have hf := norm_graphSignal_unitaryDoubleOrbit M J hJ Ω c T u 1
    (by simpa only [OneMemClass.coe_one, star_one] using hcomm 1 E.algebra.one_mem)
    (by simpa only [star_star] using hcomm _ hus)
    (by simpa only [OneMemClass.coe_one, star_one] using hvector 1 E.algebra.one_mem)
    (by simpa only [star_star] using hvector _ hus)
    (by simpa only [star_one] using hinvariant u hu) z hz
  simpa only [unitaryDoubleOrbit, OneMemClass.coe_one, star_one, mul_one, matrixGraphRow, u] using hf

end

end KadisonKastler

end OAI
