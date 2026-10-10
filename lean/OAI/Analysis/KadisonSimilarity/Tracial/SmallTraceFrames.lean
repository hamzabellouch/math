import OAI.Analysis.KadisonSimilarity.Tracial.MatrixUnitFamilies

namespace OAI

/-! An unbounded matrix tower supplies the small corner and its complete
finite partial-isometry frame used in the free-corner argument. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  {τ : P →ₗ[ℂ] ℂ} {V : P →ₗ[ℂ] H}

omit [CompleteSpace H] in
/-- The corner may be chosen below any positive prescribed trace bound.
Its matrix-unit column resolves the identity, so no frame existence is an
additional hypothesis. -/
theorem NestedTracialMatrices.exists_small_trace_frame
    (M : NestedTracialMatrices (A := I) τ V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) :
    ∃ (n : ℕ) (_hn : 0 < n) (t : ℝ), 0 < t ∧ t < s ∧
      ∃ F : TracialMatrixUnitColumnFamily τ (Fin n), τ F.corner = (t : ℂ) := by
  have hevent : ∀ᶠ j in Filter.atTop, 1 / s < (Fintype.card (I j) : ℝ) :=
    hsize.eventually (Filter.eventually_gt_atTop (1 / s))
  obtain ⟨j, hj⟩ := hevent.exists
  let n := Fintype.card (I j)
  have hn : 0 < n := Fintype.card_pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨n, hn, 1 / (n : ℝ), one_div_pos.mpr hnR, ?_,
    M.nonemptyFinColumnFamily j, ?_⟩
  · exact (div_lt_iff₀ hnR).mpr (by
      have h := (div_lt_iff₀ hs).mp hj
      simpa only [mul_comm] using h)
  · simpa only [Fintype.card_fin, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast] using (M.nonemptyFinColumnFamily j).trace_corner

end KadisonSimilarity

end

end OAI
