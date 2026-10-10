import OAI.Probability.GammaPassage.Stationarity
import Mathlib.Analysis.Subadditive

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Mean passage times along a lattice ray form a subadditive sequence. -/
theorem GammaEnvironment.meanPassageSequence_isSubadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : Subadditive (meanPassageSequence P τ z) := by
  intro m n
  exact h.meanPassageSequence_subadditive hs hr z m n

/-- Nonnegative passage times bound the normalized mean sequence below,
including the totalized quotient at `n = 0`. -/
theorem GammaEnvironment.normalized_meanPassage_bddBelow
    (h : GammaEnvironment shape rate P τ) (z : Vertex) :
    BddBelow (Set.range (fun n : ℕ => meanPassageSequence P τ z n / (n : ℝ))) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact div_nonneg (h.meanPassageSequence_nonneg z n) (Nat.cast_nonneg n)

/-- The directional mean constant is the Fekete limit of mean passage times
along a lattice ray, with the infimum taken over positive indices. -/
noncomputable def directionalMeanConstant
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : ℝ :=
  (h.meanPassageSequence_isSubadditive hs hr z).lim

/-- Convergence in the native filter ℕ.atTop, including the zero direction. -/
theorem GammaEnvironment.meanPassageSequence_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    Tendsto (fun n : ℕ => meanPassageSequence P τ z n / (n : ℝ))
      atTop (𝓝 (directionalMeanConstant h hs hr z)) :=
  (h.meanPassageSequence_isSubadditive hs hr z).tendsto_lim
    (h.normalized_meanPassage_bddBelow z)

theorem GammaEnvironment.directionalMeanConstant_nonneg
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : 0 ≤ directionalMeanConstant h hs hr z :=
  ge_of_tendsto (h.meanPassageSequence_tendsto hs hr z)
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (h.meanPassageSequence_nonneg z n) (Nat.cast_nonneg n))

/-- Every positive-index finite mean bounds the limit above. The restriction
n≠0 is native to Fekete's infimum and is not discarded at total division zero. -/
theorem GammaEnvironment.directionalMeanConstant_le_normalized_mean
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) {n : ℕ} (hn : n ≠ 0) :
    directionalMeanConstant h hs hr z ≤ meanPassageSequence P τ z n / (n : ℝ) :=
  (h.meanPassageSequence_isSubadditive hs hr z).lim_le_div
    (h.normalized_meanPassage_bddBelow z) hn

theorem GammaEnvironment.directionalMeanConstant_le_mean
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z ≤
      ∫ ω, passageTime (fun e => τ e ω) 0 z ∂P := by
  have hb := h.directionalMeanConstant_le_normalized_mean hs hr z
    (n := 1) (by simp)
  simpa only [meanPassageSequence, one_nsmul, Nat.cast_one, div_one] using hb

/-- Deterministic path bound; every repeated traversal is charged. This is
finite but does not assert strict positivity in any nonzero direction. -/
theorem GammaEnvironment.directionalMeanConstant_le_path_length
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (ds : List Step) (hend : (0 : Vertex) + displacement ds = z) :
    directionalMeanConstant h hs hr z ≤ (ds.length : ℝ) * (shape / rate) :=
  (h.directionalMeanConstant_le_mean hs hr z).trans
    (h.integral_passageTime_le_path_length hs hr 0 z ds hend)

/-- The zero direction is handled by the actual empty path, not a positivity
assumption or an exception to the convergence statement. -/
theorem GammaEnvironment.directionalMeanConstant_zero
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    directionalMeanConstant h hs hr (0 : Vertex) = 0 := by
  apply le_antisymm _ (h.directionalMeanConstant_nonneg hs hr 0)
  have hb := h.directionalMeanConstant_le_path_length hs hr 0 [] (by simp)
  simpa only [List.length_nil, Nat.cast_zero, zero_mul] using hb

/-- The same native convergence theorem specializes to literal zero at z=0. -/
theorem GammaEnvironment.meanPassageSequence_zero_direction_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    Tendsto (fun n : ℕ => meanPassageSequence P τ (0 : Vertex) n / (n : ℝ))
      atTop (𝓝 0) := by
  simpa only [h.directionalMeanConstant_zero hs hr] using
    h.meanPassageSequence_tendsto hs hr (0 : Vertex)

end GammaFPP

end OAI
