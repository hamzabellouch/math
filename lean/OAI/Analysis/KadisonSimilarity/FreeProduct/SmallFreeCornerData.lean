import OAI.Analysis.KadisonSimilarity.Tracial.SmallTraceFrames
import OAI.Analysis.KadisonSimilarity.Tracial.TracialHalfProjectionData
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerTransport
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteHalfProjection

namespace OAI

/-! The small projection, its full matrix frame, the containing half
projection, and the Haar unitary all belong to the same corner. The matrix
frame is constructed from the tower. Only trace cutting and the local Haar
existence statement are required for the two remaining choices. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact geometric data used in one application of the free-corner
estimate. None of the fields mentions the operator being estimated. -/
structure SmallFreeCornerData (τ : P →ₗ[ℂ] ℂ) (s : ℝ) where
  size : ℕ
  size_pos : 0 < size
  frame : TracialMatrixUnitColumnFamily τ (Fin size)
  trace : ℝ
  trace_pos : 0 < trace
  trace_lt : trace < s
  corner_trace : τ frame.corner = (trace : ℂ)
  half : HalfTraceProjectionData τ frame.corner
  haar : unitary (CStarCorner frame.corner frame.corner_projection)
  moments : HaarCornerMoments τ haar trace

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The frame and its trace are chosen from an actual matrix stage. The
half-projection and Haar hypotheses are the two local diffuse-corner facts,
not any estimate for a commutator. -/
theorem exists_smallFreeCornerData (τ : P →ₗ[ℂ] ℂ) (V : P →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) τ V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    (half : ∀ (e : P), IsStarProjection e → ∀ t : ℝ,
      τ e = (t : ℂ) → t ≤ 1 / 2 → Nonempty (HalfTraceProjectionData τ e))
    (haar : ∀ (e : P) (he : IsStarProjection e) (t : ℝ),
      0 < t → τ e = (t : ℂ) →
      ∃ z : unitary (CStarCorner e he), HaarCornerMoments τ z t)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData τ s) := by
  obtain ⟨n, hn, t, ht, hts, F, hF⟩ :=
    M.exists_small_trace_frame hsize (lt_min hs (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Q⟩ := half F.corner F.corner_projection t hF
    (le_of_lt (lt_of_lt_of_le hts (min_le_right _ _)))
  obtain ⟨z, hz⟩ := haar F.corner F.corner_projection t ht hF
  exact ⟨⟨n, hn, F, t, ht, lt_of_lt_of_le hts (min_le_left _ _), hF, Q, z, hz⟩⟩

section Concrete

open UltrapowerBridge

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {N : VonNeumannAlgebra K}

local instance : IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K)) :=
  Generator.Tracial.base_norm_closed N

/-- The local specialization of H. Thiel, *Diffuse traces and Haar
unitaries*, arXiv:2009.06940v3, Proposition 7.2 and the following paragraph
(printed p.20). A nonzero corner of a diffuse von Neumann algebra is diffuse;
its normalized normal trace has a Haar unitary. The ambient trace is used
here, since multiplying its vanishing moments by the normalization gives
exactly `HaarCornerMoments`. This is an explicit conditional input. -/
def ThielDiffuseCornerHaarInput (τ : TracialRepresentation N) : Prop :=
  ∀ (q : N.toStarSubalgebra) (hq : IsStarProjection q),
    0 < (τ.trace q).re →
      ∃ z : unitary (CStarCorner q hq),
        ∀ k : ℤ, k ≠ 0 → τ.trace (haarCornerPower z k) = 0

/-- Package the cited Haar statement in precisely the normalization used
by the propagation theorem. -/
theorem exists_concreteHaarCorner (τ : TracialRepresentation N)
    (published : ThielDiffuseCornerHaarInput τ)
    (q : N.toStarSubalgebra) (hq : IsStarProjection q)
    {t : ℝ} (ht : 0 < t) (htrace : τ.trace q = (t : ℂ)) :
    ∃ z : unitary (CStarCorner q hq),
      HaarCornerMoments (concreteTraceLinear τ) z t := by
  obtain ⟨z, hz⟩ := published q hq (by simpa only [htrace, Complex.ofReal_re] using ht)
  refine ⟨z, ?_⟩
  intro k hk
  change (t : ℂ)⁻¹ * τ.trace (haarCornerPower z k) = 0
  rw [hz k hk, mul_zero]

/-- Trace cutting supplies the half projection in the concrete diffuse
algebra, and the Haar input supplies the corner unitary. -/
theorem exists_concreteSmallFreeCornerData (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (published : ThielDiffuseCornerHaarInput τ)
    (V : N.toStarSubalgebra →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) (concreteTraceLinear τ) V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData (concreteTraceLinear τ) s) :=
  exists_smallFreeCornerData (concreteTraceLinear τ) V M hsize
    (fun e he _t htrace ht => exists_concreteHalfTraceProjectionData τ hdiff e he htrace ht)
    (fun e he _t ht htrace => exists_concreteHaarCorner τ published e he ht htrace) hs

end Concrete
end KadisonSimilarity

end

end OAI
