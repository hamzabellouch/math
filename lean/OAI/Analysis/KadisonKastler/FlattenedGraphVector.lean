import OAI.Analysis.KadisonKastler.GraphClipping
import OAI.Analysis.KadisonKastler.RescaledGraphSignal

namespace OAI

/-! # A bounded operator retaining the rescaled graph defect

The defining graph vector is normalized, averaged over the actual
finite matrix orbits, sampled with independent signs, and spectrally
clipped. All bounds concern the same resulting algebra element.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance flattenedGraphOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance flattenedGraphStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

private theorem normalizedSignSum_mem
    (M : VonNeumannAlgebra H) {ι : Type*} [Fintype ι]
    (a : ι → H →L[ℂ] H) (ha : ∀ i, a i ∈ M) (ε : ι → Bool) :
    normalizedFiniteSignSum a ε ∈ M := by
  change normalizedFiniteSignSum a ε ∈ M.toStarSubalgebra.restrictScalars ℝ
  unfold normalizedFiniteSignSum finiteSignSum
  apply (M.toStarSubalgebra.restrictScalars ℝ).smul_mem
  apply (M.toStarSubalgebra.restrictScalars ℝ).sum_mem
  intro i _
  exact (M.toStarSubalgebra.restrictScalars ℝ).smul_mem (ha i) _

private theorem matrixOrbitSample_mem
    (M : VonNeumannAlgebra H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra) (x : H →L[ℂ] H) (hx : x ∈ M)
    (g : MatrixOrbitIndex d) : matrixOrbitSample E x g ∈ M := by
  change (matrixUnitSignedRepresentation E g.1 : H →L[ℂ] H) * x *
    star (matrixUnitSignedRepresentation E g.2 : H →L[ℂ] H) ∈ M
  exact M.mul_mem (M.mul_mem (hE (matrixUnitSignedRepresentation_mem E g.1)) hx)
    (M.toStarSubalgebra.star_mem' (hE (matrixUnitSignedRepresentation_mem E g.2)))

/-- A nonzero graph-supported operator has one uniformly bounded algebra
vector which retains a fixed fraction of its norm. The matrix actions
are the actual common left/right actions on the graph. -/
theorem exists_bounded_rescaledGraph_signal
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {k : ℝ} (hk : 1 ≤ k)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection M J Ω (Real.sqrt k) = T)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ j (u v : unitary (H →L[ℂ] H)),
      (u : H →L[ℂ] H) ∈ (E j).algebra → (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ z : Algebra M, ‖z‖ ≤ 128 ∧
      ‖rescaledGraphVector J Ω (Real.sqrt k) z.val‖ ^ 2 ≤ 240 ∧
      ‖T‖ / 8 ≤ ‖T (rescaledGraphVector J Ω (Real.sqrt k) z.val)‖ := by
  obtain ⟨x, hxunit, hxsignal⟩ :=
    exists_normalized_rescaledGraph_signal M J Ω (Real.sqrt k) T hT hsupport
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hxnorm : ‖x.val Ω‖ ^ 2 + k * ‖star x.val Ω‖ ^ 2 = 1 := by
    have hn := norm_rescaledGraphVector_sq J Ω (Real.sqrt k) x.val
    rw [hxunit, Real.sq_sqrt hk0] at hn
    simpa only [one_pow] using hn.symm
  have hpos : 0 < ‖T (rescaledGraphVector J Ω (Real.sqrt k) x.val)‖ :=
    (div_pos (norm_pos_iff.mpr hT) (by norm_num)).trans hxsignal
  obtain ⟨j, m, ω, ε, _, hs, hcost⟩ :=
    exists_rescaledGraph_orbit_signal_and_cost M Ω hΩ d E hmono hEM hirr hc
      x.val x.property J hJ hk hxnorm T hpos hcomm hvector hinvariant
  let y : H →L[ℂ] H := normalizedFiniteSignSum
    (fun i => matrixOrbitSample (E j) x.val (ω i)) ε
  have hy : y ∈ M := normalizedSignSum_mem M _
    (fun i => matrixOrbitSample_mem M (E j) (hEM j) x.val x.property (ω i)) ε
  have hcost' : graphMomentCost Ω ((Real.sqrt k) ^ 2) y ≤ 240 := by
    simpa only [Real.sq_sqrt hk0] using hcost
  have hsignal : ‖T‖ ^ 2 / 8 ≤ ‖T (rescaledGraphVector J Ω (Real.sqrt k) y)‖ ^ 2 := by
    change ‖T (rescaledGraphVector J Ω (Real.sqrt k) x.val)‖ ^ 2 / 2 ≤ _ at hs
    nlinarith [norm_nonneg T]
  refine ⟨⟨spectralClip 128 y, spectralClip_mem_vonNeumannAlgebra M 128 hy⟩, ?_, ?_, ?_⟩
  · exact spectralClip_norm_le (by norm_num) y
  · exact (norm_rescaledGraph_spectralClip_sq_le_cost J Ω (Real.sqrt k)
      (by norm_num : (0 : ℝ) < 128) y).trans hcost'
  · exact graphSignal_spectralClip_128_lower_bound J Ω (Real.sqrt k) T y hcost' hsignal

end

end KadisonKastler

end OAI
