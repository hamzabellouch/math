import OAI.Analysis.KadisonKastler.FlattenedGraphRow

namespace OAI

/-! # Actual bounded rows detecting the rescaled graph defect

The single bounded graph vector is replicated by independent left
matrix translates, and one common spectral cutoff produces a row whose
norm and retained signal have constants independent of its length.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A graph-supported operator is detected by an actual bounded row of
algebra elements, without any matrix amplification of ordinary distance. -/
theorem exists_bounded_graphRow_signal
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {k : ℕ} (hk : 0 < k)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection M J Ω (Real.sqrt (k : ℝ)) = T)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ j (u v : unitary (H →L[ℂ] H)),
      (u : H →L[ℂ] H) ∈ (E j).algebra → (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) ∧ ‖operatorRow X‖ ≤ 131072 ∧
      ‖T‖ / 16 ≤ finiteRMS (fun i =>
        T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (X i))) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨z, hznorm, hzgraph, hzsignal⟩ := exists_bounded_rescaledGraph_signal M Ω hΩ
    d E hmono hEM hirr hc J hJ (by exact_mod_cast hk) T hT hsupport hcomm hvector hinvariant
  have hzsize : ‖z.val Ω‖ ^ 2 + k * ‖star z.val Ω‖ ^ 2 ≤ 240 := by
    rwa [norm_rescaledGraphVector_sq, Real.sq_sqrt (Nat.cast_nonneg k)] at hzgraph
  obtain ⟨j, ω, hcost⟩ := exists_matrixGraphRow_cost_le M Ω hΩ d E hmono hEM
    hirr hc hk z.val z.property hznorm hzsize
  let Y : Fin k → H →L[ℂ] H := matrixGraphRow (E j) z.val ω
  have hY : ∀ i, Y i ∈ M := fun i =>
    M.mul_mem (hEM j (matrixUnitSignedRepresentation_mem (E j) (ω i))) z.property
  have hnorm (i : Fin k) :
      ‖T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i))‖ =
        ‖T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) z.val)‖ :=
    matrixGraphRow_signal_eq M J hJ Ω _ T (E j) z.val z.property (hcomm j) (hvector j)
      (fun u hu => hinvariant j u 1 hu (E j).algebra.one_mem) ω i
  have hsig : ‖T‖ / 8 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i))) := by
    rw [finiteRMS_eq_of_norm_eq _ (norm_nonneg _) hnorm]
    exact hzsignal
  refine ⟨clippedGraphRow 131072 Y, clippedGraphRow_mem M _ Y hY,
    norm_clippedGraphRow_le (by norm_num) Y, ?_⟩
  exact clippedGraphRow_signal_le hk J Ω T Y hcost hsig

end

end KadisonKastler

end OAI
