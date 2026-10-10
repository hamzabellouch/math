import OAI.Analysis.KadisonKastler.MatrixGraphMomentBounds
import OAI.Analysis.KadisonKastler.GraphSignalSelection
import OAI.Analysis.KadisonKastler.RescaledGraphAction

namespace OAI

/-! # Actual orbit samples retaining the rescaled graph signal

The finite matrix moment estimate and the Hilbert sign selection are
combined here. The signal is the image of the graph vector under the
specified bounded operator; its invariance is derived from the common
unitary graph action.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The graph formula is linear on all ambient operators. -/
def rescaledGraphOperatorMap (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ) :
    (H →L[ℂ] H) →ₗ[ℂ] TomitaGraphHilbert H where
  toFun x := rescaledGraphVector J Ω c x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rescaledGraphVector, star_add, map_add, smul_add]
  map_smul' z x := by
    ext i
    fin_cases i
    · simp [rescaledGraphVector]
    · change c • J (star (z • x) Ω) = z • (c • J (star x Ω))
      rw [star_smul, smul_apply, J.map_smulₛₗ]
      change c • (star (star z) • J (star x Ω)) = z • (c • J (star x Ω))
      rw [star_star, smul_comm]

/-- The actual graph signal, viewed as a real-linear map for sign sums. -/
def rescaledGraphSignalMap (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :
    (H →L[ℂ] H) →ₗ[ℝ] TomitaGraphHilbert H :=
  (T.toLinearMap.comp (rescaledGraphOperatorMap J Ω c)).restrictScalars ℝ

@[simp] theorem rescaledGraphSignalMap_apply
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (x : H →L[ℂ] H) :
    rescaledGraphSignalMap J Ω c T x = T (rescaledGraphVector J Ω c x) := rfl

/-- Commutation with the unitary graph action preserves the signal on
an actual two-sided orbit. -/
theorem norm_graphSignal_unitaryDoubleOrbit
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (u v : unitary (H →L[ℂ] H))
    (hvright : conjugationOperator J (v : H →L[ℂ] H) ∈ M.commutant)
    (huright : conjugationOperator J (u : H →L[ℂ] H) ∈ M.commutant)
    (hvΩ : conjugationOperator J (v : H →L[ℂ] H) Ω = star (v : H →L[ℂ] H) Ω)
    (huΩ : conjugationOperator J (u : H →L[ℂ] H) Ω = star (u : H →L[ℂ] H) Ω)
    (hT : T * (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T)
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    ‖T (rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v))‖ =
      ‖T (rescaledGraphVector J Ω c x)‖ := by
  have hf := rescaledGraphAction_vector M J hJ Ω c u (star v)
    (by simpa only [Unitary.coe_star, star_star] using hvright) huright
    (by simpa only [Unitary.coe_star, star_star] using hvΩ) huΩ ⟨x, hx⟩
  change (rescaledGraphAction J hJ u (star v) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x) =
    rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v) at hf
  rw [← hf]
  have he := congrArg (fun A : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H =>
    A (rescaledGraphVector J Ω c x)) hT
  simp only [mul_apply_eq_comp] at he
  rw [he, Unitary.norm_map]

omit [CompleteSpace H] in
/-- The defect between two graph projections commutes with every
common graph unitary that commutes with the two projections. -/
theorem graphProjectionDefect_commutes
    (P Q A : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hP : P * A = A * P) (hQ : Q * A = A * Q) :
    ((1 - Q) * P) * A = A * ((1 - Q) * P) := by
  calc
    _ = (1 - Q) * (P * A) := mul_assoc _ _ _
    _ = (1 - Q) * (A * P) := by rw [hP]
    _ = (A - Q * A) * P := by noncomm_ring
    _ = (A - A * Q) * P := by rw [hQ]
    _ = _ := by simp only [mul_sub, sub_mul, one_mul, mul_assoc]

/-- In a common prepared position, the actual graph defect has the
required common matrix-orbit invariance. -/
theorem rescaledGraphProjectionDefect_commutes
    (M N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRM : R ≤ M.toStarSubalgebra) (hRN : R ≤ N.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (hMcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ M.commutant)
    (hNcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ N.commutant)
    (hvector : ∀ a ∈ R, conjugationOperator J (star a) Ω = a Ω)
    (u v : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ R) (hv : (v : H →L[ℂ] H) ∈ R) :
    ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c) *
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
        ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c) :=
  graphProjectionDefect_commutes _ _ _
    (rescaledGraphProjection_commutes M R hRM J hJ Ω c hMcomm hvector u v hu hv)
    (rescaledGraphProjection_commutes N R hRN J hJ Ω c hNcomm hvector u v hu hv)

section Selection

variable (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M)

include M hΩ hmono hEM hirr hc hx

/-- The matrix cost construction and a constant orbit signal select one
actual sampled operator, rather than a separate sample for each bound. -/
theorem exists_matrixOrbit_signal_and_cost
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k : ℝ} (hk : 1 ≤ k) (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1)
    (L : (H →L[ℂ] H) →ₗ[ℝ] V) {s : ℝ} (hs : 0 < s)
    (hsignal : ∀ j g, ‖L (matrixOrbitSample (E j) x g)‖ ^ 2 = s) :
    ∃ j m, ∃ ω : Fin m → MatrixOrbitIndex (d j), ∃ ε : Fin m → Bool,
      1 ≤ m ∧
      s / 2 ≤ ‖L (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε)‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε) ≤ 240 := by
  obtain ⟨j, m, hm, hcost⟩ := exists_matrixOrbit_graphCost_le_ten M Ω hΩ d E hmono hEM
    hirr hc x hx hk hxnorm
  let : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)⟩
  obtain ⟨ω, ε, hsignal', hcost'⟩ := exists_sampled_sign_signal_and_cost (I := Fin m)
    Ω (le_trans zero_le_one hk) L (matrixOrbitSample (E j) x) hs (hsignal j) hcost
  exact ⟨j, m, ω, ε, hm, hsignal', hcost'⟩

/-- The genuine common graph action discharges the signal-invariance
premise in the simultaneous selection theorem. -/
theorem exists_rescaledGraph_orbit_signal_and_cost
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {k : ℝ} (hk : 1 ≤ k) (hxnorm : ‖x Ω‖ ^ 2 + k * ‖star x Ω‖ ^ 2 = 1)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hs : 0 < ‖T (rescaledGraphVector J Ω (Real.sqrt k) x)‖)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hT : ∀ j (u v : unitary (H →L[ℂ] H)), (u : H →L[ℂ] H) ∈ (E j).algebra →
      (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ j m, ∃ ω : Fin m → MatrixOrbitIndex (d j), ∃ ε : Fin m → Bool,
      1 ≤ m ∧
      ‖T (rescaledGraphVector J Ω (Real.sqrt k) x)‖ ^ 2 / 2 ≤
        ‖T (rescaledGraphVector J Ω (Real.sqrt k)
          (normalizedFiniteSignSum (fun i => matrixOrbitSample (E j) x (ω i)) ε))‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum
        (fun i => matrixOrbitSample (E j) x (ω i)) ε) ≤ 240 := by
  let : InnerProductSpace ℝ (TomitaGraphHilbert H) := InnerProductSpace.complexToReal
  apply exists_matrixOrbit_signal_and_cost M Ω hΩ d E hmono hEM hirr hc x hx hk hxnorm
    (rescaledGraphSignalMap J Ω (Real.sqrt k) T) (sq_pos_of_pos hs)
  intro j g
  let u := matrixUnitSignedRepresentation (E j) g.1
  let v := matrixUnitSignedRepresentation (E j) g.2
  have hu : (u : H →L[ℂ] H) ∈ (E j).algebra := matrixUnitSignedRepresentation_mem _ _
  have hv : (v : H →L[ℂ] H) ∈ (E j).algebra := matrixUnitSignedRepresentation_mem _ _
  have hvs := (E j).algebra.star_mem' hv
  have hus := (E j).algebra.star_mem' hu
  have he := norm_graphSignal_unitaryDoubleOrbit M J hJ Ω (Real.sqrt k) T u v
    (by simpa only [star_star] using hcomm j _ hvs)
    (by simpa only [star_star] using hcomm j _ hus)
    (by simpa only [star_star] using hvector j _ hvs)
    (by simpa only [star_star] using hvector j _ hus)
    (hT j u (star v) hu (by
      change star (v : H →L[ℂ] H) ∈ (E j).algebra.carrier
      exact hvs)) x hx
  simp only [rescaledGraphSignalMap_apply, matrixOrbitSample, u, v, he]

end Selection

end

end KadisonKastler

end OAI
