import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonKastler.AmenableEmbedding

namespace OAI

/-! # Exact transport of the concrete centre

Conjugating a represented algebra conjugates its concrete centre by the
same unitary. In particular, moving aligned centres back gives a literal
common centre for the resulting pair.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_concreteCenter_iff (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    T ∈ concreteCenter M ↔ T ∈ M ∧ ∀ S ∈ M, S * T = T * S := by
  change (T ∈ M ∧ T ∈ M.commutant) ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]

theorem unitaryConj_mem_concreteCenter {M N : VonNeumannAlgebra H}
    {w : unitary (H →L[ℂ] H)} (hw : Conjugates w M N)
    {T : H →L[ℂ] H} (hT : T ∈ concreteCenter M) :
    unitaryConj w T ∈ concreteCenter N := by
  rw [mem_concreteCenter_iff] at hT ⊢
  constructor
  · change unitaryConj w T ∈ (N : Set (H →L[ℂ] H))
    rw [← hw]
    exact ⟨T, hT.1, rfl⟩
  · intro S hS
    obtain ⟨R, hR, rfl⟩ : S ∈ unitaryConj w '' (M : Set (H →L[ℂ] H)) := by
      rw [hw]
      exact hS
    let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w
    change e R * e T = e T * e R
    simpa only [map_mul] using congrArg e (hT.2 R hR)

/-- The same implementing unitary transports both algebra and centre. -/
theorem Conjugates.concreteCenter {M N : VonNeumannAlgebra H}
    {w : unitary (H →L[ℂ] H)} (hw : Conjugates w M N) :
    Conjugates w (concreteCenter M) (concreteCenter N) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact unitaryConj_mem_concreteCenter hw hT
  · intro T hT
    refine ⟨unitaryConj (star w) T, unitaryConj_mem_concreteCenter hw.symm hT, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star w) T

theorem concreteCenter_unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) :
    concreteCenter (unitaryConjugateAlgebra w M) =
      unitaryConjugateAlgebra w (concreteCenter M) := by
  have hc := (conjugates_unitaryConjugateAlgebra w M).concreteCenter
  apply VonNeumannAlgebra.ext
  intro T
  change T ∈ (concreteCenter (unitaryConjugateAlgebra w M) : Set (H →L[ℂ] H)) ↔
    T ∈ unitaryConj w '' (concreteCenter M : Set (H →L[ℂ] H))
  rw [hc]

/-- Moving back a centre-aligning unitary produces exactly equal centres. -/
theorem concreteCenter_conjugated_neighbor_eq {M N : VonNeumannAlgebra H}
    (w : unitary (H →L[ℂ] H))
    (hw : Conjugates w (concreteCenter M) (concreteCenter N)) :
    concreteCenter (unitaryConjugateAlgebra (star w) N) = concreteCenter M := by
  rw [concreteCenter_unitaryConjugateAlgebra]
  apply VonNeumannAlgebra.ext
  intro T
  change T ∈ unitaryConj (star w) '' (concreteCenter N : Set (H →L[ℂ] H)) ↔
    T ∈ (concreteCenter M : Set (H →L[ℂ] H))
  rw [hw.symm]

end

end KadisonKastler

end OAI
