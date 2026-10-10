import OAI.Analysis.KadisonKastler.CyclicAbelianExpectation
import OAI.Analysis.KadisonKastler.SpatialDerivationClosure

namespace OAI

/-! # Abelian averaging of a spatial derivation implementer

A spatial derivation preserving a von Neumann algebra also preserves its
commutant. Averaging over any commuting unitary subgroup of the commutant
keeps the same derivation, preserves the norm bound, and makes the
implementer commute with that subgroup. This is the abelian averaging
step in the spatial splitting argument.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutator_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M.commutant) :
    T * b - b * T ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hab := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  have hDb := VonNeumannAlgebra.mem_commutant_iff.mp hb _ (hT a ha)
  calc
    a * (T * b - b * T) = (T * a) * b - a * b * T -
        ((T * a - a * T) * b) := by noncomm_ring
    _ = (T * a) * b - a * b * T - b * (T * a - a * T) := by rw [hDb]
    _ = T * (a * b) - b * T * a := by
      simp only [mul_sub, ← mul_assoc, ← hab]
      abel
    _ = (T * b - b * T) * a := by rw [hab]; noncomm_ring

theorem unitaryConj_sub_mem_commutant_of_preserves
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (u : unitary (H →L[ℂ] H)) (hu : u.val ∈ M.commutant) :
    unitaryConj u T - T ∈ M.commutant := by
  have hc := commutator_mem_commutant_of_preserves M T hT u.val hu
  have he : unitaryConj u T - T = -(T * u.val - u.val * T) * star u.val := by
    dsimp [unitaryConj]
    rw [neg_mul, sub_mul, mul_assoc T, Unitary.mul_star_self_of_mem u.property, mul_one]
    noncomm_ring
  rw [he]
  exact M.commutant.mul_mem (M.commutant.neg_mem hc)
    (M.commutant.toStarSubalgebra.star_mem' hu)

theorem exists_abelian_averaged_implementer
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (G : Type*) [CommGroup G]
    (U : G →* unitary (H →L[ℂ] H))
    (hU : ∀ g, (U g).val ∈ M.commutant) :
    ∃ S : H →L[ℂ] H, IsSelfAdjoint S ∧ ‖S‖ ≤ ‖T‖ ∧
      S - T ∈ M.commutant ∧ (∀ g, Commute (U g).val S) ∧
      ∀ a ∈ M, S * a - a * S = T * a - a * T := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let m := abelianScalarInvariantMean G
  let S := m.averageConjugation U T
  have hdiff : S - T ∈ M.commutant := by
    have he : S - T = m.operatorMean
        (ScalarInvariantMean.conjugationFamily U T - BoundedContinuousFunction.const G T) := by
      rw [map_sub, m.operatorMean_const]
      rfl
    rw [he]
    apply m.operatorMean_mem
    intro g
    exact unitaryConj_sub_mem_commutant_of_preserves M T hT (U g) (hU g)
  refine ⟨S, ?_, m.averageConjugation_norm_le U T, hdiff, ?_, ?_⟩
  · change star (m.averageConjugation U T) = m.averageConjugation U T
    rw [← completelyPositive_map_star, hsa.star_eq]
  · intro g
    have hi := m.averageConjugation_invariant U T g
    have h := congrArg (fun A : H →L[ℂ] H => A * (U g).val) hi
    change ((U g).val * S * star (U g).val) * (U g).val = S * (U g).val at h
    exact show (U g).val * S = S * (U g).val from
      by simpa only [mul_assoc, (U g).property.1, mul_one] using h
  · intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hdiff a ha
    change a * (S - T) = (S - T) * a at hc
    rw [mul_sub, sub_mul] at hc
    simpa only [neg_sub] using congrArg Neg.neg (sub_eq_sub_iff_sub_eq_sub.mp hc)

end

end KadisonKastler

end OAI
