import OAI.Probability.SignedSweeps.InjectionRestriction
import OAI.Probability.SignedSweeps.CoefficientPositivity
import OAI.Probability.SignedSweeps.BlockRestriction

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H E : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_injective_coefficient_positive (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (φ : G →* H) (hφ : Function.Injective φ)
    (f : H → ℂ) (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ (fun g => f (φ g))).IsPositive := by
  let : Fintype φ.range := @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ φ.range
    (fun _ => Classical.propDecidable _) inferInstance
  let e := MonoidHom.ofInjective hφ
  have hp := unitary_coefficientAction_positive (ρ.comp e.symm.toMonoidHom)
    (fun g => hρ (e.symm g)) _ (subgroup_coefficient_positive φ.range f hf)
  rwa [coefficientAction_comp_equiv ρ e (fun h : φ.range => f h)] at hp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

lemma grouped_signed_coefficient_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (f : ∀ j, SymmetricGroup (k j) → ℂ) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (groupedPairTypeProjection e h a b * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f))) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        (pairTypeProjection (h j) (a j) (b j) C *
          coefficientAction (signedWordRepresentation (k j) C) (f j)) := by
  rw [coefficientAction_push]
  simp only [coefficientAction, Finset.mul_sum, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul, MonoidHom.comp_apply, grouped_signed_type_trace,
    productCoefficient, ← Finset.prod_mul_distrib, Fintype.prod_sum]

lemma grouped_signed_coefficient_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (f : (∀ j, SymmetricGroup (k j)) → ℂ) :
    groupedPairTypeProjection e h a b * coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) =
    coefficientAction (signedWordRepresentation p C)
      (coefficientPush (blockPermutation e) f) * groupedPairTypeProjection e h a b := by
  rw [coefficientAction_push]
  exact (coefficientAction_commute _ _ (fun g =>
    (groupedPairTypeProjection_signed_commute e h a b g).symm) f).symm

lemma pairTypeProjection_coefficient_commute {u v : ℕ} (hp : u+v=p)
    (a : Partition u) (b : Partition v) (f : SymmetricGroup p → ℂ) :
    pairTypeProjection hp a b C * coefficientAction (signedWordRepresentation p C) f =
      coefficientAction (signedWordRepresentation p C) f * pairTypeProjection hp a b C :=
  (coefficientAction_commute _ _ (fun g => (pairTypeProjection_signed_commute hp a b g).symm) f).symm

end SignedSweeps
end

end OAI
