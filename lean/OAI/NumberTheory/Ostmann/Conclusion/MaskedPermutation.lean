import OAI.NumberTheory.Ostmann.Conclusion.ActualAmplitudeNorm
import OAI.NumberTheory.Ostmann.Conclusion.SourcePermutation

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

theorem state_coprime_values_perm {a b : State} (outside : List ℕ)
    (hp : a.giantPlus=b.giantPlus) (hm : a.giantMinus=b.giantMinus)
    (hs : (a.small.map SmallSlot.value).Perm (b.small.map SmallSlot.value)) :
    a.Coprime outside ↔ b.Coprime outside := by
  have hv : a.values.Perm b.values := by
    simp only [State.values,hp,hm]
    exact (hs.cons _).cons _
  exact (hv.append_right outside).pairwise_iff (fun h => h.symm)

theorem supportedRegularTransform_values_perm (g giant : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) {a b : State} (hf : a.frequency=b.frequency)
    (hp : a.giantPlus=b.giantPlus) (hm : a.giantMinus=b.giantMinus)
    (hs : (a.small.map SmallSlot.value).Perm (b.small.map SmallSlot.value)) :
    supportedRegularTransform g giant outside a = supportedRegularTransform g giant outside b := by
  classical
  have hc := state_coprime_values_perm outside hp hm hs
  simp only [supportedRegularTransform,hc,hf]
  split_ifs
  · exact regularTransform_values_perm g giant outside hf hp hm hs
  · rfl

def amplitudeSamplePermutation (sources : SourceFamily) (seed : List SourceSlot)
    (giant spectator : PrimeSource) (m l : ℕ)
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀i, sources (Template.current seed l)[σ i].origin = sources (Template.current seed l)[i].origin) :
    ((Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant) ≃
      ((Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) (sourceAssignmentPermutation sources (Template.current seed l) σ hσ)))

theorem amplitudeSamplePermutation_mass (sources : SourceFamily) (seed : List SourceSlot)
    (giant spectator : PrimeSource) (m l : ℕ)
    (σ : Equiv.Perm (Fin (Template.current seed l).length)) (hσ) (x) :
    (amplitudePrior sources seed giant spectator m l).mass
      (amplitudeSamplePermutation sources seed giant spectator m l σ hσ x) =
    (amplitudePrior sources seed giant spectator m l).mass x := by
  change _ * (_ * (_ * (assignmentPrior sources (Template.current seed l)).mass
    (sourceAssignmentPermutation sources (Template.current seed l) σ hσ x.2.2.2))) = _
  rw [sourceAssignmentPermutation_mass]
  rfl

theorem supportedRegularTransform_amplitudeSamplePermutation (sources : SourceFamily) (seed : List SourceSlot)
    (giant spectator : PrimeSource) (m l : ℕ)
    (σ : Equiv.Perm (Fin (Template.current seed l).length)) (hσ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (x) (s : ℤ) :
    supportedRegularTransform g giantTransform
      (spectatorList spectator (amplitudeSamplePermutation sources seed giant spectator m l σ hσ x).1)
      (outerState sources (Template.current seed l) giant
        (amplitudeSamplePermutation sources seed giant spectator m l σ hσ x).2 s) =
    supportedRegularTransform g giantTransform (spectatorList spectator x.1)
      (outerState sources (Template.current seed l) giant x.2 s) := by
  exact supportedRegularTransform_values_perm _ _ _ rfl rfl rfl
    (sourceAssignmentPermutation_values _ _ _ _ _)

end Ostmann.Conclusion

end

end OAI
