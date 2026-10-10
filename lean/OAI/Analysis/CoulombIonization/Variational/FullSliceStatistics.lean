import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedInnerCap
import OAI.Analysis.CoulombIonization.Localization.Observation

namespace OAI

open MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def fullSlicePair {N M : ℕ} (psi : FormVector (N+M)) (F : FullStatistic)
    (t : Spins M) (v : Configuration M) : ℝ :=
  ∑ s : Spins N, ∫ x : Configuration N, F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2

lemma fullSlicePair_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (F : FullStatistic) (t : Spins M) :
    Integrable (fullSlicePair psi F t) := by
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  apply integrable_finsetSum
  intro s _
  have hi := rawFormPair_integrable hpsi (F.measurable (N+M)) hB (joinLists s t)
  exact (integrable_join hi).integral_prod_right

lemma fullSlicePair_fubini {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (F : FullStatistic) :
    (∑ t : Spins M, ∫ v, fullSlicePair psi F t v) = rawFormPair psi (F.value (N+M)) := by
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  have hi (s : Spins (N+M)) := rawFormPair_integrable hpsi (F.measurable (N+M)) hB s
  have he (s : Spins N) (t : Spins M) :
      (∫ v : Configuration M, ∫ x : Configuration N,
        F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) =
        ∫ x, F.value (N+M) x*‖psi.value (joinLists s t) x‖^2 :=
    integral_join (hi (joinLists s t))
  have hsum (t : Spins M) : (∫ v, fullSlicePair psi F t v) =
      ∑ s : Spins N, ∫ v : Configuration M, ∫ x : Configuration N,
        F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2 := by
    apply integral_finsetSum
    intro s _
    exact (integrable_join (hi (joinLists s t))).integral_prod_right
  simp_rw [hsum,he]
  exact sum_spin_join (fun s : Spins (N+M) => ∫ x,F.value (N+M) x*‖psi.value s x‖^2)

lemma fullSlicePair_eq_zero_of_mass {N M : ℕ} {psi : FormVector (N+M)}
    (F : FullStatistic) (t : Spins M) (v : Configuration M)
    (hpsi : SobolevVector (coreSlice psi t v)) (hm : formMass (coreSlice psi t v) = 0) :
    fullSlicePair psi F t v = 0 := by
  have hz (s : Spins N) : ∀ᵐ x, ‖(coreSlice psi t v).value s x‖^2 = 0 := by
    have hi : (∫ x, ‖(coreSlice psi t v).value s x‖^2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
        (Finset.mem_univ _)
    exact (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (hpsi.1 s).norm.integrable_sq).mp hi
  apply Finset.sum_eq_zero
  intro s _
  apply integral_eq_zero_of_ae
  filter_upwards [hz s] with x hx
  simp only [hx,mul_zero,Pi.zero_apply]

lemma SplitPositionSupport.outer_of_mass_ne_zero {N M : ℕ} {psi : FormVector (N+M)}
    {P Q : Space → Prop} (hs : SplitPositionSupport psi P Q)
    (t : Spins M) (v : Configuration M) (hm : formMass (coreSlice psi t v) ≠ 0) :
    ∀ i, Q (v i) := by
  by_contra! hh
  obtain ⟨i,hi⟩ := hh
  apply hm
  have hz : ∀ s x, (coreSlice psi t v).value s x = 0 := by
    intro s x
    by_contra hn
    exact hi ((hs s t x v hn).2 i)
  simp only [formMass,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero,Finset.sum_const_zero]
end CoulombAtom

end

end OAI
