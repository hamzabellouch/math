import OAI.NumberTheory.Ostmann.Construction.ConstituentRootCoefficient
import OAI.NumberTheory.Ostmann.Construction.ScheduledSampleQuotient

namespace OAI

/-! # The exact final fixed-history pair, with all original support guards -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentPrimeTerm_pair {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t t' : FrequencyTree ℤ n)
    (hroot : frequencyRoot n t = frequencyRoot n t')
    (e : Equiv.Perm (SurvivingConstituent role size n))
    (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
    (q : SurvivingConstituent role size n → P) (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))) =
      if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
        finiteEdgeWeight
          (dirichletGraphEdge (fun i => χ (copyScheduleOrigin n i.val))
            (graphDifference
              (scheduledSurvivorGraph (fun i : Σ a, Fin (size a) => role i.1) pivot n)
              (transportGraph e (scheduledSurvivorGraph
                (fun i : Σ a, Fin (size a) => role i.1) pivot n))))
          (fun i p => scheduledSurvivorUnary (fun i : Σ a, Fin (size a) => role i.1)
              χ κ pivot n t i p *
            conj (scheduledSurvivorUnary (fun i : Σ a, Fin (size a) => role i.1)
              χ κ pivot n t' (e.symm i) p)) (fun i => (q i : ℕ)) *
        (groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (scheduleConstituentWord role size n v).map e)
          childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ))))
      else 0 := by
  have hpair : Pairwise (fun i j => (q (e i) : ℕ).Coprime (q (e j) : ℕ)) ↔
      Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) := by
    constructor
    · intro h i j hij
      simpa only [e.apply_symm_apply] using
        h (show e.symm i ≠ e.symm j from fun hh => hij (e.symm.injective hh))
    · intro h i j hij
      exact h (fun hh => hij (e.injective hh))
  have hleft := groupedFullCoprimeFourierWeight_atom role n (scheduleConstituentWord role size n)
    childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ))
  have hright := groupedFullCoprimeFourierWeight_atom role n
    (fun v => (scheduleConstituentWord role size n v).map e)
    childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ))
  simp only [List.map_map, Function.comp_def] at hright
  change groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
    childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) =
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t at hleft
  change groupedFullCoprimeFourierWeight role n
    (fun v => (scheduleConstituentWord role size n v).map e)
    childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ)) =
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q (e i) : ℕ))).prod) t' at hright
  unfold constituentPrimeTerm
  rw [hpair]
  by_cases hp : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ))
  · rw [ite_eq_left hp, map_mul, ite_eq_left hp, ite_eq_left hp, ← hleft, ← hright]
    have hh := scheduledSamplePhase_invariant_pair
      (fun i : Σ a, Fin (size a) => role i.1) χ κ pivot n t t' hroot e hχ P hP q hp center
    calc
      _ = (groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (scheduleConstituentWord role size n v).map e)
          childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ)))) *
        (scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1) χ κ pivot n t P hP q center *
          conj (scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
            χ κ pivot n t' P hP (fun i => q (e i)) center)) := by ring_nf; rfl
      _ = _ := by rw [hh]; ring
  · simp only [hp, ite_false, mul_zero, map_zero]

end Ostmann

end OAI
