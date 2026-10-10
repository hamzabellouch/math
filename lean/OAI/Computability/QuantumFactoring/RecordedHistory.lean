import Mathlib
import OAI.Computability.QuantumFactoring.ExactnessFurther

namespace OAI

section
open scoped BigOperators


/-! The same-history deferred-filter argument of Section 6, at the level of
finite complex amplitudes with all old registers retained.  These are proved
lemmas for the main construction, not assumptions replacing that construction. -/
namespace ExactQuantumFactoring.RecordedHistory
open scoped BigOperators
open ExactQuantumFactoring.Exactness

/-- A fresh controlled computation appends a register, retaining the old one. -/
noncomputable def appendState {H Y : Type*} (ψ : H → ℂ) (fresh : H → Y → ℂ) : H × Y → ℂ :=
  fun hy => ψ hy.1 * fresh hy.1 hy.2

lemma append_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) [DecidablePred passed]
    (pass : H → Y → Prop) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      ∑ h, if passed h then Complex.normSq (ψ h) * outcomeMass (pass h) (fresh h) else 0 := by
  classical
  unfold outcomeMass appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · simp only [hh, true_and, Complex.normSq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  · simp [hh]

/-- The normalized state of idle old work need not be known; exact local mass
on each passing passed suffices. No conditioning on future verification occurs. -/
lemma append_constant_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) (pass : H → Y → Prop)
    (z : ℝ) (hlocal : ∀ h, passed h → outcomeMass (pass h) (fresh h) = z) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      outcomeMass passed ψ * z := by
  classical
  rw [append_mass]
  unfold outcomeMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · have hl : (∑ y, if pass h y then Complex.normSq (fresh h y) else 0) = z :=
      hlocal h hh
    simp [hh, hl]
  · simp [hh]

lemma append_normalized {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ)
    (hψ : ∑ h, Complex.normSq (ψ h) = 1)
    (hfresh : ∀ h, ∑ y, Complex.normSq (fresh h y) = 1) :
    ∑ hy, Complex.normSq (appendState ψ fresh hy) = 1 := by
  simp only [appendState, Complex.normSq_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hfresh, mul_one]
  exact hψ

/-- An ordered history, stored with the most recent outcome first. -/
abbrev History (Y : Type*) (t : ℕ) := Fin t → Y

noncomputable def historyState {Y : Type*}
    (fresh : ∀ t, History Y t → Y → ℂ) : ∀ t, History Y t → ℂ
  | 0, _ => 1
  | t+1, h => historyState fresh t (Fin.tail h) * fresh t (Fin.tail h) (h 0)

def historyPass {Y : Type*} (pass : ∀ t, History Y t → Y → Prop) :
    ∀ t, History Y t → Prop
  | 0, _ => True
  | t+1, h => historyPass pass t (Fin.tail h) ∧ pass t (Fin.tail h) (h 0)

lemma outcomeMass_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : Y → Prop) (ψ : Y → ℂ) :
    outcomeMass (p ∘ e) (ψ ∘ e) = outcomeMass p ψ := by
  classical
  exact e.sum_comp (fun y => if p y then Complex.normSq (ψ y) else 0)

/-- Exactly z at every passing history gives exactly z^L, including all padded
slots. The hypotheses are local unconditioned fresh-register laws, not an
assumption about eventual successful completion. -/
lemma history_mass {Y : Type*} [Fintype Y]
    (fresh : ∀ t, History Y t → Y → ℂ)
    (pass : ∀ t, History Y t → Y → Prop) (z : ℝ)
    (hlocal : ∀ t h, historyPass pass t h → outcomeMass (pass t h) (fresh t h) = z) :
    ∀ L, outcomeMass (historyPass pass L) (historyState fresh L) = z^L := by
  intro L
  induction L with
  | zero => simp [outcomeMass, historyPass, historyState]
  | succ t ht =>
    let e : (History Y t × Y) ≃ History Y (t+1) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Y))
    rw [← outcomeMass_equiv e]
    change outcomeMass
      (fun hy : History Y t × Y => historyPass pass t hy.1 ∧ pass t hy.1 hy.2)
      (appendState (historyState fresh t) (fresh t)) = z^(t+1)
    rw [append_constant_mass _ _ _ _ z (hlocal t), ht, pow_succ]

/-- The two filters are evaluated on the SAME recorded outcome and coins.
This proposition is independent of any stochastic representation of the runs. -/
lemma deferred_event_eq {Run Data : Type*} (trueData : Data)
    (produced : Run → Option Data) (verified : Run → Prop)
    (tests : Data → Run → Prop)
    (hallGood : ∀ r, tests trueData r → produced r = some trueData ∧ verified r)
    (hunique : ∀ r d, produced r = some d → verified r → d = trueData) :
    (fun r => ∃ d, produced r = some d ∧ verified r ∧ tests d r) =
      (fun r => tests trueData r) := by
  funext r
  apply propext
  constructor
  · rintro ⟨d, hd, hv, ht⟩
    rwa [hunique r d hd hv] at ht
  · intro ht
    exact ⟨trueData, (hallGood r ht).1, (hallGood r ht).2, ht⟩

lemma deferred_mass_eq {Run Data : Type*} [Fintype Run] (ψ : Run → ℂ)
    (trueData : Data) (produced : Run → Option Data) (verified : Run → Prop)
    (tests : Data → Run → Prop)
    (hallGood : ∀ r, tests trueData r → produced r = some trueData ∧ verified r)
    (hunique : ∀ r d, produced r = some d → verified r → d = trueData) :
    outcomeMass (fun r => ∃ d, produced r = some d ∧ verified r ∧ tests d r) ψ =
      outcomeMass (tests trueData) ψ := by
  rw [deferred_event_eq trueData produced verified tests hallGood hunique]

end ExactQuantumFactoring.RecordedHistory


end

end OAI
