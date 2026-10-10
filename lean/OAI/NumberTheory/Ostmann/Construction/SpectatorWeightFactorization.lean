import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSpectatorHistory
import OAI.NumberTheory.Ostmann.Construction.FullAtomTransferWeight

namespace OAI

/-! # Separating the spectator from the original supported coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate BigOperators

theorem recursiveTransferWeight_mul_leaf {State : Type*}
    (sys : TransferHistorySystem State) (F G : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys (fun σ s => F σ s * G σ s) cutoff n σ t =
      recursiveTransferWeight sys F cutoff n σ t *
        recursiveTransferWeight sys G (fun _ _ _ _ => 1) n σ t := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveTransferWeight]
    split_ifs with hv
    · rw [ih, ih]
      simp only [star_mul, Complex.ofReal_one, one_mul]
      ring
    · simp only [zero_mul]

theorem copyScheduleSurvives_outside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .outside) (n : ℕ) :
    CopyScheduleSurvives role n (copyScheduleOutside n i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih, ?_, ?_⟩ <;> rw [copyScheduleRole_outside, hi] <;> rfl

noncomputable def persistentSpectatorAtom {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .outside) (n : ℕ) : CopyScheduleAtoms role n :=
  ⟨copyScheduleOutside n i, copyScheduleSurvives_outside role i hi n⟩

theorem persistentSpectatorAtom_reverse {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .outside) (n : ℕ) (b : Bool) (P : A)
    (x : CopyScheduleAtoms role (n + 1) → A) :
    reverseCopyLabelMap role n b P x (persistentSpectatorAtom role i hi n) =
      x (persistentSpectatorAtom role i hi (n + 1)) := by
  let y : CopyScheduleY role n := ⟨copyScheduleOutside n i,
    copyScheduleSurvives_outside role i hi n,
    by rw [copyScheduleRole_outside, hi]; rfl,
    by rw [copyScheduleRole_outside, hi]; rfl⟩
  exact reverseCopyLabelMap_retained role n b P x y

theorem coprime_spectator_cast_ne_zero {q P : ℕ} [Fact q.Prime]
    (h : P.Coprime q) : (P : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ P := (ZMod.natCast_eq_zero_iff P q).mp hz
  have ho : q ∣ 1 := by
    rw [← h.gcd_eq_one]
    exact Nat.dvd_gcd hd (dvd_refl q)
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp ho)

/-- The outside prime is unchanged along both branches. Every original
coprimality guard therefore forces the spectator zero convention to pass. -/
theorem full_support_spectator_cutoff {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (i : I) (hi : role i = .outside) {q : ℕ} [Fact q.Prime]
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hq : x (persistentSpectatorAtom role i hi n) = q)
    (hc : scheduleAtomFullCoprimeValid role childBound pivotBound n x t)
    (G : ScheduleAtomState role → ℤ → ℂ) :
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound) G
      (spectatorHistoryCutoff (q := q) (scheduleAtomSystem role childBound pivotBound)) n ⟨n, x⟩ t =
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound) G
      (fun _ _ _ _ => 1) n ⟨n, x⟩ t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let sys := scheduleAtomSystem role childBound pivotBound
    let P := historyPivot sys ⟨n + 1, x⟩ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hPq : P.Coprime q := by
      have h := hc.2.1 (persistentSpectatorAtom role i hi (n + 1))
      simpa only [hq] using h
    have hP0 := coprime_spectator_cast_ne_zero hPq
    have hL := ih (reverseCopyLabelMap role n true P x) t.2.1
      (by rw [persistentSpectatorAtom_reverse]; exact hq) hc.2.2.1
    have hR := ih (reverseCopyLabelMap role n false P x) t.2.2
      (by rw [persistentSpectatorAtom_reverse]; exact hq) hc.2.2.2
    change recursiveTransferWeight sys G _ (n + 1) ⟨n + 1, x⟩ t = _
    simp only [recursiveTransferWeight]
    split_ifs
    · change (spectatorHistoryCutoff sys ⟨n + 1, x⟩ t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) * _ * _ = _
      have hcut : spectatorHistoryCutoff (q := q) sys ⟨n + 1, x⟩ t.1
          (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) = 1 := by
        exact ite_eq_right hP0
      rw [hcut, Complex.ofReal_one, one_mul]
      change _ * star _ = (1 : ℂ) * _ * star _
      simpa only [sys, scheduleAtomSystem, scheduleAtomChild, one_mul, P] using
        congrArg₂ (fun a b : ℂ => a * star b) hL hR
    · rfl

theorem fullAtomTransferWeight_spectator_factor {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : I) (hi : role i = .outside) {q : ℕ} [Fact q.Prime]
    (modulus : ScheduleAtomState role → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (F : ScheduleAtomState role → ℤ → ℂ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hq : x (persistentSpectatorAtom role i hi n) = q) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun σ s => F σ s * spectatorHistoryLeaf modulus g D σ s) n x t =
      fullAtomTransferWeight role childBound pivotBound ranges F n x t *
        spectatorHistoryWeight (scheduleAtomSystem role childBound pivotBound) modulus g D n ⟨n, x⟩ t := by
  unfold fullAtomTransferWeight
  split_ifs with h
  · rw [recursiveTransferWeight_mul_leaf]
    rw [← full_support_spectator_cutoff role childBound pivotBound i hi n x t hq h.1
      (spectatorHistoryLeaf modulus g D)]
    rfl
  · simp only [zero_mul]

theorem fullAtomTransferWeight_mul_leaf {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (F G : ScheduleAtomState role → ℤ → ℂ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun σ s => F σ s * G σ s) n x t =
      fullAtomTransferWeight role childBound pivotBound ranges F n x t *
        recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
          G (fun _ _ _ _ => 1) n ⟨n, x⟩ t := by
  unfold fullAtomTransferWeight
  split_ifs
  · exact recursiveTransferWeight_mul_leaf _ F G _ n ⟨n, x⟩ t
  · exact (zero_mul _).symm

theorem fullAtomTransferWeight_prod_leaf {I J : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (F : ScheduleAtomState role → ℤ → ℂ)
    (G : J → ScheduleAtomState role → ℤ → ℂ) (S : Finset J)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun σ s => F σ s * ∏ j ∈ S, G j σ s) n x t =
      fullAtomTransferWeight role childBound pivotBound ranges F n x t *
        ∏ j ∈ S, recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
          (G j) (fun _ _ _ _ => 1) n ⟨n, x⟩ t := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert j S hj ih =>
    simp only [Finset.prod_insert hj]
    have he : (fun σ s => F σ s * (G j σ s * ∏ k ∈ S, G k σ s)) =
        (fun σ s => (F σ s * G j σ s) * ∏ k ∈ S, G k σ s) := by
      funext σ s
      exact (mul_assoc _ _ _).symm
    rw [he, ih, fullAtomTransferWeight_mul_leaf]
    exact mul_assoc _ _ _

theorem fullAtomTransferWeight_spectator_tree {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : I) (hi : role i = .outside) {q : ℕ} [Fact q.Prime]
    (modulus : ScheduleAtomState role → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (F : ScheduleAtomState role → ℤ → ℂ) {n : ℕ} {C : (ZMod q)ˣ}
    (T : RationalTreeData (ZMod q)ˣ n C)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (XL XR : (ZMod q)ˣ) (bulk : TreeLeafTuple (ZMod q)ˣ n)
    (hq : x (persistentSpectatorAtom role i hi n) = q)
    (hreal : SpectatorHistoryRealizes (scheduleAtomSystem role childBound pivotBound)
      modulus T ⟨n, x⟩ t XL XR bulk) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun σ s => F σ s * spectatorHistoryLeaf modulus g D σ s) n x t =
      fullAtomTransferWeight role childBound pivotBound ranges F n x t *
        rationalTreeAmplitude g D T XL XR (transferConjugations n false) bulk := by
  rw [fullAtomTransferWeight_spectator_factor role childBound pivotBound ranges i hi
    modulus g D F n x t hq]
  congr 1
  exact spectatorHistoryWeight_eq_tree _ modulus g D T ⟨n, x⟩ t XL XR bulk hreal false

end Ostmann

end OAI
