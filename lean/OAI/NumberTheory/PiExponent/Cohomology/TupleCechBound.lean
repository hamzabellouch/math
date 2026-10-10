import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher

namespace OAI

namespace PiExponent.TupleCechBound
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCechHigher
universe u
variable {J K A : Type*} [AddCommGroup A]

def FullSupport {q : ℕ} (c : Cochain J A q) : Prop :=
  ∀ t j, (∀ i, t i ≠ j) → c t = 0

def pullback (f : K → J) {q : ℕ} (c : Cochain J A q) : Cochain K A q :=
  fun t => c (f ∘ t)

lemma pullback_differential (f : K → J) {q : ℕ} (c : Cochain J A q) :
    pullback f (differential c) = differential (pullback f c) := rfl

lemma contraction_closed {q : ℕ} (c : Cochain J A (q + 1))
    (hc : differential c = 0) (p : J) :
    differential (fun t : Fin (q + 1) → J => c (Fin.cons p t)) = c := by
  funext t
  have h := differential_cons c p t
  rw [hc, Pi.zero_apply] at h
  exact (sub_eq_zero.mp h.symm).symm

def extend (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q) : Cochain J A q := by
  classical
  exact fun t => if h : ∀ i, t i ≠ p then c (fun i => ⟨t i, h i⟩) else 0

lemma extend_pullback (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 1) → {j : J // j ≠ p}) :
    extend p c (Subtype.val ∘ t) = c t := by
  classical
  simp only [extend, Function.comp_apply, dite_eq_left (fun i => (t i).property)]

lemma differential_extend_pullback (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 2) → {j : J // j ≠ p}) :
    differential (extend p c) (Subtype.val ∘ t) = differential c t := by
  simp only [differential]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a => (-1 : ℤ) ^ i.val • a) (extend_pullback p c (t ∘ i.succAbove))

lemma extend_missing (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (hc : FullSupport c) (t : Fin (q + 1) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : extend p c t = 0 := by
  classical
  unfold extend
  split_ifs with h
  · apply hc _ ⟨j, hjp⟩
    intro i he
    exact ht i (congrArg Subtype.val he)
  · rfl

lemma differential_extend_missing (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q) (hc : FullSupport c)
    (t : Fin (q + 2) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : differential (extend p c) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [extend_missing p c hc (t ∘ i.succAbove) j hjp (fun k => ht (i.succAbove k)), smul_zero]

theorem fullSupport_primitives_aux (n : ℕ) :
    ∀ (J : Type u) [Fintype J], Fintype.card J = n →
    ∀ q : ℕ, n ≤ q + 1 → ∀ c : Cochain J A (q + 1),
      differential c = 0 → FullSupport c →
      ∃ b : Cochain J A q, differential b = c ∧ FullSupport b := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ hcard q hq c hc hsupport
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨0, ?_, ?_⟩
      · funext t
        exact isEmptyElim (t 0)
      · intro t
        exact isEmptyElim (t 0)
    | inr hJ =>
      let p : J := Classical.choice hJ
      let b : Cochain J A q := fun t => c (Fin.cons p t)
      have hb : differential b = c := contraction_closed c hc p
      cases q with
      | zero =>
        refine ⟨b, hb, ?_⟩
        let : Subsingleton J := Fintype.card_le_one_iff_subsingleton.mp (hcard ▸ hq)
        intro t j ht
        exact False.elim (ht 0 (Subsingleton.elim _ _))
      | succ q =>
        let K := {j : J // j ≠ p}
        have hKn : Fintype.card K < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := p) (by simp)
        let bK : Cochain K A (q + 1) := pullback Subtype.val b
        have hbK : differential bK = 0 := by
          rw [← pullback_differential, hb]
          funext t
          exact hsupport _ p (fun i => (t i).property)
        have hsK : FullSupport bK := by
          intro t j ht
          apply hsupport _ j.val
          intro i
          cases i using Fin.cases with
          | zero => exact Ne.symm j.property
          | succ i =>
            intro he
            exact ht i (Subtype.ext he)
        obtain ⟨a, ha, hs⟩ := ih (Fintype.card K) hKn K rfl q (by omega) bK hbK hsK
        refine ⟨b - differential (extend p a), ?_, ?_⟩
        · rw [differential_sub, hb, differential_squared, sub_zero]
        · intro t j ht
          change b t - differential (extend p a) t = 0
          by_cases hj : j = p
          · subst j
            let tK : Fin (q + 2) → K := fun i => ⟨t i, ht i⟩
            have hvalue := congrFun ha tK
            have hext := differential_extend_pullback p a tK
            change differential (extend p a) t = differential a tK at hext
            rw [hext, hvalue]
            exact sub_self _
          · have hb0 : b t = 0 := by
              apply hsupport _ j
              intro i
              cases i using Fin.cases with
              | zero => exact Ne.symm hj
              | succ i => exact ht i
            rw [hb0, differential_extend_missing p a hs t j hj ht, sub_self]

theorem fullSupport_primitives [Fintype J] {q : ℕ}
    (hq : Fintype.card J ≤ q + 1) (c : Cochain J A (q + 1))
    (hc : differential c = 0) (hs : FullSupport c) :
    ∃ b : Cochain J A q, differential b = c ∧ FullSupport b :=
  fullSupport_primitives_aux (Fintype.card J) J rfl q hq c hc hs

end
end PiExponent.TupleCechBound

end OAI
