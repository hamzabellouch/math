import Mathlib
import OAI.Geometry.HyperbolicGroups.CyclicLink

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
open State
variable {V : Type*} [Fintype V]

def T (s : V → State) : ℕ := ∑ i, (s i).turn

def allDominant : State → State
  | .other => .dominant
  | a => a

lemma turn_eq (a : State) : a.turn = a.d + a.n := by cases a <;> rfl
lemma T_eq (s : V → State) : T s = D s + N s := by
  simp only [T,turn_eq,Finset.sum_add_distrib,D,N]
lemma D_allDominant (s : V → State) : D (allDominant ∘ s) = T s := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma N_allDominant (s : V → State) : N (allDominant ∘ s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma Q_allDominant (s : V → State) : Q (allDominant ∘ s) = Q s := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma P_allDominant (next : Equiv.Perm V) (s : V → State) (line : V → Bool) :
    P next (allDominant ∘ s) line = P next s line := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma active_allDominant (a : State) : (allDominant a).active = a.active := by
  cases a <;> rfl

lemma two_turns_le (s : V → State) {i j : V} (hne : i ≠ j)
    (hi : (s i).turn = 1) (hj : (s j).turn = 1) : 2 ≤ T s := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i,j} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)
    (fun i _ _ => Nat.zero_le ((s i).turn))
  simpa [T,hne,hi,hj] using h

/-- A full triangle-only normalized fan link has at least four steps. The
normality condition rules out immediate reversal of the same indexed triangle;
the fan's bipartition rules out odd circuits. -/
lemma triangle_only_four (next : Equiv.Perm V) (line : V → Bool) [Nonempty V]
    (hbip : ∀ i, line i ≠ line (next i))
    (hback : ∀ i, next (next i) ≠ i) : 4 ≤ Fintype.card V := by
  classical
  obtain ⟨i⟩ := ‹Nonempty V›
  have h01 : i ≠ next i := fun h => hbip i (congrArg line h)
  have h12 : next i ≠ next (next i) := fun h => hbip (next i) (congrArg line h)
  have h02 : i ≠ next (next i) := (hback i).symm
  have hcard : 3 ≤ Fintype.card V := by
    have h := Finset.card_le_card (show ({i,next i,next (next i)} : Finset V) ⊆ Finset.univ from
      Finset.subset_univ _)
    simpa [h01,h12,h02] using h
  have parity : 2 * (∑ i, bit (line i)) = Fintype.card V := by
    have hh : (∑ i, (bit (line i) + bit (line (next i)))) = ∑ _ : V, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hbip i
      cases he : line i <;> cases he' : line (next i) <;> simp_all [bit]
    simp only [Finset.sum_add_distrib] at hh
    rw [Equiv.sum_comp next (fun i => bit (line i))] at hh
    simpa [two_mul] using hh
  omega

/-- The full-link inequality in the r-dominant case.
The assumptions are only the ordinary indexed-side normality and the fan's
bipartition, not a pre-assumed apex or isoperimetric inequality. -/
theorem full_instance_bound (next : Equiv.Perm V) (s : V → State) (line : V → Bool)
    [Nonempty V] (hfull : ∀ i, (s i).active = true)
    (hfix : ∀ i, next i ≠ i)
    (hbip : ∀ i, s i = triangle → line i ≠ line (next i))
    (hback : ∀ i, s i = triangle → s (next i) = triangle → next (next i) ≠ i) :
    (4 : ℝ) - 2 * T s ≤ (Q s : ℝ) + P next s line := by
  rcases Nat.lt_trichotomy (T s) 1 with ht | ht | ht
  · have ht0 : T s = 0 := by omega
    have htri : ∀ i, s i = triangle := by
      intro i
      have hi : (s i).turn = 0 := (Finset.sum_eq_zero_iff.mp ht0) i (Finset.mem_univ _)
      have ha := hfull i
      cases he : s i <;> simp_all [State.turn,State.active]
    have hh := triangle_only_four next line (fun i => hbip i (htri i))
      (fun i => hback i (htri i) (htri (next i)))
    have hq : Q s = Fintype.card V := by simp [Q,htri,State.f]
    rw [ht0,hq]
    have hq' : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hh
    have hp : (0:ℝ) ≤ P next s line := Nat.cast_nonneg _
    linarith
  · have hcancel : ∀ i, ¬ (allDominant (s i) = dominant ∧
        allDominant (s (next i)) = dominant) := by
      intro i ⟨hi,hj⟩
      have hai : (s i).turn = 1 := by cases he : s i <;> simp_all [allDominant,State.turn]
      have haj : (s (next i)).turn = 1 := by cases he : s (next i) <;> simp_all [allDominant,State.turn]
      have hh := two_turns_le s (hfix i).symm hai haj
      omega
    have hbip' : ∀ i, (allDominant ∘ s) i = triangle → line i ≠ line (next i) := by
      intro i hi
      apply hbip i
      cases he : s i <;> simp_all [allDominant]
    have hh := dominant_endpoint_bound next (allDominant ∘ s) line hcancel hbip'
    rw [D_allDominant,N_allDominant,Q_allDominant,P_allDominant,
      boundary_full next (allDominant ∘ s) (fun i => (active_allDominant _).trans (hfull i)),ht] at hh
    have hh' : (2:ℝ) ≤ (Q s:ℝ) + P next s line := by exact_mod_cast (by simpa using hh : 2 ≤ Q s + P next s line)
    rw [ht]
    norm_num
    exact hh'
  · have hh : (2:ℝ) ≤ (T s:ℝ) := by exact_mod_cast (show 2 ≤ T s by omega)
    have hq : (0:ℝ) ≤ Q s := Nat.cast_nonneg _
    have hp : (0:ℝ) ≤ P next s line := Nat.cast_nonneg _
    linarith

end HyperbolicObstruction.FanLink
end
end

section

end
end

end OAI
