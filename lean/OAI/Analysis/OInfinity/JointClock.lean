import OAI.Analysis.OInfinity.ClockPolar

namespace OAI

/-! # A clock on the actual joint cyclic partition

The clock lies in the source-row algebra. Its source partition is convolved
with a target-row partition. Thus the clock cycles the joint partition
exactly, while both row endomorphisms shift that same partition approximately.
The construction does not replace the joint partition by a source-only one.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma jointRohlinProjection_clock {N : ℕ} [NeZero N]
    (p q : ZMod N → E) (u : E)
    (hp : ∀ i, u * p i = p (i + 1) * u)
    (hq : ∀ j, Commute u (q j)) (k : ZMod N) :
    u * jointRohlinProjection p q k = jointRohlinProjection p q (k + 1) * u := by
  have he : (∑ i, p (i + 1) * q (k - i)) = jointRohlinProjection p q (k + 1) := by
    unfold jointRohlinProjection
    apply Fintype.sum_equiv (Equiv.addRight 1)
    intro i
    change p (i + 1) * q (k - i) = p (i + 1) * q (k + 1 - (i + 1))
    congr 2
    abel
  calc
    _ = ∑ i, u * (p i * q (k - i)) := by rw [jointRohlinProjection, Finset.mul_sum]
    _ = ∑ i, (p (i + 1) * q (k - i)) * u := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, hp i, mul_assoc, (hq (k - i)).eq]
      simp only [mul_assoc]
    _ = _ := by rw [← Finset.sum_mul, he]

private lemma exists_binary_clock_in (B : StarSubalgebra ℂ E) [IsClosed (B : Set E)]
    (s : Fin 2 → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (hmem : ∀ i, s i ∈ B)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : E) (p : ZMod (2 ^ m) → E),
      u ∈ B ∧ u ∈ unitary E ∧ u ^ (2 ^ m) = 1 ∧
      (∀ j, p j ∈ B) ∧ (∀ j, IsStarProjection (p j)) ∧ (∑ j, p j) = 1 ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧
      (∀ j, u * p j = p (j + 1) * u) ∧
      ‖finiteRowShift s u - u‖ < ε ∧
      (∀ i, ‖u * s i - s i * u‖ < ε) ∧
      (∀ j, ‖finiteRowShift s (p j) - p (j + 1)‖ < ε) := by
  let r : Fin 2 × Fin 1 → E := fun i => s i.1
  have hr (i j : Fin 2 × Fin 1) : star (r i) * r j = if i = j then 1 else 0 := by
    rcases i with ⟨i, i'⟩
    rcases j with ⟨j, j'⟩
    have hij : i' = j' := Subsingleton.elim _ _
    subst j'
    simpa only [r, Prod.mk.injEq, and_true] using hs i j
  have hrsum : (∑ i, r i * star (r i)) = 1 := by
    simpa only [r, Fintype.sum_prod_type, Fin.sum_univ_one] using hsum
  obtain ⟨u, p, huB, hu, huN, hpB, hp, hpsum, hpo, hcycle, hshift, hgen, hpshift⟩ :=
    exists_even_clock_partition_in B r hr hrsum (fun i => hmem i.1) m ε hε
  refine ⟨u, p, huB, hu, huN, hpB, hp, hpsum, hpo, hcycle, ?_, ?_, ?_⟩
  · simpa only [r, binary_evenRowShift] using hshift
  · intro i
    exact hgen (i, 0)
  · simpa only [r, binary_evenRowShift] using hpshift

/-- Actual joint partition and its exact finite-order clock. Every object
comes from the two specified commuting full binary rows. -/
lemma exists_joint_binary_clock (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hc : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : E) (e : ZMod (2 ^ m) → E),
      u ∈ unitary E ∧ u ^ (2 ^ m) = 1 ∧
      (∀ k, IsStarProjection (e k)) ∧ (∑ k, e k) = 1 ∧
      (∀ k l, k ≠ l → e k * e l = 0) ∧
      (∀ k, u * e k = e (k + 1) * u) ∧
      ‖finiteRowShift s u - u‖ < ε ∧
      (∀ i, ‖u * s i - s i * u‖ < ε) ∧
      (∀ i, Commute u (t i)) ∧ finiteRowShift t u = u ∧
      (∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ < ε) ∧
      (∀ k, ‖finiteRowShift t (e k) - e (k + 1)‖ < ε) ∧
      (∀ k n, ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * e k -
          e k * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ ≤ 2 * (n : ℝ) * ε) ∧
      ∀ n, ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * u -
          u * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ ≤ (n : ℝ) * ε := by
  let δ := ε / ((2 ^ m : ℕ) + 1 : ℝ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsmall : ((2 ^ m : ℕ) : ℝ) * δ < ε := by
    have he : δ * (((2 ^ m : ℕ) : ℝ) + 1) = ε := by dsimp only [δ]; field_simp
    nlinarith
  have hδε : δ < ε := by
    have he : δ * (((2 ^ m : ℕ) : ℝ) + 1) = ε := by dsimp only [δ]; field_simp
    have hpos : 0 < δ * ((2 ^ m : ℕ) : ℝ) := by positivity
    nlinarith
  obtain ⟨u, p, huB, hu, huN, hpB, hp, hpsum, hpo, hcycle, hshift, hgen, hpshift⟩ :=
    exists_binary_clock_in (closedCuntzRowAlgebra s) s hs hsum
      (mem_closedCuntzRowAlgebra s) m δ hδ
  obtain ⟨q, hqB, hq, hqsum, hqo, hqshift⟩ :=
    exists_binary_cyclic_partition_in (closedCuntzRowAlgebra t) t ht htsum
      (mem_closedCuntzRowAlgebra t) m δ hδ
  have hpq (i j : ZMod (2 ^ m)) : Commute (p i) (q j) :=
    closedCuntzRowAlgebras_commute s t hc (p i) (q j) (hpB i) (hqB j)
  have hSq (i : Fin 2) (j : ZMod (2 ^ m)) : Commute (s i) (q j) :=
    closedCuntzRowAlgebras_commute s t hc (s i) (q j)
      (mem_closedCuntzRowAlgebra s i) (hqB j)
  have hTp (i : Fin 2) (j : ZMod (2 ^ m)) : Commute (t i) (p j) :=
    (closedCuntzRowAlgebras_commute s t hc (p j) (t i)
      (hpB j) (mem_closedCuntzRowAlgebra t i)).symm
  have huq (j : ZMod (2 ^ m)) : Commute u (q j) :=
    closedCuntzRowAlgebras_commute s t hc u (q j) huB (hqB j)
  have huT (i : Fin 2) : Commute u (t i) :=
    closedCuntzRowAlgebras_commute s t hc u (t i) huB (mem_closedCuntzRowAlgebra t i)
  let e := jointRohlinProjection p q
  have hS (k : ZMod (2 ^ m)) : ‖finiteRowShift s (e k) - e (k + 1)‖ < ε := by
    exact (jointRohlinProjection_shift_left_le (finiteCuntzDiagonalHom s hs) p q
      (fun j => finiteRowShift_fixed_of_commutes s hsum (q j) (fun i => hSq i j))
      hq δ (fun j => (hpshift j).le) k).trans_lt hsmall
  have hT (k : ZMod (2 ^ m)) : ‖finiteRowShift t (e k) - e (k + 1)‖ < ε := by
    exact (jointRohlinProjection_shift_right_le (finiteCuntzDiagonalHom t ht) p q
      (fun j => finiteRowShift_fixed_of_commutes t htsum (p j) (fun i => hTp i j))
      hp hpq δ (fun j => (hqshift j).le) k).trans_lt hsmall
  refine ⟨u, e, hu, huN,
    jointRohlinProjection_isStarProjection p q hp hq hpo hpq,
    jointRohlinProjection_sum p q hpsum hqsum,
    jointRohlinProjection_orthogonal p q (fun i => (hp i).isIdempotentElem.eq) hpo hqo hpq,
    jointRohlinProjection_clock p q u hcycle huq,
    hshift.trans hδε, (fun i => (hgen i).trans hδε), huT,
    finiteRowShift_fixed_of_commutes t htsum u (fun i => (huT i).symm), hS, hT, ?_, ?_⟩
  · intro k n
    exact (binaryRowCocycle_joint_commutator_le s t hs ht hsum htsum e ε ε
      (fun j => (hS j).le) (fun j => (hT j).le) k n).trans_eq (by ring)
  · intro n
    exact (binaryRowCocycle_periodic_commutator_le s t hs ht hsum htsum
      (fun _ => u) n ε rfl (fun _ _ => (hshift.trans hδε).le) (fun i => (huT i).symm))

end WeakPureInfiniteness

end

end OAI
