import OAI.Analysis.OInfinity.JointRohlin
import OAI.Analysis.OInfinity.RohlinShift
import OAI.Analysis.OInfinity.MixedTower

namespace OAI

/-! # Cyclic partitions inside the two generated row algebras

The existing finite CAR construction is applied inside a closed generated
algebra. Thus the resulting partitions commute with the opposite row and
with one another. The scope remains full coisometric binary rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def closedCuntzRowAlgebra (s : Fin 2 → E) : StarSubalgebra ℂ E :=
  (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure

instance closedCuntzRowAlgebra_isClosed (s : Fin 2 → E) :
    IsClosed (closedCuntzRowAlgebra s : Set E) :=
  StarSubalgebra.isClosed_topologicalClosure _

lemma mem_closedCuntzRowAlgebra (s : Fin 2 → E) (i : Fin 2) :
    s i ∈ closedCuntzRowAlgebra s :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)

lemma closedCuntzRowAlgebra_le_centralizer (s t : Fin 2 → E)
    (hc : bergRowsCommute s t) :
    closedCuntzRowAlgebra t ≤ StarSubalgebra.centralizer ℂ (Set.range s) := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨(hc i j).1.eq, ?_⟩
    simpa only [star_star] using (hc i j).2.star_star.eq
  · exact Set.isClosed_centralizer _

lemma closedCuntzRowAlgebras_commute (s t : Fin 2 → E) (hc : bergRowsCommute s t)
    (x y : E) (hx : x ∈ closedCuntzRowAlgebra s) (hy : y ∈ closedCuntzRowAlgebra t) :
    Commute x y := by
  have hyc := closedCuntzRowAlgebra_le_centralizer s t hc hy
  have hxc : x ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range s) : Set E) :=
    StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ (Set.range s) hx
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hxc) y hyc).1.symm

lemma binary_evenRowShift (s : Fin 2 → E) (x : E) :
    evenRowShift (fun i : Fin 2 × Fin 1 => s i.1) x = finiteRowShift s x := by
  simp [evenRowShift, finiteRowShift, Fintype.sum_prod_type]

lemma sum_zmod_val {N : ℕ} [NeZero N] (f : ℕ → E) :
    (∑ k : ZMod N, f k.val) = ∑ k ∈ Finset.range N, f k := by
  calc
    _ = ∑ k : Fin N, f k.val := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro k
      cases N with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    _ = _ := Fin.sum_univ_eq_sum_range f N

lemma exists_binary_cyclic_partition_in (B : StarSubalgebra ℂ E) [IsClosed (B : Set E)]
    (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (hmem : ∀ i, s i ∈ B)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ZMod (2 ^ m) → E,
      (∀ k, p k ∈ B) ∧ (∀ k, IsStarProjection (p k)) ∧
      (∑ k, p k) = 1 ∧
      (∀ k l, k ≠ l → p k * p l = 0) ∧
      (∀ k, ‖finiteRowShift s (p k) - p (k + 1)‖ < ε) := by
  let S : Fin 2 → B := fun i => ⟨s i, hmem i⟩
  have hS (i j : Fin 2) : star (S i) * S j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      apply Subtype.ext
      change star (s i) * s i = 1
      simpa only [ite_true] using hs i i
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (s i) * s j = 0
      simpa only [ite_eq_right hij] using hs i j
  have hSsum : (∑ i, S i * star (S i)) = 1 := by
    apply Subtype.ext
    change B.subtype (∑ i, S i * star (S i)) = B.subtype 1
    simp only [map_sum, map_mul, map_star, map_one]
    exact hsum
  let r : Fin 2 × Fin 1 → B := fun i => S i.1
  have hr (i j : Fin 2 × Fin 1) : star (r i) * r j = if i = j then 1 else 0 := by
    rcases i with ⟨i, i'⟩
    rcases j with ⟨j, j'⟩
    have he : i' = j' := Subsingleton.elim _ _
    subst j'
    simpa only [r, Prod.mk.injEq, and_true] using hS i j
  have hrsum : (∑ i, r i * star (r i)) = 1 := by
    simpa [r, Fintype.sum_prod_type] using hSsum
  obtain ⟨L, hL, hproj, hsumP, horth, hshift⟩ :=
    exists_evenRohlin_cyclic_partition (1 : B) r (star_one _) (one_mul _) hr hrsum m ε hε
  let P : ℕ → B := evenRohlinProjection (1 : B) r L m
  let p : ZMod (2 ^ m) → E := fun k => (P k.val : E)
  have hmapShift (b : B) : ((evenRowShift r b : B) : E) = finiteRowShift s (b : E) := by
    rw [show r = (fun i : Fin 2 × Fin 1 => S i.1) from rfl, binary_evenRowShift]
    change B.subtype (∑ i, S i * b * star (S i)) = ∑ i, s i * (b : E) * star (s i)
    simp only [map_sum, map_mul, map_star, S]
    rfl
  refine ⟨p, (fun k => (P k.val).property), ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · exact congrArg B.subtype (hproj k.val).isIdempotentElem.eq
    · exact congrArg B.subtype (hproj k.val).isSelfAdjoint.star_eq
  · change (∑ k : ZMod (2 ^ m), (P k.val : E)) = 1
    rw [sum_zmod_val (N := 2 ^ m) (fun j => (P j : E))]
    change (∑ k ∈ Finset.range (2 ^ m), B.subtype (P k)) = B.subtype 1
    rw [← map_sum]
    exact congrArg B.subtype hsumP
  · intro k l hkl
    have hval : k.val ≠ l.val := by
      intro h
      apply hkl
      rw [← ZMod.natCast_zmod_val k, ← ZMod.natCast_zmod_val l, h]
    exact congrArg B.subtype (horth k.val l.val k.val_lt l.val_lt hval)
  · intro k
    have hk : ((k + 1 : ZMod (2 ^ m)).val) = (k.val + 1) % (2 ^ m) := by
      have hcast : k + 1 = ((k.val + 1 : ℕ) : ZMod (2 ^ m)) := by
        simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
      rw [hcast, ZMod.val_natCast]
    change ‖finiteRowShift s (P k.val : E) - (P (k + 1).val : E)‖ < ε
    rw [hk, ← hmapShift]
    exact hshift k.val k.val_lt

/-- Actual common cyclic partitions for commuting full binary rows. The
commutator estimate is uniform over the cells and explicit in the cocycle
length. No commutation with a contraction path is asserted. -/
lemma exists_joint_binary_cyclic_partition (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hc : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ k, IsStarProjection (e k)) ∧ (∑ k, e k) = 1 ∧
      (∀ k l, k ≠ l → e k * e l = 0) ∧
      (∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ < ε) ∧
      (∀ k, ‖finiteRowShift t (e k) - e (k + 1)‖ < ε) ∧
      (∀ k n, ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * e k -
          e k * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ ≤
            2 * (n : ℝ) * ε) := by
  let δ := ε / ((2 ^ m : ℕ) + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ((2 ^ m : ℕ) : ℝ) * δ < ε := by
    have he : δ * (((2 ^ m : ℕ) : ℝ) + 1) = ε := by
      dsimp [δ]
      field_simp
    nlinarith
  obtain ⟨p, hpMem, hp, hpsum, hpo, hpshift⟩ :=
    exists_binary_cyclic_partition_in (closedCuntzRowAlgebra s) s hs hsum
      (mem_closedCuntzRowAlgebra s) m δ hδ
  obtain ⟨q, hqMem, hq, hqsum, hqo, hqshift⟩ :=
    exists_binary_cyclic_partition_in (closedCuntzRowAlgebra t) t ht htsum
      (mem_closedCuntzRowAlgebra t) m δ hδ
  have hpq (i j : ZMod (2 ^ m)) : Commute (p i) (q j) :=
    closedCuntzRowAlgebras_commute s t hc (p i) (q j) (hpMem i) (hqMem j)
  have hSq (i : Fin 2) (j : ZMod (2 ^ m)) : Commute (s i) (q j) :=
    closedCuntzRowAlgebras_commute s t hc (s i) (q j)
      (mem_closedCuntzRowAlgebra s i) (hqMem j)
  have hTp (i : Fin 2) (j : ZMod (2 ^ m)) : Commute (t i) (p j) :=
    (closedCuntzRowAlgebras_commute s t hc (p j) (t i)
      (hpMem j) (mem_closedCuntzRowAlgebra t i)).symm
  let e := jointRohlinProjection p q
  have hS (k : ZMod (2 ^ m)) : ‖finiteRowShift s (e k) - e (k + 1)‖ < ε := by
    have h := jointRohlinProjection_shift_left_le (finiteCuntzDiagonalHom s hs) p q
      (fun j => finiteRowShift_fixed_of_commutes s hsum (q j) (fun i => hSq i j))
      hq δ (fun j => (hpshift j).le) k
    exact h.trans_lt hsmall
  have hT (k : ZMod (2 ^ m)) : ‖finiteRowShift t (e k) - e (k + 1)‖ < ε := by
    have h := jointRohlinProjection_shift_right_le (finiteCuntzDiagonalHom t ht) p q
      (fun j => finiteRowShift_fixed_of_commutes t htsum (p j) (fun i => hTp i j))
      hp hpq δ (fun j => (hqshift j).le) k
    exact h.trans_lt hsmall
  refine ⟨e, jointRohlinProjection_isStarProjection p q hp hq hpo hpq,
    jointRohlinProjection_sum p q hpsum hqsum,
    jointRohlinProjection_orthogonal p q (fun i => (hp i).isIdempotentElem.eq) hpo hqo hpq,
    hS, hT, ?_⟩
  intro k n
  calc
    _ ≤ (n : ℝ) * (ε + ε) := binaryRowCocycle_joint_commutator_le s t hs ht hsum htsum
      e ε ε (fun j => (hS j).le) (fun j => (hT j).le) k n
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
