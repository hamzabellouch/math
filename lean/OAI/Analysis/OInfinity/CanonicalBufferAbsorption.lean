import OAI.Analysis.OInfinity.CanonicalBuffer

namespace OAI

/-! # Absorbing a commuting canonical row into the actual vacuum split

The corner and its connected anchor come from the source row itself.  The
finite target completion is used only at the auxiliary index.  The original
source representation remains explicitly on the complementary corner.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] [Nontrivial E]

/-- A vacuum corner absorbs a proper target prefix.  No commutation of the
corner with the source row is required. -/
lemma BufferAbsorptionCorner.exists_proper_vacuum_absorption
    (D : BufferAbsorptionCorner E) (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (n : ℕ) (hqz : D.q * s (n + 2) = 0)
    (hqt : ∀ i, Commute D.q (t i))
    (hat : ∀ i, Commute (star D.a) (t i))
    (hbt : ∀ i, Commute (star D.b) (t i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : unitary E, Joined D.anchor U ∧
      ∀ i : Fin n,
        ‖(U : E) * s i * star (U : E) -
          (t i * D.q + D.w * s i * star D.w)‖ < ε := by
  let x : Fin (n + 1) → E := fun i => t i * D.q
  have hxs (i : Fin (n + 1)) : D.q * x i = x i ∧ x i * D.q = x i := by
    constructor
    · change D.q * (t i * D.q) = t i * D.q
      rw [← mul_assoc, (hqt i).eq, mul_assoc, D.projection.isIdempotentElem.eq]
    · change (t i * D.q) * D.q = t i * D.q
      rw [mul_assoc, D.projection.isIdempotentElem.eq]
  have hx (i j : Fin (n + 1)) : star (x i) * x j = if i = j then D.q else 0 := by
    change star (t i * D.q) * (t j * D.q) = _
    rw [star_mul, D.projection.isSelfAdjoint.star_eq]
    calc
      _ = D.q * (star (t i) * t j) * D.q := by noncomm_ring
      _ = _ := by
        by_cases hij : i = j
        · subst j
          simp only [ht, ite_true, mul_one, D.projection.isIdempotentElem.eq]
        · rw [ht, ite_eq_right (fun h => hij (Fin.ext h)),
            ite_eq_right hij, mul_zero, zero_mul]
  obtain ⟨T, hTx, hTq, hT, hTs⟩ := D.extend_finite_proper_row n x hxs hx
  let S : Fin (n + 1) → E := Fin.cons (s n) (fun i : Fin n => s i)
  have hS (i j : Fin (n + 1)) : star (S i) * S j = if i = j then 1 else 0 := by
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [S, Fin.cons_zero, ite_true] using hs n n
    · have hne : n ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        (Fin.succ_ne_zero j).symm] using hs n j
    · have hne : (i : ℕ) ≠ n := by omega
      simpa only [S, Fin.cons_zero, Fin.cons_succ, hne, ite_false,
        Fin.succ_ne_zero] using hs i n
    · simpa only [S, Fin.cons_succ, Fin.succ_inj, Fin.ext_iff,
        Fin.val_succ, Nat.succ.injEq] using hs i j
  have hroot (i : Fin (n + 1)) : star (s (n + 1)) * S i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [S, Fin.cons_zero, Nat.add_one_ne_self, ite_false] using hs (n + 1) n
    · have hne : n + 1 ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_succ, hne, ite_false] using hs (n + 1) j
  have hspare (i : Fin (n + 1)) : star (s (n + 2)) * S i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · have hne : n + 2 ≠ n := by omega
      simpa only [S, Fin.cons_zero, hne, ite_false] using hs (n + 2) n
    · have hne : n + 2 ≠ (j : ℕ) := by omega
      simpa only [S, Fin.cons_succ, hne, ite_false] using hs (n + 2) j
  have haT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.a) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.a) (t j * D.q)
      exact (hat j).mul_right (D.a_star_right.trans D.a_star_left.symm)
  have hbT (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) : Commute (star D.b) (T i) := by
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; exact (Nat.lt_irrefl 0 h).elim
    · intro _
      rw [hTx]
      change Commute (star D.b) (t j * D.q)
      exact (hbt j).mul_right (D.b_star_right.trans D.b_star_left.symm)
  obtain ⟨U, hU, hUi⟩ := D.exists_vacuum_absorption_on S T (s (n + 1)) (s (n + 2))
    (fun i => 0 < (i : ℕ))
    (by simpa only [ite_true] using hs (n + 1) (n + 1)) hroot hS
    (by simpa only [ite_true] using hs (n + 2) (n + 2)) hqz
    (by rw [hs, ite_eq_right (by omega)]) hspare
    (fun i => (hTq i).2) hTs hT haT hbT ε hε
  refine ⟨U, hU, fun i => ?_⟩
  have hi := hUi i.succ (by simp)
  rw [hTx] at hi
  change ‖(U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)‖ < ε at hi
  have hmul : ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E)) *
      star (U : E) = (U : E) * s i * star (U : E) -
        (x i.castSucc + D.w * s i * star D.w) := by
    rw [sub_mul, mul_assoc _ (U : E), Unitary.mul_star_self_of_mem U.property, mul_one]
  have hnorm := CStarRing.norm_mul_mem_unitary
    ((U : E) * s i - (x i.castSucc + D.w * s i * star D.w) * (U : E))
    (Unitary.star_mem U.property)
  rw [hmul] at hnorm
  have hc : ‖(U : E) * s i * star (U : E) -
      (x i.castSucc + D.w * s i * star D.w)‖ < ε := by
    rw [hnorm]
    exact hi
  simpa only [x, Fin.val_castSucc] using hc

/-- All geometric, coefficient-commutation and connected-anchor hypotheses
are supplied by the two commuting canonical rows.  The independently
chosen tolerance `κ` controls the source's actual finite vacuum split. -/
lemma exists_connected_canonical_buffer_absorption
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hst : bergRowsCommute s t) (n : ℕ)
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ D : BufferAbsorptionCorner E, ∃ U : unitary E,
      Joined (1 : unitary E) U ∧ D.q ≠ 0 ∧
      (∀ i : Fin (n + 1), ‖s i * D.q - D.q * s i‖ < κ) ∧
      (∀ i : Fin (n + 1),
        ‖D.q * s i * D.q - zeroCornerRow D.q D.a D.b n i‖ < κ) ∧
      (∀ i, Commute D.q (t i) ∧ Commute D.w (t i) ∧
        Commute D.a (t i) ∧ Commute D.b (t i)) ∧
      (∀ i : Fin n,
        ‖(U : E) * s i * star (U : E) -
          (t i * D.q + D.w * s i * star D.w)‖ < ε) := by
  obtain ⟨D, hanchor, hqne, hqz, hqc, hcomp, hcomm⟩ :=
    exists_canonical_connected_absorption_corner s hs n κ hκ
  have htc (i : ℕ) : ∀ j, Commute (s j) (t i) ∧ Commute (star (s j)) (t i) := by
    intro j
    exact ⟨(hst j i).1, by simpa only [star_star] using (hst j i).2.star_star⟩
  have htcs (i : ℕ) : ∀ j, Commute (s j) (star (t i)) ∧
      Commute (star (s j)) (star (t i)) := by
    intro j
    exact ⟨(hst j i).2, (hst j i).1.star_star⟩
  have hqt (i : ℕ) := (hcomm (t i) (htc i)).1
  have hat (i : ℕ) : Commute (star D.a) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.1.star_star
  have hbt (i : ℕ) : Commute (star D.b) (t i) := by
    simpa only [star_star] using (hcomm (star (t i)) (htcs i)).2.2.2.star_star
  obtain ⟨U, hU, hUi⟩ := D.exists_proper_vacuum_absorption s t hs ht n hqz hqt hat hbt ε hε
  exact ⟨D, U, hanchor.trans hU, hqne, hqc, hcomp,
    fun i => hcomm (t i) (htc i), hUi⟩

end WeakPureInfiniteness

end

end OAI
