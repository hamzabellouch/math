import Mathlib

namespace OAI

/-!
Signed reflection permutations and strong exchange for arbitrary Coxeter systems.
-/

section


namespace KLInvariance.CoxeterSupport

open CoxeterSystem

universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

noncomputable local instance : DecidableEq W := Classical.decEq W

noncomputable def simpleAction (i : B) : Equiv.Perm (W × ZMod 2) := by
  classical
  let f : W × ZMod 2 → W × ZMod 2 := fun p =>
    (cs.simple i * p.1 * cs.simple i, p.2 + if p.1 = cs.simple i then 1 else 0)
  have hf : Function.Involutive f := by
    rintro ⟨t, a⟩
    dsimp [f]
    have heq : cs.simple i * t * cs.simple i = cs.simple i ↔ t = cs.simple i := by
      constructor
      · intro h
        have := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc] using this
      · rintro rfl
        simp
    simp only [heq]
    ext
    · simp [mul_assoc]
    · split_ifs
      · simp only [add_assoc, ZModModule.add_self, add_zero]
      · simp
  exact ⟨f, f, hf, hf⟩

@[simp] theorem simpleAction_apply (i : B) (t : W) (a : ZMod 2) :
    simpleAction cs i (t, a) =
      (cs.simple i * t * cs.simple i, a + if t = cs.simple i then 1 else 0) := by
  classical
  rfl

noncomputable def wordAction (ω : List B) : Equiv.Perm (W × ZMod 2) :=
  (ω.map (simpleAction cs)).prod

@[simp] theorem wordAction_nil : wordAction cs [] = 1 := rfl

theorem wordAction_concat (ω : List B) (i : B) :
    wordAction cs (ω.concat i) = wordAction cs ω * simpleAction cs i := by
  simp [wordAction]

/-- Signed action records the parity of the genuine left inversion sequence. -/
theorem wordAction_record (ω : List B) (t : W) (a : ZMod 2) :
    wordAction cs ω ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω, a) =
      (t, a + ((cs.leftInvSeq ω).count t : ZMod 2)) := by
  classical
  induction ω using List.reverseRecOn generalizing a with
  | nil => simp [wordAction]
  | append_singleton ω i ih =>
    rw [← List.concat_eq_append, wordAction_concat, Equiv.Perm.mul_apply,
      cs.wordProd_concat, mul_inv_rev, cs.inv_simple, simpleAction_apply]
    have hc : cs.simple i * ((cs.simple i * (cs.wordProd ω)⁻¹) * t *
          (cs.wordProd ω * cs.simple i)) * cs.simple i =
          (cs.wordProd ω)⁻¹ * t * cs.wordProd ω := by
      simp [mul_assoc]
    rw [hc, ih]
    rw [cs.leftInvSeq_concat]
    have heq : (cs.simple i * (cs.wordProd ω)⁻¹) * t *
          (cs.wordProd ω * cs.simple i) = cs.simple i ↔
          t = cs.wordProd ω * cs.simple i * (cs.wordProd ω)⁻¹ := by
      constructor
      · intro h
        have := congrArg (fun z => cs.wordProd ω * cs.simple i * z *
          cs.simple i * (cs.wordProd ω)⁻¹) h
        simpa [mul_assoc] using this
      · rintro rfl
        simp [mul_assoc]
    simp only [List.concat_eq_append, List.count_append, List.count_singleton,
      Nat.cast_add, heq]
    congr 1
    split_ifs <;> simp_all [add_comm, add_left_comm]

/-- The presentation relation has a doubled inversion sequence, so its
signed action is trivial, including for no-relation entries `M i j = 0`. -/
theorem leftInvSeq_alternating_formula (i j : B) (p : ℕ) :
    cs.leftInvSeq (alternatingWord i j (2 * p)) =
      (List.range (2 * p)).map (fun k => cs.simple i * (cs.simple j * cs.simple i) ^ k) := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  have hk0 : k < 2 * p := by simpa using hk
  rw [cs.getElem_leftInvSeq_alternatingWord i j p k hk0,
    List.getElem_map, List.getElem_range]
  rw [cs.prod_alternatingWord_eq_mul_pow]
  simp only [Nat.not_even_iff_odd.mpr (show Odd (2 * k + 1) from ⟨k, rfl⟩),
    ↓reduceIte]
  congr 2
  omega

theorem leftInvSeq_relation_doubled (i j : B) :
    ∃ l : List W, cs.leftInvSeq (alternatingWord i j (2 * M i j)) = l ++ l := by
  let f : ℕ → W := fun k => cs.simple i * (cs.simple j * cs.simple i) ^ k
  refine ⟨(List.range (M i j)).map f, ?_⟩
  rw [leftInvSeq_alternating_formula, two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  dsimp [f]
  rw [pow_add, cs.simple_mul_simple_pow']
  simp

theorem wordAction_alternating (i j : B) (p : ℕ) :
    wordAction cs (alternatingWord i j (2 * p)) =
      (simpleAction cs i * simpleAction cs j) ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega,
      alternatingWord_succ', alternatingWord_succ']
    simp only [Nat.not_even_iff_odd.mpr (show Odd (2 * p + 1) from ⟨p, rfl⟩),
      ↓reduceIte, even_two, Even.mul_right]
    change simpleAction cs i * (simpleAction cs j *
      wordAction cs (alternatingWord i j (2 * p))) = _
    rw [ih, ← mul_assoc, pow_succ']

theorem simpleAction_liftable : M.IsLiftable (simpleAction cs) := by
  intro i j
  rw [← wordAction_alternating]
  apply Equiv.ext
  rintro ⟨t, a⟩
  have h := wordAction_record cs (alternatingWord i j (2 * M i j)) t a
  have hw : cs.wordProd (alternatingWord i j (2 * M i j)) = 1 := by
    rw [cs.prod_alternatingWord_eq_mul_pow]
    simp
  obtain ⟨l, hl⟩ := leftInvSeq_relation_doubled cs i j
  simpa [hw, hl, List.count_append, Nat.cast_add, ZModModule.add_self] using h

noncomputable def reflectionAction : W →* Equiv.Perm (W × ZMod 2) :=
  cs.lift ⟨simpleAction cs, simpleAction_liftable cs⟩

@[simp] theorem reflectionAction_simple (i : B) :
    reflectionAction cs (cs.simple i) = simpleAction cs i :=
  cs.lift_apply_simple (simpleAction_liftable cs) i

theorem reflectionAction_wordProd (ω : List B) :
    reflectionAction cs (cs.wordProd ω) = wordAction cs ω := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, reflectionAction_simple, ih]
    rfl

/-- The signed action is conjugation on labels and a translation on signs. -/
theorem reflectionAction_translation (w t : W) :
    ∃ δ : ZMod 2, ∀ a : ZMod 2,
      reflectionAction cs w (t, a) = (w * t * w⁻¹, a + δ) := by
  classical
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  refine ⟨((cs.leftInvSeq ω).count (cs.wordProd ω * t * (cs.wordProd ω)⁻¹) : ZMod 2), ?_⟩
  intro a
  rw [reflectionAction_wordProd]
  have h := wordAction_record cs ω (cs.wordProd ω * t * (cs.wordProd ω)⁻¹) a
  simpa [mul_assoc] using h

/-- A reflection changes the sign of its own label. This is the critical
conjugation step making the representation yield *strong* exchange. -/
theorem reflectionAction_reflection {t : W} (ht : cs.IsReflection t) (a : ZMod 2) :
    reflectionAction cs t (t, a) = (t, a + 1) := by
  obtain ⟨w, i, rfl⟩ := ht
  obtain ⟨δ, hδ⟩ := reflectionAction_translation cs w⁻¹
    (w * cs.simple i * w⁻¹)
  obtain ⟨ε, hε⟩ := reflectionAction_translation cs w (cs.simple i)
  have hδ' (a : ZMod 2) : reflectionAction cs w⁻¹
      (w * cs.simple i * w⁻¹, a) = (cs.simple i, a + δ) := by
    simpa [mul_assoc] using hδ a
  have hz : δ + ε = 0 := by
    have h := congrArg (fun p : W × ZMod 2 => p.2)
      (Equiv.apply_symm_apply (reflectionAction cs w) (w * cs.simple i * w⁻¹, 0))
    change ((reflectionAction cs w) ((reflectionAction cs w)⁻¹
      (w * cs.simple i * w⁻¹, 0))).2 = 0 at h
    rw [← map_inv, hδ', hε] at h
    simpa using h
  rw [map_mul, map_mul, reflectionAction_simple, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, hδ', simpleAction_apply]
  simp only [cs.simple_mul_simple_self, one_mul, ↓reduceIte]
  rw [hε]
  congr 1
  calc
    (a + δ + 1) + ε = (a + 1) + (δ + ε) := by ring
    _ = a + 1 := by rw [hz, add_zero]


theorem mem_leftInvSeq_of_inversion {ω : List B} (_hω : cs.IsReduced ω)
    {t : W} (ht : cs.IsLeftInversion (cs.wordProd ω) t) :
    t ∈ cs.leftInvSeq ω := by
  classical
  by_contra hnot
  obtain ⟨ν, hν, heq⟩ := cs.exists_isReduced (t * cs.wordProd ω)
  have hw := wordAction_record cs ω t (0 : ZMod 2)
  rw [← reflectionAction_wordProd] at hw
  simp only [List.count_eq_zero.mpr hnot, Nat.cast_zero, add_zero] at hw
  have hv := wordAction_record cs ν t (0 : ZMod 2)
  rw [← reflectionAction_wordProd, ← heq] at hv
  have hin : (t * cs.wordProd ω)⁻¹ * t * (t * cs.wordProd ω) =
      (cs.wordProd ω)⁻¹ * t * cs.wordProd ω := by
    rw [mul_inv_rev, ht.1.inv]
    simp [mul_assoc, ht.1.mul_self]
  rw [hin, map_mul, Equiv.Perm.mul_apply, hw,
    reflectionAction_reflection cs ht.1] at hv
  have hmem : t ∈ cs.leftInvSeq ν := by
    by_contra hnone
    have h := congrArg Prod.snd hv
    simp [List.count_eq_zero.mpr hnone] at h
  have hlt := (cs.isLeftInversion_of_mem_leftInvSeq hν hmem).2
  rw [← heq] at hlt
  have hcancel : t * (t * cs.wordProd ω) = cs.wordProd ω := by
    rw [← mul_assoc, ht.1.mul_self, one_mul]
  rw [hcancel] at hlt
  exact (not_lt_of_ge hlt.le) ht.2

/-- Full strong exchange, with the deletion index in the supplied reduced word. -/
theorem strong_exchange {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : cs.IsLeftInversion (cs.wordProd ω) t) :
    ∃ j : ℕ, j < ω.length ∧ t * cs.wordProd ω = cs.wordProd (ω.eraseIdx j) := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp
    (mem_leftInvSeq_of_inversion cs hω ht)
  refine ⟨j, by simpa using hj, ?_⟩
  rw [← heq, ← List.getD_eq_getElem _ 1 hj]
  exact cs.getD_leftInvSeq_mul_wordProd ω j

end KLInvariance.CoxeterSupport


end

end OAI
