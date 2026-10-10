import OAI.Probability.SATComputability.TrialDisorder

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance trialDescriptionsRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem computable_bool_and :
    Computable (fun p : Bool × Bool => p.1 && p.2) := Primrec.and.to_comp

theorem computable_list_all {A B : Type} [Primcodable A] [Primcodable B]
    {xs : A → List B} {test : A → B → Bool} (hxs : Computable xs) (htest : Computable₂ test) :
    Computable (fun a => (xs a).all (test a)) := by
  have ht : Computable (fun p : A × B => test p.1 p.2) := htest
  have h := computable_list_foldr hxs (Computable.const true)
    (h := fun a p => test a p.1 && p.2)
    (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun a => by induction xs a <;> simp_all)

noncomputable def rationalAt (ms : List ℚ) (i : ℕ) : ℚ := ms[i]?.getD 0

@[fun_prop] theorem rationalAt_computable :
    Computable (fun p : List ℚ × ℕ => rationalAt p.1 p.2) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const (0 : ℚ))).to_comp

theorem rationalAt_get (ms : List ℚ) (i : Fin ms.length) : rationalAt ms i.val = ms.get i := by
  simp [rationalAt]

noncomputable def positiveExponents (ms : List ℚ) : Bool :=
  ms.all (fun q => decide (0 < q))

@[fun_prop] theorem positiveExponents_computable : Computable positiveExponents := by
  apply computable_list_all Computable.id
  unfold Computable₂
  fun_prop

theorem positiveExponents_iff (ms : List ℚ) :
    positiveExponents ms = true ↔ ∀ i : Fin ms.length, 0 < ms.get i := by
  simp only [positiveExponents, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h _ (List.get_mem _ _)
  · intro h q hq
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hq
    exact h i

noncomputable def exponentCheck (ms : List ℚ) : Bool :=
  (List.range ms.length).all (fun i => decide (0 < rationalAt ms i ∧ rationalAt ms i < 1) &&
    (List.range ms.length).all (fun j => decide (j ≤ i ∨ rationalAt ms i < rationalAt ms j)))

attribute [local irreducible] rationalAt

@[fun_prop] theorem exponentCheck_computable : Computable exponentCheck := by
  have hi : Computable (fun ms : List ℚ => List.range ms.length) := by fun_prop
  have hj : Computable (fun p : List ℚ × ℕ =>
      (List.range p.1.length).all (fun j => decide (j ≤ p.2 ∨ rationalAt p.1 p.2 < rationalAt p.1 j))) := by
    apply computable_list_all (by fun_prop)
    unfold Computable₂
    fun_prop
  unfold exponentCheck
  apply computable_list_all hi
  unfold Computable₂
  fun_prop

theorem exponentCheck_iff (ms : List ℚ) :
    exponentCheck ms = true ↔ Exponents (fun i : Fin ms.length => (ms.get i : ℝ)) := by
  simp only [exponentCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h
    constructor
    · intro i j hij
      have hi := ((h i.val i.isLt).2 j.val j.isLt).resolve_left (Nat.not_le_of_gt hij)
      rw [rationalAt_get ms i, rationalAt_get ms j] at hi
      change (ms.get i : ℝ) < ms.get j
      exact_mod_cast hi
    · intro i
      have hi := (h i.val i.isLt).1
      rw [rationalAt_get ms i] at hi
      change 0 < (ms.get i : ℝ) ∧ (ms.get i : ℝ) < 1
      exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
  · intro h i hi
    refine ⟨?_, ?_⟩
    · have hb := h.2 ⟨i,hi⟩
      change 0 < (ms.get ⟨i,hi⟩ : ℝ) ∧ (ms.get ⟨i,hi⟩ : ℝ) < 1 at hb
      rw [rationalAt_get ms ⟨i,hi⟩]
      exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    · intro j hj
      by_cases hij : j ≤ i
      · exact Or.inl hij
      right
      have hm := h.1 (show (⟨i,hi⟩ : Fin ms.length) < ⟨j,hj⟩ from Nat.lt_of_not_ge hij)
      change (ms.get ⟨i,hi⟩ : ℝ) < ms.get ⟨j,hj⟩ at hm
      rw [rationalAt_get ms ⟨i,hi⟩, rationalAt_get ms ⟨j,hj⟩]
      exact_mod_cast hm

theorem exponentCheck_positive {ms : List ℚ} (h : exponentCheck ms = true) :
    positiveExponents ms = true := by
  rw [positiveExponents_iff]
  intro i
  have hp := (((exponentCheck_iff ms).mp h).2 i).1
  change 0 < (ms.get i : ℝ) at hp
  exact_mod_cast hp

end FixedClauseThreshold.Computability

end OAI
