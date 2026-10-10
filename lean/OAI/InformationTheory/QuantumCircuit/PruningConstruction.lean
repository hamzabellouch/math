import OAI.InformationTheory.QuantumCircuit.ProductState

namespace OAI

/-! Pruning reflection circuits by an excitation threshold. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def ReflectionLayer.retain {N : ℕ} (R : ReflectionLayer N) (ψ : State N) (q : ℝ) :
    ReflectionLayer N where
  gates := R.gates.filter (fun A => decide (q ≤ ‖act A.zero ψ‖^2))
  disjoint := R.disjoint.filter _

lemma reflectList_unitary {N : ℕ} (l : List (Count N)) :
    reflectList l ∈ unitary (Operator N) := by
  induction l with
  | nil => simp [reflectList]
  | cons A l ih =>
    exact (unitary (Operator N)).mul_mem (reflect_unitary A) ih

lemma reflectList_zero_commute {N : ℕ} (A : Count N) (l : List (Count N))
    (h : ∀ B ∈ l, Disjoint A.support B.support) : Commute (reflectList l) A.zero := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
  exact reflect_disjoint_zero_commute B A (h B hB).symm

lemma reflect_action_error {N : ℕ} (A : Count N) (ψ : State N) :
    ‖act (reflect A) ψ - ψ‖ = 2 * ‖act A.zero ψ‖ := by
  have heq : act (reflect A) ψ - ψ = act (reflect A - 1) ψ := by rw [act_sub, act_one]
  have halg : reflect A - 1 = (-2 : ℝ) • A.zero := by dsimp [reflect]; module
  rw [heq, halg, act_real_smul, norm_smul, Real.norm_eq_abs]
  norm_num

lemma reflection_filter_error {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support))
    (ψ : State N) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖act (reflectList l) ψ -
      act (reflectList (l.filter (fun A => decide (σ^2 ≤ ‖act A.zero ψ‖^2)))) ψ‖ ≤
        (l.length : ℝ) * (2 * σ) := by
  induction l with
  | nil => simp [reflectList]
  | cons A l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
    have hi := ih hl
    let f := l.filter (fun B => decide (σ^2 ≤ ‖act B.zero ψ‖^2))
    by_cases hp : σ^2 ≤ ‖act A.zero ψ‖^2
    · simp only [List.filter_cons, hp, decide_true, ite_true,
        reflectList, List.map_cons, List.prod_cons, act_mul]
      have heq : act (reflect A) (act (reflectList l) ψ) -
          act (reflect A) (act (reflectList f) ψ) =
          act (reflect A) (act (reflectList l) ψ - act (reflectList f) ψ) := by simp [act]
      change ‖act (reflect A) (act (reflectList l) ψ) -
        act (reflect A) (act (reflectList f) ψ)‖ ≤ _
      rw [heq, act_unitary_norm (reflect_unitary A)]
      have hbudget : (l.length : ℝ) * (2 * σ) ≤ ((A :: l).length : ℝ) * (2 * σ) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; nlinarith
      exact hi.trans hbudget
    · have hsmall : ‖act A.zero ψ‖ ≤ σ := by
        have hn := norm_nonneg (act A.zero ψ)
        nlinarith
      have hc : Commute (reflectList f) A.zero := reflectList_zero_commute A f
        (fun B hB => ha B (List.mem_filter.mp hB).1)
      have hn : ‖act A.zero (act (reflectList f) ψ)‖ = ‖act A.zero ψ‖ := by
        rw [← act_mul, ← hc.eq, act_mul, act_unitary_norm (reflectList_unitary f)]
      have hd : ‖act (reflect A) (act (reflectList f) ψ) - act (reflectList f) ψ‖ ≤ 2 * σ := by
        rw [reflect_action_error, hn]
        linarith
      simp only [List.filter_cons, hp, decide_false, Bool.false_eq_true, ite_false,
        reflectList, List.map_cons, List.prod_cons, act_mul]
      have heq : act (reflect A) (act (reflectList l) ψ) - act (reflectList f) ψ =
          act (reflect A) (act (reflectList l) ψ - act (reflectList f) ψ) +
          (act (reflect A) (act (reflectList f) ψ) - act (reflectList f) ψ) := by
        simp only [act, map_sub]; abel
      change ‖act (reflect A) (act (reflectList l) ψ) - act (reflectList f) ψ‖ ≤ _
      rw [heq]
      apply (norm_add_le _ _).trans
      rw [act_unitary_norm (reflect_unitary A)]
      have hsum := add_le_add hi hd
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hsum

def pruneLayer {N : ℕ} (a : AnalyticLayer N) (ψ : State N) : AnalyticLayer N :=
  match a with
  | .local L => .local L
  | .reflection R => .reflection (R.retain ψ ((N : ℝ)^(-6 : ℝ)))

def pruneCircuit {N : ℕ} : List (AnalyticLayer N) → State N → List (AnalyticLayer N)
  | [], _ => []
  | a :: l, ψ => let a' := pruneLayer a ψ
                a' :: pruneCircuit l (act a'.matrix ψ)

lemma pruneCircuit_length {N : ℕ} (l : List (AnalyticLayer N)) (ψ : State N) :
    (pruneCircuit l ψ).length = l.length := by
  induction l generalizing ψ with
  | nil => rfl
  | cons a l ih => simp only [pruneCircuit, List.length_cons, ih]

def NonemptyGateSupports {N : ℕ} (l : List (AnalyticLayer N)) : Prop :=
  ∀ a ∈ l, ∀ R, a = .reflection R → ∀ A ∈ R.gates, A.support.Nonempty

lemma reflectionLayer_length_le {N : ℕ} (R : ReflectionLayer N)
    (h : ∀ A ∈ R.gates, A.support.Nonempty) : R.gates.length ≤ N := by
  have hh := list_disjoint_hits_length Count.support R.gates R.disjoint Finset.univ
    (fun A hA => by simpa using h A hA)
  simpa using hh

lemma pruneLayer_error {N : ℕ} (hN : 1 ≤ N) (a : AnalyticLayer N)
    (ha : ∀ R, a = .reflection R → ∀ A ∈ R.gates, A.support.Nonempty)
    (ψ : State N) :
    ‖act a.matrix ψ - act (pruneLayer a ψ).matrix ψ‖ ≤ 2 * (N : ℝ)^(-2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  cases a with
  | «local» L => simp [pruneLayer]
  | reflection R =>
    have hs : ((N : ℝ)^(-3 : ℝ))^2 = (N : ℝ)^(-6 : ℝ) := by
      rw [← Real.rpow_mul_natCast hn.le]
      norm_num
    have hh := reflection_filter_error R.gates R.disjoint ψ
      (σ := (N : ℝ)^(-3 : ℝ)) (Real.rpow_nonneg hn.le _)
    rw [hs] at hh
    change ‖act (reflectionMatrix R) ψ -
      act (reflectionMatrix (R.retain ψ ((N : ℝ)^(-6 : ℝ)))) ψ‖ ≤ _
    rw [reflectionMatrix_eq, reflectionMatrix_eq]
    have hlen : (R.gates.length : ℝ) ≤ N := by
      exact_mod_cast reflectionLayer_length_le R (ha R rfl)
    calc
      _ ≤ (R.gates.length : ℝ) * (2 * (N : ℝ)^(-3 : ℝ)) := hh
      _ ≤ (N : ℝ) * (2 * (N : ℝ)^(-3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = _ := by
        have hp : (N : ℝ)^(-2 : ℝ) = (N : ℝ)^(-3 : ℝ) * N := by
          convert Real.rpow_add_one hn.ne' (-3) using 1
          norm_num
        rw [hp]
        ring

theorem pruneCircuit_error {N : ℕ} (hN : 1 ≤ N)
    (l : List (AnalyticLayer N)) (hs : NonemptyGateSupports l) (ψ : State N) :
    ‖act (evolution l) ψ - act (evolution (pruneCircuit l ψ)) ψ‖ ≤
      2 * (l.length : ℝ) * (N : ℝ)^(-2 : ℝ) := by
  induction l generalizing ψ with
  | nil => simp [pruneCircuit]
  | cons a l ih =>
    let a' := pruneLayer a ψ
    let ξ := act a'.matrix ψ
    have htail : NonemptyGateSupports l := fun b hb => hs b (List.mem_cons_of_mem _ hb)
    have hfirst := pruneLayer_error hN a (hs a (List.mem_cons_self ..)) ψ
    have hlast := ih htail ξ
    have heq : act (evolution (a :: l)) ψ - act (evolution (pruneCircuit (a :: l) ψ)) ψ =
        act (evolution l) (act a.matrix ψ - act a'.matrix ψ) +
        (act (evolution l) ξ - act (evolution (pruneCircuit l ξ)) ξ) := by
      simp only [evolution, pruneCircuit, act_mul, a', ξ, act_sub_state]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [act_unitary_norm (evolution_isCircuit l).mem_unitary]
    have hh := add_le_add hfirst hlast
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, add_mul,
      mul_one, one_mul, add_comm, add_left_comm, add_assoc] using hh

lemma pruneCircuit_gate_probability {N : ℕ} (l : List (AnalyticLayer N))
    (ψ : State N) (j : ℕ) (R : ReflectionLayer N)
    (hj : (pruneCircuit l ψ)[j]? = some (.reflection R)) :
    ∀ A ∈ R.gates, (N : ℝ)^(-6 : ℝ) ≤
      ‖act A.zero (act (evolution ((pruneCircuit l ψ).take j)) ψ)‖^2 := by
  induction l generalizing ψ j R with
  | nil => simp [pruneCircuit] at hj
  | cons a l ih =>
    cases j with
    | zero =>
      cases a with
      | «local» L => simp [pruneCircuit, pruneLayer] at hj
      | reflection T =>
        simp only [pruneCircuit, pruneLayer, List.getElem?_cons_zero, Option.some.injEq,
          AnalyticLayer.reflection.injEq] at hj
        subst R
        intro A hA
        simpa only [List.take_zero, evolution, act_one, ReflectionLayer.retain,
          List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hA).2
    | succ j =>
      simp only [pruneCircuit, List.getElem?_cons_succ] at hj
      have hh := ih (act (pruneLayer a ψ).matrix ψ) j R hj
      intro A hA
      have ha := hh A hA
      simpa only [pruneCircuit, List.take_succ_cons, evolution, act_mul] using ha

end QAC

end

end OAI
