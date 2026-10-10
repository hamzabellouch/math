import OAI.Computability.MeanPayoff.ErrorBounds

namespace OAI

section

namespace MeanPayoff

theorem admissible_bottom {n : ℕ} (P : Budgets n) (F : Vec (Fin n) → Vec (Fin n))
    {a b : Vec (Fin n)} (hab : a ≤ b) : AdmissibleSub F a b a P := by
  refine ⟨⟨⟨le_rfl, hab⟩, fun i hi => (lt_irrefl _ hi).elim⟩, ?_⟩
  simpa [mass, lowerActive] using P.k_pos.le

theorem admissible_top {n : ℕ} (P : Budgets n) (F : Vec (Fin n) → Vec (Fin n))
    {a b : Vec (Fin n)} (hab : a ≤ b) : AdmissibleSuper F a b b P := by
  refine ⟨⟨⟨hab, le_rfl⟩, fun i hi => (lt_irrefl _ hi).elim⟩, ?_⟩
  simpa [mass, upperActive] using P.m_pos.le

theorem solve_comparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n) :
    Comparisons G P (solve G (Bmax := Bmax) P) := by
  classical
  by_cases hR : P.parameter < 1
  · constructor
    · intro I y hy
      have hc := (small_rank_comparisons P hR hy (admissible_top P (operator G) I.ordered)).1
      have hc' : y ≤ (I.smallVector P).val := hc
      rw [solve, dite_eq_left hR, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc')]
      norm_num
    · intro I z hz
      have hc := (small_rank_comparisons P hR (admissible_bottom P (operator G) I.ordered) hz).2
      have hc' : (I.smallVector P).val ≤ z := hc
      rw [solve, dite_eq_left hR, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc')]
      norm_num
  · have hl : LowerComparisons G (Bmax := Bmax) P (fun Q _ K => solve G Q K) := by
      intro Q hQ
      exact solve_comparisons G Q
    constructor
    · intro I y hy
      rw [solve, dite_eq_right hR]
      exact (solveWidth_high G P (le_of_not_gt hR) _ hl I y hy).trans (width_error_small I)
    · intro I z hz
      rw [solve, dite_eq_right hR]
      exact (solveWidth_low G P (le_of_not_gt hR) _ hl I z hz).trans (width_error_small I)
termination_by parameterRank P.parameter



def rootBudgets (G : Game) : Budgets G.n where
  alpha := fun _ => 1
  beta := fun _ => 1
  k := G.n
  m := G.n
  alpha_pos := fun _ => by norm_num
  beta_pos := fun _ => by norm_num
  k_pos := by exact_mod_cast G.positive
  m_pos := by exact_mod_cast G.positive

theorem rootBudgets_parameter (G : Game) : (rootBudgets G).parameter = (G.n : ℚ) ^ 3 := by
  simp [Budgets.parameter, Budgets.totalDensity, Budgets.density, mass, rootBudgets]
  ring

theorem topWidth_positive (G : Game) : 0 < topWidth G := by
  unfold topWidth
  exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast G.positive)) (weightBound_positive G)

def rootBox (G : Game) : SolveBox G.n (topWidth G).toNat where
  a := fun _ => 0
  b := fun _ => topWidth G
  ordered := fun _ => (topWidth_positive G).le
  width := (topWidth G).toNat
  positive := by have h := topWidth_positive G; omega
  bounded := le_rfl
  width_bound := fun _ => by rw [Int.toNat_of_nonneg (topWidth_positive G).le]; omega

theorem root_sub_admissible (G : Game) {y : Vec (Fin G.n)}
    (hy : Subsolution (operator G) (rootBox G).a (rootBox G).b y) :
    AdmissibleSub (operator G) (rootBox G).a (rootBox G).b y (rootBudgets G) := by
  refine ⟨hy, ?_⟩
  have h := Finset.card_le_card (Finset.subset_univ (lowerActive (rootBox G).a y))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simpa [mass, rootBudgets] using (show ((lowerActive (rootBox G).a y).card : ℚ) ≤ G.n by exact_mod_cast h)

theorem root_super_admissible (G : Game) {z : Vec (Fin G.n)}
    (hz : Supersolution (operator G) (rootBox G).a (rootBox G).b z) :
    AdmissibleSuper (operator G) (rootBox G).a (rootBox G).b z (rootBudgets G) := by
  refine ⟨hz, ?_⟩
  have h := Finset.card_le_card (Finset.subset_univ (upperActive (rootBox G).b z))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simpa [mass, rootBudgets] using (show ((upperActive (rootBox G).b z).card : ℚ) ≤ G.n by exact_mod_cast h)

theorem solve_root_exact (G : Game) :
    (solve G (rootBudgets G) (rootBox G)).probability
      (fun p => p.val ≠ ((rootBox G).exactVector G).val) ≤ 1 / 8 := by
  let I := rootBox G
  let x := (I.exactVector G).val
  have hx := basic_spec G I.a I.b I.ordered
  have h := solve_comparisons G (Bmax := (topWidth G).toNat) (rootBudgets G)
  have hhi := h.1 I x (root_sub_admissible G hx.1)
  have hlo := h.2 I x (root_super_admissible G hx.2.1)
  have hu := RandomTree.probability_union (solve G (rootBudgets G) I)
    (fun p => ¬x ≤ p.val) (fun p => ¬p.val ≤ x)
  have hsub : (solve G (rootBudgets G) I).probability (fun p => p.val ≠ x) ≤
      (solve G (rootBudgets G) I).probability (fun p => ¬x ≤ p.val ∨ ¬p.val ≤ x) := by
    apply RandomTree.probability_mono
    intro p hp
    by_contra han
    have hh := not_or.mp han
    exact hp (le_antisymm (not_not.mp hh.2) (not_not.mp hh.1))
  exact hsub.trans (hu.trans (by linarith only [hhi, hlo]))

def gameSolve (G : Game) : RandomTree (Fin G.n → Bool) :=
  (solve G (rootBudgets G) (rootBox G)).map fun p v => decide (topWidth G / 2 < p.val v)

def CorrectSet (G : Game) (out : Fin G.n → Bool) : Prop := ∀ v, out v = true ↔ Winning G v

theorem gameSolve_failure (G : Game) :
    (gameSolve G).probability (fun out => ¬CorrectSet G out) ≤ 1 / 8 := by
  rw [gameSolve, RandomTree.probability_map]
  apply le_trans (RandomTree.probability_mono _ (fun p hp => ?_)) (solve_root_exact G)
  intro heq
  apply hp
  intro v
  simp only [decide_eq_true_eq]
  rw [heq]
  exact (winning_iff_high G
    ⟨(basic_spec G (rootBox G).a (rootBox G).b (rootBox G).ordered).1,
      (basic_spec G (rootBox G).a (rootBox G).b (rootBox G).ordered).2.1⟩ v).symm

theorem gameSolve_success (G : Game) :
    7 / 8 ≤ (gameSolve G).probability (CorrectSet G) := by
  have h := gameSolve_failure G
  rw [RandomTree.probability_compl] at h
  linarith only [h]


namespace RandomTree

@[simp] theorem leaf_bind {α β : Type} (a : α) (f : α → RandomTree β) :
    (leaf a).bind f = f a := rfl

@[simp] theorem bind_leaf {α : Type} (t : RandomTree α) : t.bind leaf = t := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, il, ir]

@[simp] theorem bind_assoc {α β γ : Type} (t : RandomTree α)
    (f : α → RandomTree β) (g : β → RandomTree γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, il, ir]

@[simp] theorem map_map {α β γ : Type} (t : RandomTree α) (f : α → β) (g : β → γ) :
    (t.map f).map g = t.map (fun a => g (f a)) := by simp [map]

@[simp] theorem bind_map {α β γ : Type} (t : RandomTree α) (f : α → β)
    (g : β → RandomTree γ) : (t.map f).bind g = t.bind (fun a => g (f a)) := by
  simp [map]

@[simp] theorem all_map {α β : Type} (t : RandomTree α) (f : α → β) (P : β → Prop) :
    (t.map f).All P ↔ t.All (fun a => P (f a)) := by
  simp only [map, all_bind, All]

end RandomTree

structure Counted (α : Type) where
  tree : RandomTree (α × ℕ)

namespace Counted

def pure {α : Type} (a : α) : Counted α := ⟨.leaf (a, 0)⟩
def lift {α : Type} (t : RandomTree α) : Counted α := ⟨t.map (fun a => (a, 0))⟩
def map {α β : Type} (f : α → β) (t : Counted α) : Counted β :=
  ⟨t.tree.map (fun p => (f p.1, p.2))⟩
def bind {α β : Type} (t : Counted α) (f : α → Counted β) : Counted β :=
  ⟨t.tree.bind fun p => (f p.1).tree.map (fun q => (q.1, p.2 + q.2))⟩
def charge {α : Type} (c : ℕ) (t : Counted α) : Counted α :=
  ⟨t.tree.map (fun p => (p.1, c + p.2))⟩
def erase {α : Type} (t : Counted α) : RandomTree α := t.tree.map Prod.fst
def Bounded {α : Type} (t : Counted α) (N : ℕ) : Prop := t.tree.All (fun p => p.2 ≤ N)

@[simp] theorem erase_pure {α : Type} (a : α) : (pure a).erase = .leaf a := rfl
@[simp] theorem erase_lift {α : Type} (t : RandomTree α) : (lift t).erase = t := by
  simp [erase, lift, RandomTree.map]
@[simp] theorem erase_map {α β : Type} (t : Counted α) (f : α → β) :
    (t.map f).erase = t.erase.map f := by simp [erase, map]
@[simp] theorem erase_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    (t.bind f).erase = t.erase.bind (fun a => (f a).erase) := by
  simp [erase, bind, RandomTree.map_bind]
@[simp] theorem erase_charge {α : Type} (c : ℕ) (t : Counted α) :
    (t.charge c).erase = t.erase := by simp [erase, charge]

theorem bounded_pure {α : Type} (a : α) {N : ℕ} : (pure a).Bounded N := Nat.zero_le N

theorem bounded_lift {α : Type} (t : RandomTree α) : (lift t).Bounded 0 := by
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_of_forall _ (fun _ => le_rfl)

theorem bounded_mono {α : Type} {t : Counted α} {N M : ℕ} (h : t.Bounded N) (hle : N ≤ M) :
    t.Bounded M := RandomTree.all_mono _ h (fun _ hp => hp.trans hle)

theorem bounded_map {α β : Type} {t : Counted α} (f : α → β) {N : ℕ} (h : t.Bounded N) :
    (t.map f).Bounded N := (RandomTree.all_map _ _ _).mpr h

theorem bounded_charge {α : Type} {t : Counted α} (c : ℕ) {N : ℕ} (h : t.Bounded N) :
    (t.charge c).Bounded (c + N) := by
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ h (fun _ hp => Nat.add_le_add_left hp c)

theorem bounded_bind {α β : Type} {t : Counted α} (f : α → Counted β) {N M : ℕ}
    (h : t.Bounded N) (hf : ∀ a, (f a).Bounded M) : (t.bind f).Bounded (N + M) := by
  change (t.tree.bind _).All _
  rw [RandomTree.all_bind]
  apply RandomTree.all_mono _ h
  intro p hp
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ (hf p.1) (fun q hq => Nat.add_le_add hp hq)

theorem bounded_bind_qualified {α β : Type} {t : Counted α} (f : α → Counted β)
    (P : α → Prop) {N M : ℕ} (h : t.Bounded N) (hp : t.erase.All P)
    (hf : ∀ a, P a → (f a).Bounded M) : (t.bind f).Bounded (N + M) := by
  change (t.tree.bind _).All _
  rw [RandomTree.all_bind]
  have hP : t.tree.All (fun p => P p.1) := (RandomTree.all_map _ _ _).mp hp
  apply RandomTree.all_mono _ (RandomTree.all_and _ h hP)
  intro p hp
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ (hf p.1 hp.2) (fun q hq => Nat.add_le_add hp.1 hq)

def trials {α : Type} (t : Counted α) : ℕ → Counted (List α)
  | 0 => pure []
  | J + 1 => t.bind fun a => (trials t J).map (a :: ·)

def traverse {α β : Type} (f : α → Counted β) : List α → Counted (List β)
  | [] => pure []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

@[simp] theorem erase_trials {α : Type} (t : Counted α) (J : ℕ) :
    (trials t J).erase = RandomTree.trials t.erase J := by
  induction J with
  | zero => rfl
  | succ J ih => simp [trials, RandomTree.trials, ih]

@[simp] theorem erase_traverse {α β : Type} (f : α → Counted β) (as : List α) :
    (traverse f as).erase = RandomTree.traverse (fun a => (f a).erase) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [traverse, RandomTree.traverse, ih]

theorem bounded_trials {α : Type} {t : Counted α} {N : ℕ} (h : t.Bounded N) (J : ℕ) :
    (trials t J).Bounded (J * N) := by
  induction J with
  | zero => exact bounded_pure _
  | succ J ih =>
    simpa [trials, Nat.succ_mul, Nat.add_comm] using
      bounded_bind (fun a => (trials t J).map (a :: ·)) h (fun a => bounded_map _ ih)

theorem bounded_traverse {α β : Type} (f : α → Counted β) {N : ℕ}
    (h : ∀ a, (f a).Bounded N) (as : List α) : (traverse f as).Bounded (as.length * N) := by
  induction as with
  | nil => exact bounded_pure _
  | cons a as ih =>
    simpa only [traverse, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm] using
      bounded_bind (fun b => (traverse f as).map (b :: ·)) (h a) (fun b => bounded_map _ ih)

end Counted
end MeanPayoff
end

end OAI
