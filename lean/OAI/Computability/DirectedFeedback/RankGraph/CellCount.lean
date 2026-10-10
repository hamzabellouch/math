import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.UnweightedIntegrated

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

theorem transition_membership (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (P : Set X)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E)
    {r : Fin k} {r' : Fin (2 * k)} (hr : Transition g cell r)
    (hr' : Transition g' (refineCell cell P) r')
    (a : S × X) (ha : refineCell cell P a = r') :
    decide (a.2 ∈ P) = g' (conditionedSet cell r P) := by
  classical
  have hdiv := transition_refines g g' hg' cell P hlift hr hr'
  have hav := congrArg Fin.val ha
  by_cases hp : a.2 ∈ P
  · have hex : r'.val = 2 * r.val := by
      simp only [refineCell, hp, ↓reduceIte, add_zero] at hav
      omega
    have hh := hr'.2
    rw [hex, refined_middle_boundary] at hh
    simpa only [hp, decide_true] using hh.symm
  · have hex : r'.val = 2 * r.val + 1 := by
      simp only [refineCell, hp, ↓reduceIte] at hav
      omega
    have hh := hr'.1
    rw [hex, refined_middle_boundary] at hh
    simpa only [hp, decide_false] using hh.symm

theorem starred_transition (g : Set S → Bool) (hg : Monotone g)
    (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r)
    (Z : Set S) (hstar : ∀ a, cell a = r → a ∈ Z) :
    g (boundary cell r.val \ Z) = false ∧
      g ((boundary cell r.val \ Z) ∪ Z) = true := by
  constructor
  · have hh := hg (Set.sdiff_subset : boundary cell r.val \ Z ⊆ boundary cell r.val)
    rw [hr.1] at hh
    exact le_antisymm hh (Bool.false_le _)
  · have hsub : boundary cell (r.val + 1) ⊆ (boundary cell r.val \ Z) ∪ Z := by
      intro a ha
      by_cases hz : a ∈ Z
      · exact Or.inr hz
      · apply Or.inl
        refine ⟨?_, hz⟩
        have hne : cell a ≠ r := fun hh => hz (hstar a hh)
        have hnev : (cell a).val ≠ r.val := fun hh => hne (Fin.ext hh)
        dsimp [boundary] at *
        omega
    have hh := hg hsub
    rw [hr.2] at hh
    exact le_antisymm (Bool.le_true _) hh

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {X : Type*}

def cellCount : ℕ → ℕ
  | 0 => 1
  | t+1 => 2 * cellCount t

theorem cellCount_eq (t : ℕ) : cellCount t = 2^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [cellCount, ih, pow_succ, mul_comm]

def prefixCell : (t : ℕ) → (ℕ → Set X) → (Fin t → X) → Fin (cellCount t)
  | 0, _, _ => ⟨0, by decide⟩
  | t+1, P, a => refineCell (prefixCell t P) (P t) (Fin.init a, a (Fin.last t))

def splitLast (t : ℕ) : (Fin (t+1) → X) ≃ ((Fin t → X) × X) where
  toFun a := (Fin.init a, a (Fin.last t))
  invFun a := Fin.snoc a.1 a.2
  left_inv a := by funext i; exact Fin.lastCases (by simp) (fun j => by simp [Fin.init]) i
  right_inv a := by rcases a with ⟨a,x⟩; simp

def stepFunction (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (E : Set ((Fin t → X) × X)) : Bool := g (t+1) (splitLast t ⁻¹' E)

theorem stepFunction_mono (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (hg : Monotone (g (t+1))) : Monotone (stepFunction g t) := by
  intro E F hEF
  exact hg (Set.preimage_mono hEF)

theorem stepFunction_lift (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E) (E : Set (Fin t → X)) :
    stepFunction g t (Prod.fst ⁻¹' E) = g t E := hlift E

theorem step_transition (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (P : ℕ → Set X) {r : Fin (cellCount (t+1))}
    (hr : Transition (g (t+1)) (prefixCell (t+1) P) r) :
    Transition (stepFunction g t) (refineCell (prefixCell t P) (P t)) r := hr

def conditionedValue (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ) (R : Set X) : Bool :=
  stepFunction g t (conditionedSet (prefixCell t P) (r t) R)

theorem selected_parent (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ)
    (hg : Monotone (g (t+1)))
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : Transition (g t) (prefixCell t P) (r t))
    (hr' : Transition (g (t+1)) (prefixCell (t+1) P) (r (t+1)))
    (a : Fin (t+1) → X) (ha : prefixCell (t+1) P a = r (t+1)) :
    prefixCell t P (Fin.init a) = r t := by
  have hd := transition_refines (g t) (stepFunction g t) (stepFunction_mono g t hg)
    (prefixCell t P) (P t) (stepFunction_lift g t hlift) hr (step_transition g t P hr')
  have hva := congrArg Fin.val ha
  apply Fin.ext
  dsimp only [prefixCell, refineCell] at hva
  split_ifs at hva <;> omega

theorem selected_last (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ)
    (hg : Monotone (g (t+1)))
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : Transition (g t) (prefixCell t P) (r t))
    (hr' : Transition (g (t+1)) (prefixCell (t+1) P) (r (t+1)))
    (a : Fin (t+1) → X) (ha : prefixCell (t+1) P a = r (t+1)) :
    decide (a (Fin.last t) ∈ P t) = conditionedValue g P r t (P t) :=
  transition_membership (g t) (stepFunction g t) (stepFunction_mono g t hg)
    (prefixCell t P) (P t) (stepFunction_lift g t hlift) hr (step_transition g t P hr')
    (Fin.init a, a (Fin.last t)) ha

theorem full_transition_membership (g : (t : ℕ) → Set (Fin t → X) → Bool)
    (P : ℕ → Set X) (r : (t : ℕ) → Fin (cellCount t)) (T : ℕ)
    (hg : ∀ t ≤ T, Monotone (g t))
    (hlift : ∀ t < T, ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : ∀ t ≤ T, Transition (g t) (prefixCell t P) (r t))
    (a : Fin T → X) (ha : prefixCell T P a = r T) :
    ∀ j : Fin T, decide (a j ∈ P j.val) = conditionedValue g P r j.val (P j.val) := by
  induction T with
  | zero => intro j; exact Fin.elim0 j
  | succ T ih =>
    have ha' := selected_parent g P r T (hg _ (by omega)) (hlift _ (by omega))
      (hr _ (by omega)) (hr _ (by omega)) a ha
    have hp := ih (fun t ht => hg t (by omega)) (fun t ht => hlift t (by omega))
      (fun t ht => hr t (by omega)) (Fin.init a) ha'
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact selected_last g P r T (hg _ (by omega)) (hlift _ (by omega))
        (hr _ (by omega)) (hr _ (by omega)) a ha
    · exact hp i

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k n : ℕ}

def orderedCell (cell : S → Fin k) (order : X ≃ Fin n) (a : S × X) : Fin (k*n) :=
  ⟨n*(cell a.1).val + (order a.2).val, by
    have h := Nat.mul_le_mul_left n (cell a.1).isLt
    have h' := (order a.2).isLt
    simp only [Nat.mul_succ] at h
    rw [Nat.mul_comm k n]
    omega⟩

theorem block_prefix {a b r q : ℕ} (hb : b < n) (hq : q ≤ n) :
    n*a+b < n*r+q ↔ a < r ∨ a = r ∧ b < q := by
  constructor
  · intro h
    by_cases har : a < r
    · exact Or.inl har
    · have har' : r ≤ a := by omega
      by_cases hra : r < a
      · have hh := Nat.mul_le_mul_left n hra
        simp only [Nat.mul_succ] at hh
        omega
      · have he : a = r := by omega
        subst a
        exact Or.inr ⟨rfl, by omega⟩
  · rintro (ha | ⟨rfl, hbq⟩)
    · have hh := Nat.mul_le_mul_left n ha
      simp only [Nat.mul_succ] at hh
      omega
    · omega

theorem ordered_boundary_sdiff (cell : S → Fin k) (order : X ≃ Fin n)
    (r : Fin k) (q : ℕ) (hq : q ≤ n) (j : X) :
    boundary (orderedCell cell order) (n*r.val+q) \ {a | a.2 = j} =
      {a | ((cell a.1).val < r.val ∧ a.2 ≠ j) ∨
        (cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q)} := by
  ext a
  simp only [Set.mem_sdiff, boundary, orderedCell, Set.mem_ofPred_eq,
    block_prefix (order a.2).isLt hq, Fin.ext_iff]
  tauto

theorem single_label_crossing (cell : S → Fin k) (order : X ≃ Fin n)
    (r : Fin k) (q : ℕ) (hq : q ≤ n) (j : X)
    (g : Set (S × X) → Bool) (hg : Monotone g)
    (h0 : g (conditionedSet cell r {x | x ≠ j ∧ (order x).val < q}) = false)
    (h1 : g (conditionedSet cell r ({x | x ≠ j ∧ (order x).val < q} ∪ {j})) = true) :
    let E := boundary (orderedCell cell order) (n*r.val+q) \ {a | a.2 = j}
    g E = false ∧ g (E ∪ {a | a.2 = j}) = true := by
  dsimp only
  rw [ordered_boundary_sdiff cell order r q hq j]
  constructor
  · have h := hg (show {a : S × X | (cell a.1).val < r.val ∧ a.2 ≠ j ∨
        cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q} ⊆
        conditionedSet cell r {x | x ≠ j ∧ (order x).val < q} by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl ha.1
        · exact Or.inr ⟨ha.1, ha.2⟩)
    rw [h0] at h
    exact le_antisymm h (by simp)
  · have h := hg (show conditionedSet cell r ({x | x ≠ j ∧ (order x).val < q} ∪ {j}) ⊆
        {a : S × X | (cell a.1).val < r.val ∧ a.2 ≠ j ∨
          cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q} ∪ {a | a.2 = j} by
        intro a ha
        by_cases haj : a.2 = j
        · exact Or.inr haj
        · left
          rcases ha with ha | ⟨ha,hb⟩
          · exact Or.inl ⟨ha,haj⟩
          · exact Or.inr ⟨ha, hb.resolve_right (by simpa using haj)⟩)
    rw [h1] at h
    exact le_antisymm (by simp) h

end DirectedFeedback.Prefix

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.SourceProbability
structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

theorem probability_iid_all (μ : FiniteDistribution Ω) (event : Ω → Bool) (n : Nat) :
    (μ.iid n).probability (fun x => decide (∀ i, event (x i) = true)) =
      μ.probability event ^ n := by
  classical
  unfold probability iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  by_cases h : ∀ i, event (x i) = true
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteDistribution
namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]
theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end FiniteDistribution
end DirectedFeedback.SourceProbability

namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J : Type*} [Fintype I] [Fintype J]

@[simp] theorem expectation_const (μ : FiniteDistribution I) (a : ℝ) :
    μ.expectation (fun _ => a) = a := by
  simp [expectation, ← Finset.sum_mul, μ.normalized]

theorem expectation_mono (μ : FiniteDistribution I) {f g : I → ℝ}
    (h : ∀ i, f i ≤ g i) : μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.nonnegative i))

theorem expectation_nonneg (μ : FiniteDistribution I) {f : I → ℝ}
    (h : ∀ i, 0 ≤ f i) : 0 ≤ μ.expectation f := by
  simpa using μ.expectation_mono h

@[simp] theorem expectation_add (μ : FiniteDistribution I) (f g : I → ℝ) :
    μ.expectation (fun i => f i + g i) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

@[simp] theorem expectation_mul_left (μ : FiniteDistribution I) (a : ℝ) (f : I → ℝ) :
    μ.expectation (fun i => a * f i) = a * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_sum (μ : FiniteDistribution I) (f : J → I → ℝ) :
    μ.expectation (fun i => ∑ j, f j i) = ∑ j, μ.expectation (f j) := by
  simp_rw [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_pushforward (μ : FiniteDistribution I) (f : I → J) (h : J → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem expectation_uniform_eq_expect [Nonempty I] (f : I → ℝ) :
    (uniform I).expectation f = 𝔼 i, f i := by
  rw [expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem table_pushforward {Q A B : Type*} [Fintype Q] [Fintype A] [Fintype B]
    [DecidableEq Q] (μ : Q → FiniteDistribution A) (f : Q → A → B) :
    (table μ).pushforward (fun x i => f i (x i)) =
      table (fun i => (μ i).pushforward (f i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [table, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · have hp : ∀ i, f i (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, f i (x i) = y i from fun hp => h (funext hp))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem table_uniform {Q A : Type*} [Fintype Q] [Fintype A]
    [DecidableEq Q] [Nonempty A] :
    table (fun _ : Q => uniform A) = uniform (Q → A) := by
  apply eq_of_weight_eq
  intro x
  simp [table, uniform, Nat.cast_pow, one_div]

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Probability
open DirectedFeedback.SourceProbability FiniteDistribution

def andBit {k : ℕ} (x : Fin k → Bool) : Bool := decide (∀ a, x a = true)

def andCoin (k : ℕ) : FiniteDistribution Bool :=
  (uniform (Fin k → Bool)).pushforward andBit

theorem andCoin_true (k : ℕ) : (andCoin k).weight true = (2 : ℝ)⁻¹ ^ k := by
  have heq (x : Fin k → Bool) : andBit x = true ↔ x = fun _ => true := by
    simp [andBit, funext_iff]
  simp [andCoin, pushforward, heq, uniform, Nat.cast_pow, inv_pow]

theorem andCoin_false (k : ℕ) : (andCoin k).weight false = 1 - (2 : ℝ)⁻¹ ^ k := by
  have h := (andCoin k).normalized
  rw [Fintype.sum_bool, andCoin_true] at h
  linarith

def dyadicLaw (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) :
    FiniteDistribution (I → Bool) := table (fun _ : I => andCoin k)

theorem dyadicLaw_weight (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) (x : I → Bool) :
    (dyadicLaw I k).weight x = ∏ i, if x i then (2 : ℝ)⁻¹ ^ k else 1 - (2 : ℝ)⁻¹ ^ k := by
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [andCoin_true, andCoin_false]

def blockAnd {I : Type*} {k : ℕ} (x : I → Fin k → Bool) : I → Bool := fun i => andBit (x i)

theorem blockAnd_expectation {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ)
    (f : (I → Bool) → ℝ) :
    (𝔼 x : I → Fin k → Bool, f (blockAnd x)) = (dyadicLaw I k).expectation f := by
  rw [← expectation_uniform_eq_expect]
  rw [← table_uniform, ← expectation_pushforward]
  unfold blockAnd
  rw [table_pushforward]
  rfl

end DirectedFeedback.Probability

noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
namespace DirectedFeedback.Pivotal

variable {I : Type*} [Fintype I] [DecidableEq I]

def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp0, sub_nonneg.mpr hp1]
  normalized := by simp

def law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDistribution (I → Bool) :=
  FiniteDistribution.table (fun _ => coin p hp0 hp1)

def relabel (σ : Equiv.Perm I) : (I → Bool) ≃ (I → Bool) where
  toFun b i := b (σ.symm i)
  invFun b i := b (σ i)
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

omit [Fintype I] [DecidableEq I] in
@[simp] theorem relabel_apply (σ : Equiv.Perm I) (b : I → Bool) (i : I) :
    relabel σ b i = b (σ.symm i) := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem relabel_trans (σ τ : Equiv.Perm I) (b : I → Bool) :
    relabel τ (relabel σ b) = relabel (σ.trans τ) b := rfl

theorem law_relabel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Equiv.Perm I) (f : (I → Bool) → ℝ) :
    (law p hp0 hp1).expectation (fun b => f (relabel σ b)) =
      (law p hp0 hp1).expectation f := by
  classical
  unfold FiniteDistribution.expectation
  symm
  apply Fintype.sum_equiv (relabel σ).symm
  intro b
  simp only [Equiv.apply_symm_apply]
  congr 1
  change (∏ i, (coin p hp0 hp1).weight (b i)) =
    ∏ i, (coin p hp0 hp1).weight (b (σ i))
  exact (Equiv.prod_comp σ (fun i => (coin p hp0 hp1).weight (b i))).symm

def chainPrefix (I : Type*) [Fintype I] (r : ℕ) : I → Bool :=
  fun i => decide ((Fintype.equivFin I i).val < r)

theorem sorted_chainPrefix (b : I → Bool) :
    ∃ σ : Equiv.Perm I, ∃ r ≤ Fintype.card I, b = relabel σ (chainPrefix I r) := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => b i = true)
  have hcard : s.card ≤ Fintype.card I := Finset.card_le_univ _
  let first : Finset I := (Finset.univ : Finset (Fin s.card)).image
    (fun i => (Fintype.equivFin I).symm (Fin.castLE hcard i))
  have hfirst : first.card = s.card := by
    dsimp [first]
    rw [Finset.card_image_of_injective _
      (show Function.Injective (fun i : Fin s.card => (Fintype.equivFin I).symm (Fin.castLE hcard i)) from (Fintype.equivFin I).symm.injective.comp (Fin.castLE_injective hcard))]
    simp
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq first s hfirst
  refine ⟨σ, s.card, hcard, ?_⟩
  ext i
  have hm : (σ.symm i ∈ first) ↔ (Fintype.equivFin I (σ.symm i)).val < s.card := by
    constructor
    · rintro hh
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hh
      rw [← hj]
      simp only [Equiv.apply_symm_apply]
      exact j.isLt
    · intro hi
      refine Finset.mem_image.mpr ⟨⟨_, hi⟩, Finset.mem_univ _, ?_⟩
      simp
  have hs : (i ∈ s) ↔ (σ.symm i ∈ first) := by
    rw [← hσ]
    simp
  apply Bool.eq_iff_iff.mpr
  simpa [s, relabel, chainPrefix] using hs.trans hm

def chainHit (event : (I → Bool) → Bool) (σ : Equiv.Perm I) : Bool :=
  decide (∃ r ≤ Fintype.card I, event (relabel σ (chainPrefix I r)) = true)

def chainBudget (event : (I → Bool) → Bool) : ℝ :=
  (FiniteDistribution.uniform (Equiv.Perm I)).probability (chainHit event)

@[simp] theorem uniform_comp_right (σ : Equiv.Perm I) (f : Equiv.Perm I → ℝ) :
    (FiniteDistribution.uniform (Equiv.Perm I)).expectation (fun τ => f (σ.trans τ)) =
      (FiniteDistribution.uniform (Equiv.Perm I)).expectation f := by
  classical
  rw [FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform]
  congr 1
  let e : Equiv.Perm I ≃ Equiv.Perm I :=
    { toFun := fun τ => σ.trans τ
      invFun := fun τ => σ.symm.trans τ
      left_inv := by intro τ; ext i; simp
      right_inv := by intro τ; ext i; simp }
  exact e.sum_comp f

omit [DecidableEq I] in
theorem probability_eq_expectation (μ : FiniteDistribution I) (event : I → Bool) :
    μ.probability event = μ.expectation (fun i => if event i then 1 else 0) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro i _
  cases h : event i <;> simp [h]

theorem bernoulli_le_chainBudget (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event : (I → Bool) → Bool) :
    (law p hp0 hp1).probability event ≤ chainBudget event := by
  classical
  let U := FiniteDistribution.uniform (Equiv.Perm I)
  let f (b : I → Bool) : ℝ := if event b then 1 else 0
  have hf (b : I → Bool) : U.expectation (fun σ => f (relabel σ b)) ≤ chainBudget event := by
    obtain ⟨τ, r, hr, rfl⟩ := sorted_chainPrefix b
    calc
      _ ≤ U.expectation (fun σ => if chainHit event (τ.trans σ) then 1 else 0) := by
        apply FiniteDistribution.expectation_mono
        intro σ
        dsimp [f]
        by_cases hh : event (relabel (τ.trans σ) (chainPrefix I r)) = true
        · have hc : chainHit event (τ.trans σ) = true := by
            exact decide_eq_true ⟨r, hr, hh⟩
          simp [hh, hc]
        · simp [hh]
          split_ifs <;> norm_num
      _ = chainBudget event := by
        rw [show U = FiniteDistribution.uniform (Equiv.Perm I) from rfl,
          uniform_comp_right τ (fun σ => if chainHit event σ then 1 else 0)]
        exact (probability_eq_expectation _ _).symm
  rw [probability_eq_expectation]
  calc
    _ = U.expectation (fun σ => (law p hp0 hp1).expectation (fun b => f (relabel σ b))) := by
      simp_rw [law_relabel]
      rw [FiniteDistribution.expectation_const]
    _ = (law p hp0 hp1).expectation (fun b => U.expectation (fun σ => f (relabel σ b))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ ≤ (law p hp0 hp1).expectation (fun _ => chainBudget event) :=
      FiniteDistribution.expectation_mono _ hf
    _ = chainBudget event := FiniteDistribution.expectation_const _ _

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def atom (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def insertBit (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) : I → Bool :=
  (Equiv.funSplitAt j Bool).symm (b, x)

omit [Fintype I] in
@[simp] theorem insertBit_self (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    insertBit j b x j = b := by simp [insertBit]

omit [Fintype I] in
@[simp] theorem insertBit_other (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool)
    (i : {i : I // i ≠ j}) : insertBit j b x i = x i := by
  simp [insertBit, i.property]

theorem sum_split (j : I) (H : (I → Bool) → ℝ) :
    (∑ x, H x) = ∑ x : {i : I // i ≠ j} → Bool,
      (H (insertBit j false x) + H (insertBit j true x)) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt j Bool).symm H]
  simp [Fintype.sum_prod_type, Finset.sum_add_distrib, insertBit, add_comm]

theorem prod_except (j : I) (g : I → ℝ) :
    (∏ i ∈ Finset.univ.erase j, g i) = ∏ i : {i : I // i ≠ j}, g i := by
  exact Finset.prod_subtype _ (by simp) g

def acceptance (f : (I → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ x, (∏ i, atom p (x i)) * bitValue (f x)

def discreteDerivative (f : (I → Bool) → Bool) (j : I)
    (x : {i : I // i ≠ j} → Bool) : ℝ :=
  bitValue (f (insertBit j true x)) - bitValue (f (insertBit j false x))

def totalInfluence (f : (I → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ j, ∑ x : {i : I // i ≠ j} → Bool,
    (∏ i, atom p (x i)) * discreteDerivative f j x

theorem acceptance_eq_probability (f : (I → Bool) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    acceptance f p = (law p hp0 hp1).probability f := by
  rw [probability_eq_expectation]
  rfl

theorem atom_hasDerivAt (b : Bool) (p : ℝ) :
    HasDerivAt (fun q => atom q b) (if b then 1 else -1) p := by
  cases b
  · convert (hasDerivAt_id p).const_sub (1 : ℝ) using 1 <;> rfl
  · exact hasDerivAt_id p

theorem russo (f : (I → Bool) → Bool) (p : ℝ) :
    HasDerivAt (acceptance f) (totalInfluence f p) p := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (I → Bool)))
    (fun x _ => (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset I))
      (fun i _ => atom_hasDerivAt (x i) p)).mul_const (bitValue (f x)))
  change HasDerivAt (acceptance f) _ p at h
  convert h using 1
  simp only [totalInfluence, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_split j]
  apply Finset.sum_congr rfl
  intro x _
  simp only [prod_except, insertBit_other, insertBit_self, Bool.false_eq_true,
    ↓reduceIte, discreteDerivative]
  ring

def pivotalEvent (f : (I → Bool) → Bool) (j : I)
    (x : {i : I // i ≠ j} → Bool) : Bool :=
  decide (f (insertBit j false x) = false ∧ f (insertBit j true x) = true)

def budget (f : (I → Bool) → Bool) : ℝ :=
  ∑ j, chainBudget (pivotalEvent f j)

omit [Fintype I] in
theorem discreteDerivative_eq_indicator (f : (I → Bool) → Bool) (hf : Monotone f)
    (j : I) (x : {i : I // i ≠ j} → Bool) :
    discreteDerivative f j x = bitValue (pivotalEvent f j x) := by
  have hm : f (insertBit j false x) ≤ f (insertBit j true x) := by
    apply hf
    intro i
    by_cases hi : i = j
    · subst i; simp
    · simp [insertBit, hi]
  cases h0 : f (insertBit j false x) <;> cases h1 : f (insertBit j true x) <;>
    simp_all [discreteDerivative, bitValue, pivotalEvent, Bool.le_iff_imp]

theorem totalInfluence_eq_sum_probability (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    totalInfluence f p = ∑ j, (law p hp0 hp1).probability (pivotalEvent f j) := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [discreteDerivative_eq_indicator f hf]
  rw [probability_eq_expectation]
  rfl

theorem influence_le_budget (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    totalInfluence f p ≤ budget f := by
  rw [totalInfluence_eq_sum_probability f hf p hp0 hp1]
  exact Finset.sum_le_sum (fun j _ => bernoulli_le_chainBudget p hp0 hp1 _)

theorem influence_nonneg (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ totalInfluence f p := by
  rw [totalInfluence_eq_sum_probability f hf p hp0 hp1]
  exact Finset.sum_nonneg (fun j _ => FiniteDistribution.probability_nonnegative _ _)

theorem acceptance_zero (f : (I → Bool) → Bool) (h0 : f (fun _ => false) = false) :
    acceptance f 0 = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = fun _ => false
  · simp [hx, h0, bitValue]
  · have hh : ∃ i, x i = true := by
      by_contra hn
      apply hx
      funext i
      cases hi : x i
      · rfl
      · exact False.elim (hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hh
    have hz : (∏ i, atom 0 (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [atom, hi])
    rw [hz, zero_mul]

end DirectedFeedback.Pivotal
end
end
end
end
end
end
end
end

end OAI
