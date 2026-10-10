import OAI.Analysis.TreePotential.Completion

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

inductive QuadraticKind where
  | sibling | antichain | global
  deriving DecidableEq

/-- Exactly the coordinate groups used by the three distinct quadratic budgets.
    Quantifying over finite subsets is equivalent to the countable-sum convention. -/
def QuadraticGroup : QuadraticKind → Finset Node → Prop
  | .sibling, B => ∃ r, ∀ s ∈ B, ∃ j, s = r ++ [j]
  | .antichain, B => (B : Set Node).Pairwise (fun s t => ¬s <+: t ∧ ¬t <+: s)
  | .global, _ => True

def QuadraticBudget (k : QuadraticKind) (f : Node → ℝ) : Prop :=
  ∀ B : Finset Node, QuadraticGroup k B → ∑ s ∈ B, f s ^ 2 ≤ 1

/-- The antichain model really requires finite support, and the global model
    really requires square summability. Neither condition is discarded. -/
def CoefficientSupport : QuadraticKind → (Node → ℝ) → Prop
  | .sibling, _ => True
  | .antichain, f => (Function.support f).Finite
  | .global, f => Memℓp f 2

structure IsTreeTest (includeRoot : Bool) (k : QuadraticKind) (f : Node → ℝ) : Prop where
  root_zero : includeRoot = false → f [] = 0
  potential_bound : ∀ s, |potential f s| ≤ 1
  quadratic_budget : QuadraticBudget k f
  coefficient_support : CoefficientSupport k f

lemma quadratic_singleton (k : QuadraticKind) {s : Node} (hs : s ≠ []) :
    QuadraticGroup k {s} := by
  cases k with
  | sibling =>
    cases s using List.reverseRecOn with
    | nil => exact (hs rfl).elim
    | append_singleton s j =>
      refine ⟨s, ?_⟩
      intro t ht
      have ht' : t = s ++ [j] := by simpa using ht
      exact ⟨j, ht'⟩
  | antichain => simp [QuadraticGroup]
  | global => trivial

lemma test_coefficient_bound {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) (s : Node) : |f s| ≤ 1 := by
  by_cases hs : s = []
  · subst s; simpa using hf.potential_bound []
  · have h := hf.quadratic_budget {s} (quadratic_singleton k hs)
    simpa only [Finset.sum_singleton, sq_le_one_iff_abs_le_one] using h

lemma quadraticBudget_dominate {k : QuadraticKind} {f g : Node → ℝ}
    (hf : QuadraticBudget k f) (h : ∀ s, |g s| ≤ |f s|) : QuadraticBudget k g := by
  intro B hB
  apply le_trans _ (hf B hB)
  apply Finset.sum_le_sum
  intro s hs
  exact (sq_le_sq).mpr (h s)

lemma coefficientSupport_dominate {k : QuadraticKind} {f g : Node → ℝ}
    (hf : CoefficientSupport k f) (h : ∀ s, |g s| ≤ |f s|) : CoefficientSupport k g := by
  cases k with
  | sibling => trivial
  | antichain =>
    apply hf.subset
    intro s hs
    change g s ≠ 0 at hs
    change f s ≠ 0
    intro hzero
    have hh := h s
    rw [hzero, abs_zero] at hh
    exact hs (abs_nonpos_iff.mp hh)
  | global =>
    exact (hf.norm).mono (by intro s; simpa only [Real.norm_eq_abs] using h s)

lemma coefficientSupport_combine {k : QuadraticKind} {f g : Node → ℝ}
    (hf : CoefficientSupport k f) (hg : CoefficientSupport k g) (a b : ℝ) :
    CoefficientSupport k (a • f + b • g) := by
  cases k with
  | sibling => trivial
  | antichain =>
    apply (hf.union hg).subset
    intro s hs
    change a * f s + b * g s ≠ 0 at hs
    change f s ≠ 0 ∨ g s ≠ 0
    by_contra hh
    push Not at hh
    exact hs (by rw [hh.1, hh.2]; ring)
  | global => exact (hf.const_smul a).add (hg.const_smul b)

lemma zero_isTreeTest (r : Bool) (k : QuadraticKind) : IsTreeTest r k 0 := by
  constructor
  · simp
  · intro s
    change |(s.inits.map fun _ => (0 : ℝ)).sum| ≤ 1
    simp
  · intro B hB; simp
  · cases k with
    | sibling => trivial
    | antichain => simp [CoefficientSupport]
    | global => exact zero_memℓp

lemma neg_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) : IsTreeTest r k (-f) := by
  constructor
  · intro hr; simpa using congrArg Neg.neg (hf.root_zero hr)
  · intro s
    have he : -f = (-1 : ℝ) • f := by ext s; simp
    rw [he, potential_smul, neg_one_mul, abs_neg]
    exact hf.potential_bound s
  · exact quadraticBudget_dominate hf.quadratic_budget (by intro s; simp)
  · exact coefficientSupport_dominate hf.coefficient_support (by intro s; simp)

lemma inits_nodup (s : Node) : s.inits.Nodup := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih =>
    have he : (s ++ [j]).inits = s.inits ++ [s ++ [j]] := by simp [List.inits_append]
    rw [he, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = s ++ [j] := by simpa using hb
    have hp := ((List.mem_inits a s).mp ha).length_le
    rw [hab, hb', List.length_append, List.length_singleton] at hp
    omega

lemma potential_single (i s : Node) :
    potential (Pi.single i (1 : ℝ)) s = if i <+: s then 1 else 0 := by
  rw [potential, ← List.sum_toFinset _ (inits_nodup s)]
  simp only [Pi.single_apply]
  by_cases h : i <+: s
  · have hm : i ∈ s.inits.toFinset := List.mem_toFinset.mpr ((List.mem_inits i s).mpr h)
    simp [hm, h]
  · have hm : i ∉ s.inits.toFinset := fun hm => h ((List.mem_inits i s).mp (List.mem_toFinset.mp hm))
    simp [hm, h]

lemma single_isTreeTest (r : Bool) (k : QuadraticKind) {i : Node}
    (hi : r = true ∨ i ≠ []) : IsTreeTest r k (Pi.single i (1 : ℝ)) := by
  constructor
  · intro hr
    have hn : [] ≠ i := by
      rcases hi with hi | hi
      · simp_all
      · exact Ne.symm hi
    exact Pi.single_eq_of_ne hn _
  · intro s
    rw [potential_single]
    split_ifs <;> norm_num
  · intro B hB
    simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    by_cases h : i ∈ B <;> simp [h]
  · cases k with
    | sibling => trivial
    | antichain =>
      change (Function.support (Pi.single i (1 : ℝ))).Finite
      exact (Set.finite_singleton i).subset (by intro s hs; simpa [Function.mem_support, Pi.single_apply] using hs)
    | global => exact (lp.single (E := fun _ : Node => ℝ) 2 i (1 : ℝ)).property

/-- Coordinate type: the root is omitted only in the rootless sibling row. -/
abbrev TreeCoordinate (includeRoot : Bool) := {s : Node // includeRoot = true ∨ s ≠ []}

def liftCoefficients (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) : ℝ :=
  if h : r = true ∨ s ≠ [] then f ⟨s, h⟩ else 0

@[simp] lemma liftCoefficients_coord {r : Bool} (f : TreeCoordinate r → ℝ) (s : TreeCoordinate r) :
    liftCoefficients r f s.val = f s := by simp [liftCoefficients, s.property]

@[simp] lemma liftCoefficients_zero (r : Bool) : liftCoefficients r 0 = 0 := by
  ext s; simp [liftCoefficients]

lemma liftCoefficients_neg (r : Bool) (f : TreeCoordinate r → ℝ) :
    liftCoefficients r (-f) = -liftCoefficients r f := by
  ext s
  by_cases h : r = true ∨ s ≠ [] <;> simp [liftCoefficients, h]

lemma liftCoefficients_single (r : Bool) (i : TreeCoordinate r) :
    liftCoefficients r (fun j => if j = i then (1 : ℝ) else 0) = Pi.single i.val 1 := by
  ext s
  by_cases h : r = true ∨ s ≠ []
  · simp [liftCoefficients, h, Pi.single_apply, Subtype.ext_iff]
  · have hn : s ≠ i.val := by rintro rfl; exact h i.property
    simp [liftCoefficients, h, hn]

attribute [-simp] liftCoefficients_coord liftCoefficients_zero potential_root potential_child in
/-- The four rows are specializations of this construction, not identified norms. -/
def treeTestFamily (r : Bool) (k : QuadraticKind) : TestFamily (TreeCoordinate r) := by
  have potential_root (f : Node → ℝ) : potential f [] = f [] := by simp [potential]
  have potential_child (f : Node → ℝ) (s : Node) (j : ℕ) :
      potential f (s ++ [j]) = potential f s + f (s ++ [j]) := by
    simp [potential, List.inits_append]
  have potential_smul (a : ℝ) (f : Node → ℝ) (s : Node) :
      potential (a • f) s = a * potential f s := by
    induction s using List.reverseRecOn with
    | nil => simp [potential_root]
    | append_singleton s j ih => simp only [potential_child, ih, Pi.smul_apply, smul_eq_mul]; ring
  have quadratic_singleton (k : QuadraticKind) {s : Node} (hs : s ≠ []) :
      QuadraticGroup k {s} := by
    cases k with
    | sibling =>
      cases s using List.reverseRecOn with
      | nil => exact (hs rfl).elim
      | append_singleton s j =>
        refine ⟨s, ?_⟩
        intro t ht
        have ht' : t = s ++ [j] := by simpa using ht
        exact ⟨j, ht'⟩
    | antichain => simp [QuadraticGroup]
    | global => trivial
  have test_coefficient_bound {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) (s : Node) : |f s| ≤ 1 := by
    by_cases hs : s = []
    · subst s; simpa only [potential_root] using hf.potential_bound []
    · have h := hf.quadratic_budget {s} (quadratic_singleton k hs)
      rw [Finset.sum_singleton] at h
      exact (sq_le_one_iff_abs_le_one (f s)).mp h
  have quadraticBudget_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : QuadraticBudget k f) (h : ∀ s, |g s| ≤ |f s|) : QuadraticBudget k g := by
    intro B hB
    apply le_trans _ (hf B hB)
    apply Finset.sum_le_sum
    intro s hs
    exact (sq_le_sq).mpr (h s)
  have coefficientSupport_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : CoefficientSupport k f) (h : ∀ s, |g s| ≤ |f s|) : CoefficientSupport k g := by
    cases k with
    | sibling => trivial
    | antichain =>
      apply hf.subset
      intro s hs
      change g s ≠ 0 at hs
      change f s ≠ 0
      intro hzero
      have hh := h s
      rw [hzero, abs_zero] at hh
      exact hs (abs_nonpos_iff.mp hh)
    | global =>
      exact (hf.norm).mono (by intro s; simpa only [Real.norm_eq_abs] using h s)
  have zero_isTreeTest (r : Bool) (k : QuadraticKind) : IsTreeTest r k 0 := by
    constructor
    · simp
    · intro s
      change |(s.inits.map fun _ => (0 : ℝ)).sum| ≤ 1
      simp
    · intro B hB; simp
    · cases k with
      | sibling => trivial
      | antichain => simp [CoefficientSupport]
      | global => exact zero_memℓp
  have neg_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) : IsTreeTest r k (-f) := by
    constructor
    · intro hr; simpa using congrArg Neg.neg (hf.root_zero hr)
    · intro s
      have he : -f = (-1 : ℝ) • f := by ext s; simp
      rw [he, potential_smul, neg_one_mul, abs_neg]
      exact hf.potential_bound s
    · exact quadraticBudget_dominate hf.quadratic_budget (by intro s; simp)
    · exact coefficientSupport_dominate hf.coefficient_support (by intro s; simp)
  have inits_nodup (s : Node) : s.inits.Nodup := by
    induction s using List.reverseRecOn with
    | nil => simp
    | append_singleton s j ih =>
      have he : (s ++ [j]).inits = s.inits ++ [s ++ [j]] := by simp [List.inits_append]
      rw [he, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = s ++ [j] := by simpa using hb
      have hp := ((List.mem_inits a s).mp ha).length_le
      rw [hab, hb', List.length_append, List.length_singleton] at hp
      exact Nat.not_succ_le_self _ hp
  have potential_single (i s : Node) :
      potential (Pi.single i (1 : ℝ)) s = if i <+: s then 1 else 0 := by
    rw [potential, ← List.sum_toFinset _ (inits_nodup s)]
    simp only [Pi.single_apply]
    by_cases h : i <+: s
    · have hm : i ∈ s.inits.toFinset := List.mem_toFinset.mpr ((List.mem_inits i s).mpr h)
      simp [hm, h]
    · have hm : i ∉ s.inits.toFinset := fun hm => h ((List.mem_inits i s).mp (List.mem_toFinset.mp hm))
      simp [hm, h]
  have single_isTreeTest (r : Bool) (k : QuadraticKind) {i : Node}
      (hi : r = true ∨ i ≠ []) : IsTreeTest r k (Pi.single i (1 : ℝ)) := by
    constructor
    · intro hr
      have hn : [] ≠ i := by
        rcases hi with hi | hi
        · simp_all
        · exact Ne.symm hi
      exact Pi.single_eq_of_ne hn _
    · intro s
      rw [potential_single]
      split_ifs <;> norm_num
    · intro B hB
      simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      by_cases h : i ∈ B <;> simp [h]
    · cases k with
      | sibling => trivial
      | antichain =>
        change (Function.support (Pi.single i (1 : ℝ))).Finite
        exact (Set.finite_singleton i).subset (by intro s hs; simpa [Function.mem_support, Pi.single_apply] using hs)
      | global => exact (lp.single (E := fun _ : Node => ℝ) 2 i (1 : ℝ)).property
  have liftCoefficients_coord {r : Bool} (f : TreeCoordinate r → ℝ) (s : TreeCoordinate r) :
      liftCoefficients r f s.val = f s := by simp [liftCoefficients, s.property]
  have liftCoefficients_zero (r : Bool) : liftCoefficients r 0 = 0 := by
    ext s; simp [liftCoefficients]
  have liftCoefficients_neg (r : Bool) (f : TreeCoordinate r → ℝ) :
      liftCoefficients r (-f) = -liftCoefficients r f := by
    ext s
    by_cases h : r = true ∨ s ≠ [] <;> simp [liftCoefficients, h]
  exact {
    carrier := {f | IsTreeTest r k (liftCoefficients r f)}
    zero_mem := by
      change IsTreeTest r k (liftCoefficients r 0)
      rw [liftCoefficients_zero]
      exact zero_isTreeTest r k
    neg_mem := by
      intro f hf
      change IsTreeTest r k (liftCoefficients r (-f))
      rw [liftCoefficients_neg]
      exact neg_isTreeTest hf
    coeff_bound := by
      intro f hf i
      simpa only [liftCoefficients_coord] using test_coefficient_bound hf i.val
    singleton_mem := by
      rintro ⟨i, hi⟩
      change IsTreeTest r k (liftCoefficients r _)
      convert single_isTreeTest r k hi using 1
      ext s
      by_cases h : r = true ∨ s ≠ []
      · simp [liftCoefficients, h, Pi.single_apply, Subtype.mk.injEq]
      · have hn : s ≠ i := by rintro rfl; exact h hi
        simp [liftCoefficients, h, hn] }

abbrev rootlessSiblingTests := treeTestFamily false .sibling
abbrev rootedSiblingTests := treeTestFamily true .sibling
abbrev antichainTests := treeTestFamily true .antichain
abbrev globalTests := treeTestFamily true .global

abbrev RootlessSiblingSpace := TestCompletion rootlessSiblingTests
abbrev RootedSiblingSpace := TestCompletion rootedSiblingTests
abbrev AntichainSpace := TestCompletion antichainTests
abbrev GlobalTestSpace := TestCompletion globalTests


lemma headPart_abs_le (D : Set Node) (f : Node → ℝ) (s : Node) : |headPart D f s| ≤ |f s| := by
  by_cases h : s ∈ D <;> simp [headPart, h]

lemma head_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) {D : Set Node} (hD : Initial D) :
    IsTreeTest r k (headPart D f) := by
  constructor
  · intro hr; simp [headPart, hf.root_zero hr]
  · exact head_potential_bound hD zero_le_one hf.potential_bound
  · exact quadraticBudget_dominate hf.quadratic_budget (headPart_abs_le D f)
  · exact coefficientSupport_dominate hf.coefficient_support (headPart_abs_le D f)

lemma lift_restrict {r : Bool} (f : Node → ℝ) (hroot : r = false → f [] = 0) :
    liftCoefficients r (fun s : TreeCoordinate r => f s.val) = f := by
  ext s
  by_cases h : r = true ∨ s ≠ []
  · simp [liftCoefficients, h]
  · have hs : s = [] := by tauto
    subst s
    have hr : r = false := by cases r <;> simp_all
    simp [liftCoefficients, hroot hr]

def asTreeTest {r : Bool} {k : QuadraticKind} (f : Node → ℝ) (hf : IsTreeTest r k f) :
    treeTestFamily r k :=
  ⟨(fun s => f s.val), by change IsTreeTest r k (liftCoefficients r _); rw [lift_restrict f hf.root_zero]; exact hf⟩

lemma inwardOne_isTreeTest {r : Bool} {k : QuadraticKind} {h g : Node → ℝ}
    (hh : IsTreeTest r k h) (hg : IsTreeTest r k g) {D : Set Node} (hD : Initial D)
    (hroot : [] ∈ D) (hsupp : ∀ s, s ∉ D → h s = 0)
    {a θ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1) :
    IsTreeTest r k (a • h + θ • inwardCoeffsOne D h g) := by
  constructor
  · intro hr
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh.root_zero hr,
      inwardCoeffsOne_on_head hD h g hroot, mul_zero, add_zero]
  · intro s
    rw [potential_add, potential_smul, potential_smul]
    change |a * potential h s + θ * potential (increments (inwardPotentialOne D h g)) s| ≤ 1
    rw [potential_increments]
    exact (inwardOne_combination_bound (hh.potential_bound s)
      (tail_potential_bound hD zero_le_one hg.potential_bound s) ha hθ).trans
      (by apply max_le <;> nlinarith)
  · intro B hB
    apply combined_quadratic_budget
    · exact hh.quadratic_budget B hB
    · exact quadraticBudget_dominate hg.quadratic_budget (inwardCoeffsOne_abs_le hD hsupp g) B hB
    · intro s hs
      by_cases hd : s ∈ D
      · exact Or.inr (inwardCoeffsOne_on_head hD h g hd)
      · exact Or.inl (hsupp s hd)
    · exact hsquare
  · exact coefficientSupport_combine hh.coefficient_support
      (coefficientSupport_dominate hg.coefficient_support (inwardCoeffsOne_abs_le hD hsupp g)) a θ

lemma inwardTwo_isTreeTest {r : Bool} {k : QuadraticKind} {h g : Node → ℝ}
    (hh : IsTreeTest r k h) (hg : IsTreeTest r k g) {D : Set Node} (hD : Initial D)
    (hroot : [] ∈ D) (hsupp : ∀ s, s ∉ D → h s = 0)
    {a θ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1) :
    IsTreeTest r k (a • h + θ • inwardCoeffsTwo D h g) := by
  constructor
  · intro hr
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh.root_zero hr,
      inwardCoeffsTwo_on_head hD h g hroot, mul_zero, add_zero]
  · intro s
    rw [potential_add, potential_smul, potential_smul]
    change |a * potential h s + θ * potential (increments (inwardPotentialTwo D h g)) s| ≤ 1
    rw [potential_increments]
    exact (inwardTwo_combination_bound (hh.potential_bound s)
      (tail_potential_bound hD zero_le_one hg.potential_bound s) ha hθ).trans
      (by apply max_le <;> nlinarith)
  · intro B hB
    apply combined_quadratic_budget
    · exact hh.quadratic_budget B hB
    · exact quadraticBudget_dominate hg.quadratic_budget (inwardCoeffsTwo_abs_le hD hsupp g) B hB
    · intro s hs
      by_cases hd : s ∈ D
      · exact Or.inr (inwardCoeffsTwo_on_head hD h g hd)
      · exact Or.inl (hsupp s hd)
    · exact hsquare
  · exact coefficientSupport_combine hh.coefficient_support
      (coefficientSupport_dominate hg.coefficient_support (inwardCoeffsTwo_abs_le hD hsupp g)) a θ



def treePairing {r : Bool} (f : Node → ℝ) : (TreeCoordinate r →₀ ℝ) →ₗ[ℝ] ℝ :=
  finitePairing (fun s => f s.val)

@[simp] lemma treePairing_lift {r : Bool} (f : TreeCoordinate r → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (liftCoefficients r f) x = finitePairing f x := by
  have he : (fun s : TreeCoordinate r => liftCoefficients r f s.val) = f :=
    funext (liftCoefficients_coord f)
  change finitePairing (fun s => liftCoefficients r f s.val) x = finitePairing f x
  rw [he]

@[simp] lemma treePairing_add_coeff {r : Bool} (f g : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (f + g) x = treePairing f x + treePairing g x := by
  simp only [treePairing, finitePairing_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] lemma treePairing_sub_coeff {r : Bool} (f g : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (f - g) x = treePairing f x - treePairing g x := by
  simp only [treePairing, finitePairing_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

@[simp] lemma treePairing_smul_coeff {r : Bool} (a : ℝ) (f : Node → ℝ) (x : TreeCoordinate r →₀ ℝ) :
    treePairing (a • f) x = a * treePairing f x := by
  simp only [treePairing, finitePairing_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma treePairing_congr {r : Bool} {f g : Node → ℝ} (x : TreeCoordinate r →₀ ℝ)
    (h : ∀ s, x s ≠ 0 → f s.val = g s.val) : treePairing f x = treePairing g x := by
  change (∑ s ∈ x.support, x s * f s.val) = (∑ s ∈ x.support, x s * g s.val)
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finsupp.mem_support_iff.mp hs)]

lemma treePairing_zero_of_disjoint {r : Bool} {f : Node → ℝ} (x : TreeCoordinate r →₀ ℝ)
    (h : ∀ s, x s ≠ 0 → f s.val = 0) : treePairing f x = 0 := by
  change (∑ s ∈ x.support, x s * f s.val) = 0
  apply Finset.sum_eq_zero
  intro s hs
  rw [h s (Finsupp.mem_support_iff.mp hs), mul_zero]

lemma treePairing_le_norm {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
    (hf : IsTreeTest r k f) (x : TreeCoordinate r →₀ ℝ) :
    treePairing f x ≤ testNorm (treeTestFamily r k) x :=
  (le_abs_self _).trans (finitePairing_le_testNorm _ (asTreeTest f hf) x)

lemma treePairing_head_eq {r : Bool} (D : Set Node) (f : Node → ℝ) (x : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) : treePairing (headPart D f) x = treePairing f x := by
  apply treePairing_congr
  intro s hs
  exact Set.indicator_of_mem (hx s hs) f

lemma treePairing_tail_eq {r : Bool} (D : Set Node) (f : Node → ℝ) (y : TreeCoordinate r →₀ ℝ)
    (hy : ∀ s, s.val ∈ D → y s = 0) : treePairing (tailPart D f) y = treePairing f y := by
  apply treePairing_congr
  intro s hs
  have hd : s.val ∉ D := fun hd => hs (hy s hd)
  exact Set.indicator_of_mem hd f

lemma inward_pairing_identity {r : Bool} {D : Set Node} (hD : Initial D) {h g : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    (a θ t : ℝ) :
    treePairing (a • h + θ • inwardCoeffsOne D h g) (x + t • y) +
      treePairing (a • h + θ • inwardCoeffsTwo D h g) (x - t • y) =
      2 * a * treePairing h x + t * θ * treePairing g y := by
  have hhy : treePairing h y = 0 := treePairing_zero_of_disjoint y (by
    intro s hs
    exact hsupp s.val (fun hd => hs (hy s hd)))
  have hu : treePairing (inwardCoeffsOne D h g) x = 0 :=
    treePairing_zero_of_disjoint x (fun s hs => inwardCoeffsOne_on_head hD h g (hx s hs))
  have hv : treePairing (inwardCoeffsTwo D h g) x = 0 :=
    treePairing_zero_of_disjoint x (fun s hs => inwardCoeffsTwo_on_head hD h g (hx s hs))
  have huv : treePairing (inwardCoeffsOne D h g) y - treePairing (inwardCoeffsTwo D h g) y =
      treePairing g y := by
    rw [← treePairing_sub_coeff]
    have he : inwardCoeffsOne D h g - inwardCoeffsTwo D h g = tailPart D g :=
      funext (inwardCoeffs_difference D h g)
    rw [he, treePairing_tail_eq D g y hy]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, treePairing_add_coeff, treePairing_smul_coeff,
    hhy, hu, hv]
  rw [← huv]
  ring

/-- The finite-array form of the paired inward inequality. The proof takes
    suprema instead of presuming an attained infinite-dimensional polar norm. -/
theorem paired_finite_test_bound {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (hsquare : a^2 + θ^2 ≤ 1)
    (f g : treeTestFamily r k) :
    a * finitePairing f.val x + (t * θ / 2) * finitePairing g.val y ≤
      (testNorm (treeTestFamily r k) (x + t • y) + testNorm (treeTestFamily r k) (x - t • y)) / 2 := by
  let h := headPart D (liftCoefficients r f.val)
  let g' := liftCoefficients r g.val
  have hh : IsTreeTest r k h := head_isTreeTest f.property hD
  have hg : IsTreeTest r k g' := g.property
  have hsupp : ∀ s, s ∉ D → h s = 0 := by intro s hs; exact Set.indicator_of_notMem hs _
  have hplus := treePairing_le_norm (inwardOne_isTreeTest hh hg hD hroot hsupp ha ha1 hθ hθ1 hsquare) (x + t • y)
  have hminus := treePairing_le_norm (inwardTwo_isTreeTest hh hg hD hroot hsupp ha ha1 hθ hθ1 hsquare) (x - t • y)
  have he := inward_pairing_identity (g := g') hD hsupp x y hx hy a θ t
  have hfx : treePairing h x = finitePairing f.val x := by
    change treePairing (headPart D (liftCoefficients r f.val)) x = _
    rw [treePairing_head_eq D _ x hx, treePairing_lift]
  have hgy : treePairing g' y = finitePairing g.val y := treePairing_lift g.val y
  rw [hfx, hgy] at he
  linarith

end TreeCalculus

lemma testNorm_weighted_sup {I : Type*} (K : TestFamily I) (x y : I →₀ ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ f g : K, a * finitePairing f.val x + b * finitePairing g.val y ≤ c) :
    a * testNorm K x + b * testNorm K y ≤ c := by
  have hba : BddAbove (range fun f : K => a * finitePairing f.val x) :=
    ⟨a * testNorm K x, by
      rintro _ ⟨f, rfl⟩
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (finitePairing_le_testNorm K f x)) ha⟩
  have hbb : BddAbove (range fun f : K => b * finitePairing f.val y) :=
    ⟨b * testNorm K y, by
      rintro _ ⟨f, rfl⟩
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (finitePairing_le_testNorm K f y)) hb⟩
  rw [testNorm_signed_sup K x, testNorm_signed_sup K y,
    Real.mul_iSup_of_nonneg ha, Real.mul_iSup_of_nonneg hb, ciSup_add hba]
  apply ciSup_le
  intro f
  rw [add_ciSup hbb]
  exact ciSup_le (h f)

namespace TreeCalculus

theorem paired_finite_inequality {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TreeCoordinate r →₀ ℝ)
    (hx : ∀ s, x s ≠ 0 → s.val ∈ D) (hy : ∀ s, s.val ∈ D → y s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * testNorm (treeTestFamily r k) x + (t * θ / 2) * testNorm (treeTestFamily r k) y ≤
      (testNorm (treeTestFamily r k) (x + t • y) + testNorm (treeTestFamily r k) (x - t • y)) / 2 := by
  apply testNorm_weighted_sup _ x y ha (by positivity)
  exact paired_finite_test_bound hD hroot x y hx hy ha ha1 hθ hθ1 hsquare

end TreeCalculus


end BoundedTreePotentials

end

end OAI
