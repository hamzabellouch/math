import OAI.Analysis.TreePotential.TestNorm

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section InwardScalarCalculus

/-- The two different inward pieces; their difference is the original relative
    potential. The value at the inherited head `c` determines their direction. -/
def inwardOne (c v : ℝ) : ℝ := if 0 ≤ c then min v 0 else max v 0
def inwardTwo (c v : ℝ) : ℝ := if 0 ≤ c then -max v 0 else -min v 0

@[simp] lemma inwardOne_zero (c : ℝ) : inwardOne c 0 = 0 := by simp [inwardOne]
@[simp] lemma inwardTwo_zero (c : ℝ) : inwardTwo c 0 = 0 := by simp [inwardTwo]

lemma inward_difference (c v : ℝ) : inwardOne c v - inwardTwo c v = v := by
  unfold inwardOne inwardTwo
  split_ifs <;> rw [sub_neg_eq_add]
  · simp
  · simp

lemma inwardOne_abs_le (c v : ℝ) : |inwardOne c v| ≤ |v| := by
  unfold inwardOne
  split_ifs
  · by_cases h : v ≤ 0
    · simp [min_eq_left h]
    · simp [min_eq_right (le_of_not_ge h)]
  · by_cases h : v ≤ 0
    · simp [max_eq_right h]
    · simp [max_eq_left (le_of_not_ge h)]

lemma inwardTwo_abs_le (c v : ℝ) : |inwardTwo c v| ≤ |v| := by
  unfold inwardTwo
  split_ifs <;> rw [abs_neg]
  · by_cases h : v ≤ 0
    · simp [max_eq_right h]
    · simp [max_eq_left (le_of_not_ge h)]
  · by_cases h : v ≤ 0
    · simp [min_eq_left h]
    · simp [min_eq_right (le_of_not_ge h)]

lemma inwardOne_sub_le (c v w : ℝ) :
    |inwardOne c v - inwardOne c w| ≤ |v - w| := by
  unfold inwardOne
  split_ifs
  · simpa only [Real.dist_eq, one_mul, id_eq, NNReal.coe_one] using
      ((LipschitzWith.id.min_const 0).dist_le_mul v w)
  · exact abs_max_sub_max_le_abs v w 0

lemma inwardTwo_sub_le (c v w : ℝ) :
    |inwardTwo c v - inwardTwo c w| ≤ |v - w| := by
  unfold inwardTwo
  split_ifs <;> rw [neg_sub_neg, abs_sub_comm]
  · exact abs_max_sub_max_le_abs v w 0
  · simpa only [Real.dist_eq, one_mul, id_eq, NNReal.coe_one] using
      ((LipschitzWith.id.min_const 0).dist_le_mul v w)

lemma inwardOne_same_sign {c d : ℝ} (h : (0 ≤ c ↔ 0 ≤ d)) (v : ℝ) :
    inwardOne c v = inwardOne d v := by simp only [inwardOne, h]
lemma inwardTwo_same_sign {c d : ℝ} (h : (0 ≤ c ↔ 0 ≤ d)) (v : ℝ) :
    inwardTwo c v = inwardTwo d v := by simp only [inwardTwo, h]

lemma opposite_sum_bound {c u a b l μ : ℝ} (hc : |c| ≤ a) (hu : |u| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ)
    (hopp : (0 ≤ c → u ≤ 0) ∧ (c < 0 → 0 ≤ u)) :
    |l * c + μ * u| ≤ max (l * a) (μ * b) := by
  rw [abs_le] at hc hu ⊢
  by_cases h : 0 ≤ c
  · have hu0 := hopp.1 h
    constructor
    · have ha := le_max_right (l * a) (μ * b)
      have hm := mul_le_mul_of_nonneg_left hu.1 hμ
      have hl := mul_nonneg hl h
      linarith
    · have ha := le_max_left (l * a) (μ * b)
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ hu0
      have hl := mul_le_mul_of_nonneg_left hc.2 hl
      linarith
  · have hc0 : c < 0 := lt_of_not_ge h
    have hu0 := hopp.2 hc0
    constructor
    · have ha := le_max_left (l * a) (μ * b)
      have hl := mul_le_mul_of_nonneg_left hc.1 hl
      have hm := mul_nonneg hμ hu0
      linarith
    · have ha := le_max_right (l * a) (μ * b)
      have hl := mul_nonpos_of_nonneg_of_nonpos hl hc0.le
      have hm := mul_le_mul_of_nonneg_left hu.2 hμ
      linarith

lemma inwardOne_combination_bound {c v a b l μ : ℝ} (hc : |c| ≤ a) (hv : |v| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) :
    |l * c + μ * inwardOne c v| ≤ max (l * a) (μ * b) := by
  apply opposite_sum_bound hc ((inwardOne_abs_le c v).trans hv) hl hμ
  constructor
  · intro h; simp only [inwardOne, ite_eq_left h]; exact min_le_right _ _
  · intro h; simp only [inwardOne, ite_eq_right (not_le.mpr h)]; exact le_max_right _ _

lemma inwardTwo_combination_bound {c v a b l μ : ℝ} (hc : |c| ≤ a) (hv : |v| ≤ b)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) :
    |l * c + μ * inwardTwo c v| ≤ max (l * a) (μ * b) := by
  apply opposite_sum_bound hc ((inwardTwo_abs_le c v).trans hv) hl hμ
  constructor
  · intro h; simp only [inwardTwo, ite_eq_left h]; exact neg_nonpos.mpr (le_max_right _ _)
  · intro h; simp only [inwardTwo, ite_eq_right (not_le.mpr h)]; exact neg_nonneg.mpr (min_le_right _ _)

lemma combined_quadratic_budget {J : Type*} (B : Finset J) (f u : J → ℝ)
    {a θ : ℝ} (hf : ∑ j ∈ B, f j ^ 2 ≤ 1) (hu : ∑ j ∈ B, u j ^ 2 ≤ 1)
    (hd : ∀ j ∈ B, f j = 0 ∨ u j = 0) (hbudget : a^2 + θ^2 ≤ 1) :
    ∑ j ∈ B, (a * f j + θ * u j)^2 ≤ 1 := by
  have he : (∑ j ∈ B, (a * f j + θ * u j)^2) =
      a^2 * (∑ j ∈ B, f j ^ 2) + θ^2 * (∑ j ∈ B, u j ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases hd j hj with h | h <;> simp [h, mul_pow]
  rw [he]
  nlinarith [sq_nonneg a, sq_nonneg θ,
    mul_le_mul_of_nonneg_left hf (sq_nonneg a), mul_le_mul_of_nonneg_left hu (sq_nonneg θ)]

end InwardScalarCalculus

namespace TreeCalculus
abbrev Node := List ℕ

/-- The root-inclusive scalar prefix sum. Rootless rows will set f([])=0. -/
def potential (f : Node → ℝ) (s : Node) : ℝ := (s.inits.map f).sum

@[simp] lemma potential_root (f : Node → ℝ) : potential f [] = f [] := by simp [potential]

@[simp] lemma potential_child (f : Node → ℝ) (s : Node) (j : ℕ) :
    potential f (s ++ [j]) = potential f s + f (s ++ [j]) := by
  simp [potential, List.inits_append]

lemma potential_add (f g : Node → ℝ) (s : Node) :
    potential (f + g) s = potential f s + potential g s := by
  exact List.sum_map_add

lemma potential_smul (a : ℝ) (f : Node → ℝ) (s : Node) :
    potential (a • f) s = a * potential f s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => simp only [potential_child, ih, Pi.smul_apply, smul_eq_mul]; ring

lemma potential_sub (f g : Node → ℝ) (s : Node) :
    potential (f - g) s = potential f s - potential g s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => simp only [potential_child, ih, Pi.sub_apply]; ring

/-- Discrete derivative with dummy parent value zero above the root. -/
def increments (P : Node → ℝ) (s : Node) : ℝ :=
  if s = [] then P [] else P s - P s.dropLast

@[simp] lemma increments_root (P : Node → ℝ) : increments P [] = P [] := by simp [increments]
@[simp] lemma increments_child (P : Node → ℝ) (s : Node) (j : ℕ) :
    increments P (s ++ [j]) = P (s ++ [j]) - P s := by simp [increments]

@[simp] theorem potential_increments (P : Node → ℝ) (s : Node) :
    potential (increments P) s = P s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih => rw [potential_child, ih, increments_child]; ring

@[simp] theorem increments_potential (f : Node → ℝ) (s : Node) :
    increments (potential f) s = f s := by
  cases s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j => simp

/-- Head sets are predecessor-closed. The empty set is allowed for block heads. -/
def Initial (D : Set Node) : Prop := ∀ ⦃s r⦄, s ∈ D → r <+: s → r ∈ D

def headPart (D : Set Node) (f : Node → ℝ) : Node → ℝ := D.indicator f

def tailPart (D : Set Node) (f : Node → ℝ) : Node → ℝ := Dᶜ.indicator f

lemma potential_tail_on_head {D : Set Node} (hD : Initial D) (g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : potential (tailPart D g) s = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  have h := hD hs ((List.mem_inits r s).mp hr)
  simp [tailPart, h]

lemma potential_head_child {D : Set Node} {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) {s : Node} {j : ℕ} (hs : s ++ [j] ∉ D) :
    potential h (s ++ [j]) = potential h s := by
  rw [potential_child, hsupp _ hs, add_zero]


lemma potential_head_on_head {D : Set Node} (hD : Initial D) (g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : potential (headPart D g) s = potential g s := by
  induction s using List.reverseRecOn with
  | nil => simp [headPart, hs]
  | append_singleton s j ih =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    rw [potential_child, potential_child, ih hp]
    simp [headPart, hs]

lemma head_potential_bound {D : Set Node} (hD : Initial D) {g : Node → ℝ}
    {b : ℝ} (hb : 0 ≤ b) (hg : ∀ s, |potential g s| ≤ b) :
    ∀ s, |potential (headPart D g) s| ≤ b := by
  intro s
  induction s using List.reverseRecOn with
  | nil =>
    by_cases h : [] ∈ D
    · simpa only [potential_head_on_head hD g h] using hg []
    · simpa [headPart, h] using hb
  | append_singleton s j ih =>
    by_cases h : s ++ [j] ∈ D
    · simpa only [potential_head_on_head hD g h] using hg (s ++ [j])
    · simpa [potential_child, headPart, h] using ih

lemma tail_eq_sub_head (D : Set Node) (g : Node → ℝ) : tailPart D g = g - headPart D g := by
  classical
  funext s
  by_cases hs : s ∈ D <;> simp [tailPart, headPart, hs]

lemma tail_potential_bound {D : Set Node} (hD : Initial D) {g : Node → ℝ}
    {b : ℝ} (hb : 0 ≤ b) (hg : ∀ s, |potential g s| ≤ b) (s : Node) :
    |potential (tailPart D g) s| ≤ 2 * b := by
  rw [tail_eq_sub_head, potential_sub]
  exact (abs_sub _ _).trans (by linarith [hg s, head_potential_bound hD hb hg s])

def inwardPotentialOne (D : Set Node) (h g : Node → ℝ) (s : Node) : ℝ :=
  inwardOne (potential h s) (potential (tailPart D g) s)
def inwardPotentialTwo (D : Set Node) (h g : Node → ℝ) (s : Node) : ℝ :=
  inwardTwo (potential h s) (potential (tailPart D g) s)
def inwardCoeffsOne (D : Set Node) (h g : Node → ℝ) := increments (inwardPotentialOne D h g)
def inwardCoeffsTwo (D : Set Node) (h g : Node → ℝ) := increments (inwardPotentialTwo D h g)

lemma inwardCoeffsOne_on_head {D : Set Node} (hD : Initial D) (h g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : inwardCoeffsOne D h g s = 0 := by
  cases s using List.reverseRecOn with
  | nil => simp [inwardCoeffsOne, inwardPotentialOne, potential_tail_on_head hD g hs]
  | append_singleton s j =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    simp [inwardCoeffsOne, inwardPotentialOne, potential_tail_on_head hD g hs,
      potential_tail_on_head hD g hp]

lemma inwardCoeffsTwo_on_head {D : Set Node} (hD : Initial D) (h g : Node → ℝ)
    {s : Node} (hs : s ∈ D) : inwardCoeffsTwo D h g s = 0 := by
  cases s using List.reverseRecOn with
  | nil => simp [inwardCoeffsTwo, inwardPotentialTwo, potential_tail_on_head hD g hs]
  | append_singleton s j =>
    have hp : s ∈ D := hD hs (List.prefix_append s [j])
    simp [inwardCoeffsTwo, inwardPotentialTwo, potential_tail_on_head hD g hs,
      potential_tail_on_head hD g hp]

lemma inwardCoeffs_difference (D : Set Node) (h g : Node → ℝ) (s : Node) :
    inwardCoeffsOne D h g s - inwardCoeffsTwo D h g s = tailPart D g s := by
  cases s using List.reverseRecOn with
  | nil => simpa [inwardCoeffsOne, inwardCoeffsTwo, inwardPotentialOne, inwardPotentialTwo] using
      inward_difference (h []) (tailPart D g [])
  | append_singleton s j =>
    unfold inwardCoeffsOne inwardCoeffsTwo
    rw [increments_child, increments_child]
    change (inwardOne _ _ - inwardOne _ _) - (inwardTwo _ _ - inwardTwo _ _) = _
    rw [show ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) by intros; ring]
    rw [inward_difference, inward_difference, potential_child]
    ring

lemma inwardCoeffsOne_abs_le {D : Set Node} (hD : Initial D) {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (g : Node → ℝ) (s : Node) :
    |inwardCoeffsOne D h g s| ≤ |g s| := by
  by_cases hd : s ∈ D
  · simp [inwardCoeffsOne_on_head hD h g hd]
  · cases s using List.reverseRecOn with
    | nil =>
      simpa [inwardCoeffsOne, inwardPotentialOne, tailPart, hd] using
        inwardOne_abs_le (h []) (g [])
    | append_singleton s j =>
      unfold inwardCoeffsOne
      rw [increments_child]
      unfold inwardPotentialOne
      rw [potential_head_child hsupp hd]
      have hh := inwardOne_sub_le (potential h s) (potential (tailPart D g) (s ++ [j]))
        (potential (tailPart D g) s)
      simpa [potential_child, tailPart, hd] using hh

lemma inwardCoeffsTwo_abs_le {D : Set Node} (hD : Initial D) {h : Node → ℝ}
    (hsupp : ∀ s, s ∉ D → h s = 0) (g : Node → ℝ) (s : Node) :
    |inwardCoeffsTwo D h g s| ≤ |g s| := by
  by_cases hd : s ∈ D
  · simp [inwardCoeffsTwo_on_head hD h g hd]
  · cases s using List.reverseRecOn with
    | nil =>
      simpa [inwardCoeffsTwo, inwardPotentialTwo, tailPart, hd] using
        inwardTwo_abs_le (h []) (g [])
    | append_singleton s j =>
      unfold inwardCoeffsTwo
      rw [increments_child]
      unfold inwardPotentialTwo
      rw [potential_head_child hsupp hd]
      have hh := inwardTwo_sub_le (potential h s) (potential (tailPart D g) (s ++ [j]))
        (potential (tailPart D g) s)
      simpa [potential_child, tailPart, hd] using hh

end TreeCalculus


end BoundedTreePotentials

end

end OAI
