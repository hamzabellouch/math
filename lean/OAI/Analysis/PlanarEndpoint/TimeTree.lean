import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open Finset Set
namespace PlanarEndpoint.TimeTree

theorem convexity_deficit {a b α : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hα : 1 < α) :
    ((2 : ℝ) ^ α - 2) * b ^ α ≤ (a + b) ^ α - a ^ α - b ^ α := by
  let f : ℝ → ℝ := fun u => (u + b) ^ α - u ^ α
  have hd (u : ℝ) : HasDerivAt f
      (α * (u + b) ^ (α - 1) - α * u ^ (α - 1)) u := by
    dsimp [f]
    convert! (((hasDerivAt_id u).add_const b).rpow_const (Or.inr hα.le)).sub
        (Real.hasDerivAt_rpow_const (Or.inr hα.le)) using 1
    simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn
    · exact (show Differentiable ℝ f from fun u => (hd u).differentiableAt).differentiableOn
    · intro u hu
      rw [(hd u).deriv]
      have hu' : 0 ≤ u := (interior_subset hu : u ∈ Ici (0 : ℝ))
      apply sub_nonneg.mpr
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hu' (le_add_of_nonneg_right hb) (by linarith))
        (by linarith)
  have h := hm hb (hb.trans hba) hba
  dsimp [f] at h
  have heq : (b + b) ^ α = (2 : ℝ) ^ α * b ^ α := by
    rw [← two_mul, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb]
  rw [heq] at h
  nlinarith

structure MassTree where
  mass : List Bool → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  split : ∀ s, mass s = mass (false :: s) + mass (true :: s)

namespace MassTree
variable (m : MassTree)

def lighterMass (s : List Bool) : ℝ := min (m.mass (false :: s)) (m.mass (true :: s))

def deficit (α : ℝ) (s : List Bool) : ℝ :=
  m.mass s ^ α - m.mass (false :: s) ^ α - m.mass (true :: s) ^ α

lemma lighterMass_nonneg (s : List Bool) : 0 ≤ m.lighterMass s :=
  le_min (m.nonneg _) (m.nonneg _)

lemma deficit_nonneg {α : ℝ} (hα : 1 ≤ α) (s : List Bool) : 0 ≤ m.deficit α s := by
  dsimp [deficit]
  rw [m.split s]
  have := Real.add_rpow_le_rpow_add (m.nonneg (false :: s)) (m.nonneg (true :: s)) hα
  linarith

lemma lighterMass_bound {α : ℝ} (hα : 1 < α) (s : List Bool) :
    ((2 : ℝ) ^ α - 2) * m.lighterMass s ^ α ≤ m.deficit α s := by
  dsimp [lighterMass, deficit]
  rw [m.split s]
  rcases le_total (m.mass (false :: s)) (m.mass (true :: s)) with h | h
  · rw [min_eq_left h]
    have he := convexity_deficit (m.nonneg (false :: s)) h hα
    rw [add_comm (m.mass (true :: s)) (m.mass (false :: s))] at he
    linarith
  · rw [min_eq_right h]
    exact convexity_deficit (m.nonneg (true :: s)) h hα

end MassTree

def level : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (level n).image (List.cons false) ∪ (level n).image (List.cons true)

@[simp] lemma mem_level (s : List Bool) (n : ℕ) : s ∈ level n ↔ s.length = n := by
  induction n generalizing s with
  | zero => simp [level]
  | succ n ih =>
    cases s with
    | nil => simp [level]
    | cons b s =>
      cases b <;> simp [level, ih]

lemma level_children_disjoint (n : ℕ) :
    Disjoint ((level n).image (List.cons false)) ((level n).image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro s h₀ h₁
  obtain ⟨s₀, _, rfl⟩ := Finset.mem_image.mp h₀
  obtain ⟨s₁, _, h⟩ := Finset.mem_image.mp h₁
  cases h

lemma sum_level_succ (F : List Bool → ℝ) (n : ℕ) :
    ∑ s ∈ level (n + 1), F s =
      ∑ s ∈ level n, (F (false :: s) + F (true :: s)) := by
  rw [level, Finset.sum_union (level_children_disjoint n), Finset.sum_add_distrib]
  congr 1 <;> exact Finset.sum_image (fun a _ b _ h => List.cons.inj h |>.2)

def internal (n : ℕ) : Finset (List Bool) :=
  (Finset.range n).biUnion level

@[simp] lemma mem_internal (s : List Bool) (n : ℕ) :
    s ∈ internal n ↔ s.length < n := by
  simp [internal]

lemma internal_succ (n : ℕ) : internal (n + 1) = internal n ∪ level n := by
  ext s
  simp only [mem_internal, Finset.mem_union, mem_level]
  omega

lemma internal_level_disjoint (n : ℕ) : Disjoint (internal n) (level n) := by
  apply Finset.disjoint_left.mpr
  intro s hi hl
  simp only [mem_internal, mem_level] at hi hl
  omega

lemma sum_internal (F : List Bool → ℝ) (n : ℕ) :
    ∑ s ∈ internal n, F s = ∑ j ∈ Finset.range n, ∑ s ∈ level j, F s := by
  induction n with
  | zero => simp [internal]
  | succ n ih =>
    rw [internal_succ, Finset.sum_union (internal_level_disjoint n), ih,
      Finset.sum_range_succ]

namespace MassTree
variable (m : MassTree)

def potential (α : ℝ) (n : ℕ) : ℝ := ∑ s ∈ level n, m.mass s ^ α

lemma potential_nonneg (α : ℝ) (n : ℕ) : 0 ≤ m.potential α n :=
  Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (m.nonneg s) α)

lemma sum_deficit_level (α : ℝ) (n : ℕ) :
    ∑ s ∈ level n, m.deficit α s = m.potential α n - m.potential α (n + 1) := by
  dsimp [deficit, potential]
  rw [sum_level_succ]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

lemma deficits_telescope (α : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ s ∈ level k, m.deficit α s =
      m.mass [] ^ α - m.potential α n := by
  induction n with
  | zero => simp [potential, level]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, m.sum_deficit_level]
    ring

lemma sum_deficit_internal (α : ℝ) (n : ℕ) :
    ∑ s ∈ internal n, m.deficit α s = m.mass [] ^ α - m.potential α n := by
  induction n with
  | zero => simp [internal, potential, level]
  | succ n ih =>
    rw [internal_succ, Finset.sum_union (internal_level_disjoint n), ih,
      m.sum_deficit_level]
    ring

lemma potential_le_root {α : ℝ} (hα : 1 ≤ α) (n : ℕ) :
    m.potential α n ≤ m.mass [] ^ α := by
  have h : 0 ≤ ∑ s ∈ internal n, m.deficit α s :=
    Finset.sum_nonneg (fun s _ => m.deficit_nonneg hα s)
  rw [m.sum_deficit_internal] at h
  linarith

lemma deficit_sum_le_root {α : ℝ} (hα : 1 ≤ α) (S : Finset (List Bool)) :
    ∑ s ∈ S, m.deficit α s ≤ m.mass [] ^ α := by
  let n := S.sup List.length + 1
  have hs : S ⊆ internal n := by
    intro s hs
    apply (mem_internal s n).mpr
    exact Nat.lt_succ_of_le (Finset.le_sup hs)
  calc
    _ ≤ ∑ s ∈ internal n, m.deficit α s :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun s _ _ => m.deficit_nonneg hα s)
    _ = m.mass [] ^ α - m.potential α n := m.sum_deficit_internal α n
    _ ≤ m.mass [] ^ α := sub_le_self _ (m.potential_nonneg α n)

lemma convexity_constant_pos {α : ℝ} (hα : 1 < α) : 0 < (2 : ℝ) ^ α - 2 := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hα
  simpa using sub_pos.mpr h

lemma lighterMass_sum_le {α : ℝ} (hα : 1 < α) (S : Finset (List Bool)) :
    ∑ s ∈ S, m.lighterMass s ^ α ≤ m.mass [] ^ α / ((2 : ℝ) ^ α - 2) := by
  apply (le_div_iff₀ (convexity_constant_pos hα)).mpr
  rw [mul_comm, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun s _ => m.lighterMass_bound hα s)).trans
    (m.deficit_sum_le_root hα.le S)

lemma lighterMass_summable {α : ℝ} (hα : 1 < α) :
    Summable (fun s : List Bool => m.lighterMass s ^ α) :=
  summable_of_sum_le (fun s => Real.rpow_nonneg (m.lighterMass_nonneg s) α)
    (m.lighterMass_sum_le hα)

lemma lighterMass_tsum_le {α : ℝ} (hα : 1 < α) :
    ∑' s : List Bool, m.lighterMass s ^ α ≤ m.mass [] ^ α / ((2 : ℝ) ^ α - 2) :=
  Real.tsum_le_of_sum_le (fun s => Real.rpow_nonneg (m.lighterMass_nonneg s) α)
    (m.lighterMass_sum_le hα)

def heavy (s : List Bool) : List Bool :=
  if m.mass (false :: s) < m.mass (true :: s) then true :: s else false :: s

def light (s : List Bool) : List Bool :=
  if m.mass (false :: s) < m.mass (true :: s) then false :: s else true :: s

lemma light_mass (s : List Bool) : m.mass (m.light s) = m.lighterMass s := by
  dsimp [light, lighterMass]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (le_of_not_gt h)).symm

lemma heavy_injective : Function.Injective m.heavy := by
  intro s t h
  have ht := congrArg List.tail h
  simpa only [heavy, List.tail_cons, apply_ite, ite_self] using ht

def heavyPath (s : List Bool) (k : ℕ) : List Bool := (m.heavy)^[k] s

lemma heavyPath_injective (k : ℕ) : Function.Injective (fun s => m.heavyPath s k) :=
  m.heavy_injective.iterate k

lemma heavyPath_length (s : List Bool) (k : ℕ) : (m.heavyPath s k).length = s.length + k := by
  change ((m.heavy)^[k] s).length = _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [heavy]
    split_ifs <;> simp only [List.length_cons, ih] <;> omega

lemma offspring_sum_le {α : ℝ} (hα : 1 < α) (S : Finset (List Bool)) (k : ℕ) :
    ∑ s ∈ S, m.mass (m.light (m.heavyPath s k)) ^ α ≤
      m.mass [] ^ α / ((2 : ℝ) ^ α - 2) := by
  simpa only [m.light_mass, Finset.sum_image,
    m.heavyPath_injective k |>.injOn] using
    m.lighterMass_sum_le hα (S.image (fun s => m.heavyPath s k))

def offspringPenalty (α q : ℝ) (s : List Bool) : ℝ :=
  ∑ k ∈ Finset.range s.length, q ^ (k + 1) * m.mass (m.light (m.heavyPath s k)) ^ α

lemma offspringPenalty_nonneg (α : ℝ) {q : ℝ} (hq : 0 ≤ q) (s : List Bool) :
    0 ≤ m.offspringPenalty α q s :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (pow_nonneg hq _) (Real.rpow_nonneg (m.nonneg _) _))

lemma offspringPenalty_sum_le {α q : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (n : ℕ) :
    ∑ s ∈ internal n, m.offspringPenalty α q s ≤
      (m.mass [] ^ α / ((2 : ℝ) ^ α - 2)) * ∑ k ∈ Finset.range n, q ^ (k + 1) := by
  calc
    _ ≤ ∑ s ∈ internal n, ∑ k ∈ Finset.range n,
        q ^ (k + 1) * m.mass (m.light (m.heavyPath s k)) ^ α := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono ((mem_internal s n).mp hs).le
      · intro k _ _
        exact mul_nonneg (pow_nonneg hq _) (Real.rpow_nonneg (m.nonneg _) _)
    _ = ∑ k ∈ Finset.range n, q ^ (k + 1) *
        ∑ s ∈ internal n, m.mass (m.light (m.heavyPath s k)) ^ α := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range n, q ^ (k + 1) *
        (m.mass [] ^ α / ((2 : ℝ) ^ α - 2)) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
        (m.offspring_sum_le hα (internal n) k) (pow_nonneg hq _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma terminal_sum_le {α q : ℝ} (hα : 1 ≤ α) (hq : 0 ≤ q) (n : ℕ) :
    ∑ s ∈ internal n, q ^ s.length * m.mass s ^ α ≤
      m.mass [] ^ α * ∑ j ∈ Finset.range n, q ^ j := by
  rw [sum_internal]
  calc
    _ = ∑ j ∈ Finset.range n, q ^ j * m.potential α j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [potential]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(mem_level s j).mp hs]
    _ ≤ ∑ j ∈ Finset.range n, q ^ j * m.mass [] ^ α := by
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (m.potential_le_root hα j) (pow_nonneg hq j))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

def pathBudget (α q : ℝ) (s : List Bool) : ℝ :=
  m.offspringPenalty α q s + q ^ s.length * m.mass s ^ α

lemma pathBudget_nonneg (α : ℝ) {q : ℝ} (hq : 0 ≤ q) (s : List Bool) :
    0 ≤ m.pathBudget α q s :=
  add_nonneg (m.offspringPenalty_nonneg α hq s)
    (mul_nonneg (pow_nonneg hq _) (Real.rpow_nonneg (m.nonneg _) _))

lemma geom_sum_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
  have hs := summable_geometric_of_lt_one hq hq1
  simpa only [tsum_geometric_of_lt_one hq hq1, one_div] using
    hs.sum_le_tsum (Finset.range n) (fun _ _ => pow_nonneg hq _)

lemma next_geom_sum_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ (j + 1) ≤ q * (1 - q)⁻¹ := by
  simp only [pow_succ, ← Finset.sum_mul]
  rw [mul_comm q]
  exact mul_le_mul_of_nonneg_right (geom_sum_le hq hq1 n) hq

lemma pathBudget_internal_le {α q : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    ∑ s ∈ internal n, m.pathBudget α q s ≤
      m.mass [] ^ α * (1 - q)⁻¹ * (1 + q / ((2 : ℝ) ^ α - 2)) := by
  have hroot := Real.rpow_nonneg (m.nonneg []) α
  have hc := convexity_constant_pos hα
  calc
    _ = (∑ s ∈ internal n, m.offspringPenalty α q s) +
        ∑ s ∈ internal n, q ^ s.length * m.mass s ^ α := by
      simp only [pathBudget, Finset.sum_add_distrib]
    _ ≤ (m.mass [] ^ α / ((2 : ℝ) ^ α - 2)) *
          (∑ k ∈ Finset.range n, q ^ (k + 1)) +
        m.mass [] ^ α * ∑ j ∈ Finset.range n, q ^ j :=
      add_le_add (m.offspringPenalty_sum_le hα hq n) (m.terminal_sum_le hα.le hq n)
    _ ≤ (m.mass [] ^ α / ((2 : ℝ) ^ α - 2)) * (q * (1 - q)⁻¹) +
        m.mass [] ^ α * (1 - q)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left (next_geom_sum_le hq hq1 n)
          (div_nonneg hroot hc.le))
        (mul_le_mul_of_nonneg_left (geom_sum_le hq hq1 n) hroot)
    _ = _ := by ring

lemma pathBudget_sum_le {α q : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1)
    (S : Finset (List Bool)) :
    ∑ s ∈ S, m.pathBudget α q s ≤
      m.mass [] ^ α * (1 - q)⁻¹ * (1 + q / ((2 : ℝ) ^ α - 2)) := by
  let n := S.sup List.length + 1
  have hs : S ⊆ internal n := fun s hs => (mem_internal s n).mpr
    (Nat.lt_succ_of_le (Finset.le_sup hs))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun s _ _ => m.pathBudget_nonneg α hq s)).trans
    (m.pathBudget_internal_le hα hq hq1 n)

lemma pathBudget_summable {α q : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (m.pathBudget α q) :=
  summable_of_sum_le (m.pathBudget_nonneg α hq) (m.pathBudget_sum_le hα hq hq1)

lemma pathBudget_tsum_le {α q : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1) :
    ∑' s : List Bool, m.pathBudget α q s ≤
      m.mass [] ^ α * (1 - q)⁻¹ * (1 + q / ((2 : ℝ) ^ α - 2)) :=
  Real.tsum_le_of_sum_le (m.pathBudget_nonneg α hq) (m.pathBudget_sum_le hα hq hq1)

lemma heavy_light_mass (s : List Bool) :
    m.mass s = m.mass (m.heavy s) + m.mass (m.light s) := by
  dsimp [heavy, light]
  split_ifs <;> simpa [add_comm] using m.split s

lemma heavy_mass_le (s : List Bool) : m.mass (m.heavy s) ≤ m.mass s := by
  rw [m.heavy_light_mass s]
  exact le_add_of_nonneg_right (m.nonneg _)

lemma heavyPath_mass_le (s : List Bool) (n : ℕ) :
    m.mass (m.heavyPath s n) ≤ m.mass s := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simpa only [heavyPath, Function.iterate_succ_apply'] using
      (m.heavy_mass_le (m.heavyPath s n)).trans ih

lemma light_length (s : List Bool) : (m.light s).length = s.length + 1 := by
  dsimp [light]
  split_ifs <;> rfl

lemma heavy_light_add {E : Type*} [AddCommMonoid E] (G : List Bool → E)
    (hsplit : ∀ s, G s = G (false :: s) + G (true :: s)) (s : List Bool) :
    G s = G (m.light s) + G (m.heavy s) := by
  dsimp [heavy, light]
  split_ifs <;> simpa [add_comm] using hsplit s

lemma heavyPath_partition {E : Type*} [AddCommMonoid E] (G : List Bool → E)
    (hsplit : ∀ s, G s = G (false :: s) + G (true :: s)) (s : List Bool) (n : ℕ) :
    G s = (∑ k ∈ Finset.range n, G (m.light (m.heavyPath s k))) +
      G (m.heavyPath s n) := by
  induction n with
  | zero => simp [heavyPath]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc]
    have hp : m.heavyPath s (n + 1) = m.heavy (m.heavyPath s n) := by
      simp only [heavyPath, Function.iterate_succ_apply']
    rw [hp, ← m.heavy_light_add G hsplit (m.heavyPath s n)]
    exact ih

lemma norm_heavyPath_le {E : Type*} [SeminormedAddCommGroup E] (G : List Bool → E)
    (hsplit : ∀ s, G s = G (false :: s) + G (true :: s)) (s : List Bool) (n : ℕ) :
    ‖G s‖ ≤ (∑ k ∈ Finset.range n, ‖G (m.light (m.heavyPath s k))‖) +
      ‖G (m.heavyPath s n)‖ := by
  calc
    ‖G s‖ = ‖(∑ k ∈ Finset.range n, G (m.light (m.heavyPath s k))) +
        G (m.heavyPath s n)‖ := congrArg norm (m.heavyPath_partition G hsplit s n)
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)

end MassTree

lemma weighted_norm_sum_sq {E ι : Type*} [SeminormedAddCommGroup E]
    (S : Finset ι) (G : ι → E) (w B : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, 0 ≤ B i)
    (hG : ∀ i ∈ S, ‖G i‖ ^ 2 ≤ w i * B i) :
    ‖∑ i ∈ S, G i‖ ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, B i := by
  calc
    _ ≤ (∑ i ∈ S, ‖G i‖) ^ 2 := by
      have hn := norm_sum_le S G
      have hp : 0 ≤ ∑ i ∈ S, ‖G i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      nlinarith [norm_nonneg (∑ i ∈ S, G i)]
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S hw hB hG

namespace MassTree
variable (m : MassTree)

def pathPiece {E : Type*} (G : List Bool → E) (s : List Bool) (k : ℕ) : E :=
  if k < s.length then G (m.light (m.heavyPath s k)) else G (m.heavyPath s s.length)

lemma sum_pathPiece {E : Type*} [AddCommMonoid E] (G : List Bool → E)
    (hsplit : ∀ s, G s = G (false :: s) + G (true :: s)) (s : List Bool) :
    ∑ k ∈ Finset.range (s.length + 1), m.pathPiece G s k = G s := by
  rw [Finset.sum_range_succ, m.heavyPath_partition G hsplit s s.length]
  simp only [pathPiece, lt_self_iff_false, ↓reduceIte]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range.mp hk, ↓reduceIte]

def pathWeight (q : ℝ) (s : List Bool) (k : ℕ) : ℝ :=
  if k < s.length then q ^ (k + 1) else q ^ s.length

lemma pathWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (s : List Bool) (k : ℕ) :
    0 ≤ pathWeight q s k := by
  unfold pathWeight
  split_ifs <;> exact pow_nonneg hq _

lemma sum_pathWeight_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (s : List Bool) :
    ∑ k ∈ Finset.range (s.length + 1), pathWeight q s k ≤ (1 - q)⁻¹ := by
  have he : ∑ k ∈ Finset.range (s.length + 1), pathWeight q s k =
      (∑ k ∈ Finset.range s.length, q ^ (k + 1)) + q ^ s.length := by
    rw [Finset.sum_range_succ]
    simp only [pathWeight, lt_self_iff_false, ↓reduceIte]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range.mp hk, ↓reduceIte]
  rw [he]
  calc
    _ ≤ q * (1 - q)⁻¹ + 1 := add_le_add (next_geom_sum_le hq hq1 _)
      (pow_le_one₀ hq hq1.le)
    _ = (1 - q)⁻¹ := by
      field_simp [sub_ne_zero.mpr (ne_of_gt hq1)]
      ring

lemma energy_le_pathBudget {E : Type*} [SeminormedAddCommGroup E]
    (G : List Bool → E) (hsplit : ∀ s, G s = G (false :: s) + G (true :: s))
    {α q C : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (s : List Bool)
    (hlight : ∀ k < s.length, ‖G (m.light (m.heavyPath s k))‖ ^ 2 ≤
      C * (q ^ (k + 1)) ^ 2 * m.mass (m.light (m.heavyPath s k)) ^ α)
    (hterminal : ‖G (m.heavyPath s s.length)‖ ^ 2 ≤
      C * (q ^ s.length) ^ 2 * m.mass (m.heavyPath s s.length) ^ α) :
    ‖G s‖ ^ 2 ≤ C * (1 - q)⁻¹ * m.pathBudget α q s := by
  let w := pathWeight q s
  let B : ℕ → ℝ := fun k => C * w k * m.mass
    (if k < s.length then m.light (m.heavyPath s k) else m.heavyPath s s.length) ^ α
  have hw : ∀ k ∈ Finset.range (s.length + 1), 0 ≤ w k :=
    fun k _ => pathWeight_nonneg hq s k
  have hB : ∀ k ∈ Finset.range (s.length + 1), 0 ≤ B k := by
    intro k hk
    exact mul_nonneg (mul_nonneg hC (hw k hk)) (Real.rpow_nonneg (m.nonneg _) _)
  have hPiece : ∀ k ∈ Finset.range (s.length + 1),
      ‖m.pathPiece G s k‖ ^ 2 ≤ w k * B k := by
    intro k hk
    dsimp [pathPiece, B, w, pathWeight]
    split_ifs with hk'
    · nlinarith [hlight k hk']
    · nlinarith [hterminal]
  have hsumB : ∑ k ∈ Finset.range (s.length + 1), B k ≤ C * m.pathBudget α q s := by
    rw [Finset.sum_range_succ]
    have hterminal_mass : m.mass (m.heavyPath s s.length) ^ α ≤ m.mass s ^ α :=
      Real.rpow_le_rpow (m.nonneg _) (m.heavyPath_mass_le s _) (le_trans (by norm_num) hα.le)
    calc
      _ = C * m.offspringPenalty α q s + C * q ^ s.length *
          m.mass (m.heavyPath s s.length) ^ α := by
        simp only [B, w, pathWeight, lt_self_iff_false, ↓reduceIte, offspringPenalty,
          Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range.mp hk, ↓reduceIte]
        ring
      _ ≤ C * m.offspringPenalty α q s + C * q ^ s.length * m.mass s ^ α :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hterminal_mass
          (mul_nonneg hC (pow_nonneg hq _)))
      _ = C * m.pathBudget α q s := by dsimp [pathBudget]; ring
  calc
    ‖G s‖ ^ 2 = ‖∑ k ∈ Finset.range (s.length + 1), m.pathPiece G s k‖ ^ 2 := by
      rw [m.sum_pathPiece G hsplit]
    _ ≤ (∑ k ∈ Finset.range (s.length + 1), w k) *
        ∑ k ∈ Finset.range (s.length + 1), B k :=
      weighted_norm_sum_sq _ _ _ _ hw hB hPiece
    _ ≤ (1 - q)⁻¹ * (C * m.pathBudget α q s) := mul_le_mul
      (sum_pathWeight_le hq hq1 s) hsumB (Finset.sum_nonneg hB) (by positivity)
    _ = _ := by ring

lemma common_tree_energy_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (G : ℕ → List Bool → E)
    (hsplit : ∀ j s, G j s = G j (false :: s) + G j (true :: s))
    {α q C : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hlight : ∀ s k, k < s.length →
      ‖G s.length (m.light (m.heavyPath s k))‖ ^ 2 ≤
        C * (q ^ (k + 1)) ^ 2 * m.mass (m.light (m.heavyPath s k)) ^ α)
    (hterminal : ∀ s, ‖G s.length (m.heavyPath s s.length)‖ ^ 2 ≤
      C * (q ^ s.length) ^ 2 * m.mass (m.heavyPath s s.length) ^ α)
    (n : ℕ) :
    (∑ j ∈ Finset.range n, ∑ s ∈ level j, ‖G j s‖ ^ 2) ≤
      C * (1 - q)⁻¹ *
        (m.mass [] ^ α * (1 - q)⁻¹ * (1 + q / ((2 : ℝ) ^ α - 2))) := by
  have he (s : List Bool) : ‖G s.length s‖ ^ 2 ≤
      C * (1 - q)⁻¹ * m.pathBudget α q s :=
    m.energy_le_pathBudget (G s.length) (hsplit s.length)
      hα hq hq1 hC s (hlight s) (hterminal s)
  have hv : 0 ≤ C * (1 - q)⁻¹ := by positivity
  calc
    _ = ∑ s ∈ internal n, ‖G s.length s‖ ^ 2 := by
      rw [sum_internal]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      rw [(mem_level s j).mp hs]
    _ ≤ ∑ s ∈ internal n, C * (1 - q)⁻¹ * m.pathBudget α q s :=
      Finset.sum_le_sum (fun s _ => he s)
    _ = C * (1 - q)⁻¹ * (∑ s ∈ internal n, m.pathBudget α q s) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (m.pathBudget_internal_le hα hq hq1 n) hv

lemma common_tree_energy_tsum_le {E : Type*} [SeminormedAddCommGroup E]
    (G : ℕ → List Bool → E)
    (hsplit : ∀ j s, G j s = G j (false :: s) + G j (true :: s))
    {α q C : ℝ} (hα : 1 < α) (hq : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hlight : ∀ s k, k < s.length →
      ‖G s.length (m.light (m.heavyPath s k))‖ ^ 2 ≤
        C * (q ^ (k + 1)) ^ 2 * m.mass (m.light (m.heavyPath s k)) ^ α)
    (hterminal : ∀ s, ‖G s.length (m.heavyPath s s.length)‖ ^ 2 ≤
      C * (q ^ s.length) ^ 2 * m.mass (m.heavyPath s s.length) ^ α) :
    (∑' j, ∑ s ∈ level j, ‖G j s‖ ^ 2) ≤
      C * (1 - q)⁻¹ *
        (m.mass [] ^ α * (1 - q)⁻¹ * (1 + q / ((2 : ℝ) ^ α - 2))) := by
  apply Real.tsum_le_of_sum_range_le
    (fun j => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact m.common_tree_energy_sum_le G hsplit hα hq hq1 hC hlight hterminal

end MassTree

end PlanarEndpoint.TimeTree
end

end OAI
