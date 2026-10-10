import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityIncidence
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
import Mathlib.Tactic.Linarith

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence

namespace MatrixMultiplication.JointCompatibilityControls

attribute [local instance] Classical.propDecidable

private theorem exists_pos_le_family {K : Type*} [Fintype K]
    (δ : K → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ δ k := by
  classical
  have aux : ∀ s : Finset K, ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ s, ε ≤ δ k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert k s hk ih =>
        obtain ⟨ε, hε, hb⟩ := ih
        refine ⟨min (δ k) ε, lt_min (hδ k) hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hb j hj)
  obtain ⟨ε, hε, hb⟩ := aux Finset.univ
  exact ⟨ε, hε, fun k => hb k (Finset.mem_univ k)⟩

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def residualBase (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (c : C) : ℕ :=
  ∑ u : {u : Shape c // ¬d c u}, base c u.val

def designatedBase (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (c : C) : ℕ :=
  ∑ u : {u : Shape c // d c u}, base c u.val

def totalCenterCount (base : ∀ c, Shape c → ℕ)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) : ℝ :=
  ∑ u, (base c u : ℝ) * law c u a

def residualCenter (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) : ℝ :=
  (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) /
    residualBase base d c

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualBase_mul_center (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) :
    (residualBase base d c : ℝ) * residualCenter base d law c a =
      ∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a := by
  by_cases hr : residualBase base d c = 0
  · have hb (u : {u : Shape c // ¬d c u}) : base c u.val = 0 := by
      have hle : base c u.val ≤ residualBase base d c :=
        Finset.single_le_sum
          (f := fun v : {u : Shape c // ¬d c u} => base c v.val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
      rw [hr] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp only [hr, Nat.cast_zero, zero_mul, hb, Finset.sum_const_zero]
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hr)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_nonneg (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (h0 : ∀ c u a, 0 ≤ law c u a)
    (c : C) (a : A c) : 0 ≤ residualCenter base d law c a :=
  div_nonneg (Finset.sum_nonneg fun shape _ =>
    mul_nonneg (Nat.cast_nonneg _) (h0 c shape.val a))
    (Nat.cast_nonneg _)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_le_one (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (h1 : ∀ c u a, law c u a ≤ 1)
    (c : C) (a : A c) : residualCenter base d law c a ≤ 1 := by
  by_cases hr : residualBase base d c = 0
  · simp only [residualCenter, hr, Nat.cast_zero, div_zero, zero_le_one]
  · have hp : (0 : ℝ) < residualBase base d c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    apply (div_le_iff₀ hp).mpr
    calc
      (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) ≤
          ∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * 1 :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (h1 _ _ _) (Nat.cast_nonneg _)
      _ = 1 * (residualBase base d c : ℝ) := by
        simp only [mul_one, one_mul, residualBase, Nat.cast_sum]

def groupCenter (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (g : Σ c, Option (Shape c)) : A g.1 → ℝ :=
  match g.2 with
  | some u => law g.1 u
  | none => residualCenter base d law g.1

def groupCap (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (ε : ℝ) (g : Σ c, Option (Shape c)) : ℝ :=
  finiteEntropy (groupCenter base d law g) + ε

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (A c)] in
theorem groupCap_nonneg (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ)
    (h0 : ∀ c u a, 0 ≤ law c u a) (h1 : ∀ c u a, law c u a ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (g : Σ c, Option (Shape c)) :
    0 ≤ groupCap base d law ε g := by
  apply add_nonneg _ hε
  rcases g with ⟨c, k⟩
  cases k with
  | some u =>
      exact finiteEntropy_nonneg (law c u) (h0 c u) (h1 c u)
  | none =>
      exact finiteEntropy_nonneg (residualCenter base d law c)
        (residualCenter_nonneg base d law h0 c) (residualCenter_le_one base d law h1 c)

omit [DecidableEq C] [∀ c, DecidableEq (Shape c)] [∀ c, DecidableEq (A c)] in
private theorem exists_group_entropy_window (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (law : ∀ c, Shape c → A c → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g : Σ c, Option (Shape c)) (q : A g.1 → ℝ),
      (∀ a, |q a - groupCenter base d law g a| ≤ δ) →
      finiteEntropy q ≤ groupCap base d law ε g := by
  have hex : ∀ g : Σ c, Option (Shape c), ∃ δ : ℝ, 0 < δ ∧
      ∀ q : A g.1 → ℝ, (∀ a, |q a - groupCenter base d law g a| ≤ δ) →
        |finiteEntropy q - finiteEntropy (groupCenter base d law g)| < ε :=
    fun g => exists_entropy_window (groupCenter base d law g) hε
  choose δ hδ hw using hex
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_le_family δ hδ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro g q hq
  have hh := (abs_lt.mp (hw g q (fun a => (hq a).trans (hsmall g)))).2
  change finiteEntropy q ≤ finiteEntropy (groupCenter base d law g) + ε
  linarith

omit [Fintype C] [DecidableEq C] in
theorem residual_card_repeated
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card {i : Pos c // ¬d c ((w c).val i)} = t * residualBase base d c := by
  have he := (Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype (w c).val
    (p := fun i => ¬d c ((w c).val i)) (q := fun u => ¬d c u)
    (fun _ => Iff.rfl))).symm
  have hc : Fintype.card {i : Pos c // ¬d c ((w c).val i)} =
      ∑ u : {u : Shape c // ¬d c u}, wordPopulation (w c).val u.val := by
    simpa only [Fintype.card_sigma, wordPopulation] using he
  exact hc.trans (by simp only [(w c).property, residualBase, Finset.mul_sum])

omit [Fintype C] [DecidableEq C] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem repeated_mixture_balance
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) (a : A c) :
    (Fintype.card {i : Pos c // ¬d c ((w c).val i)} : ℝ) * residualCenter base d law c a =
      (t : ℝ) * totalCenterCount base law c a -
        ∑ u : {u : Shape c // d c u}, (t * base c u.val : ℕ) * law c u.val a := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (d c)
    (fun u => (base c u : ℝ) * law c u a)
  have hb : (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) =
      totalCenterCount base law c a -
        ∑ u : {u : Shape c // d c u}, (base c u.val : ℝ) * law c u.val a := by
    unfold totalCenterCount
    linarith
  rw [residual_card_repeated, Nat.cast_mul, mul_assoc, residualBase_mul_center, hb]
  simp only [Nat.cast_mul, mul_sub, Finset.mul_sum, mul_assoc]

omit [Fintype C] [DecidableEq C] in
private theorem repeated_residual_width_le
    {Pos : C → Type*} [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (t : ℕ) (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    (χ η δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : ∀ c, η + (designatedBase base d c : ℝ) * χ ≤ δ) (c : C) :
    ((t : ℝ) * η + (∑ u : {u : Shape c // d c u}, ((t * base c u.val : ℕ) : ℝ)) * χ) /
        Fintype.card {i : Pos c // ¬d c ((w c).val i)} ≤ δ := by
  have hsum : (∑ u : {u : Shape c // d c u}, ((t * base c u.val : ℕ) : ℝ)) =
      (t : ℝ) * designatedBase base d c := by
    simp only [Nat.cast_mul, designatedBase, Nat.cast_sum, Finset.mul_sum]
  rw [residual_card_repeated, hsum, Nat.cast_mul]
  by_cases ht : t = 0
  · simpa only [ht, Nat.cast_zero, zero_mul, add_zero, zero_add, zero_div] using hδ
  by_cases hr : residualBase base d c = 0
  · simpa only [hr, Nat.cast_zero, mul_zero, div_zero] using hδ
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)
  have hrpos : (0 : ℝ) < residualBase base d c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  have hrone : (1 : ℝ) ≤ residualBase base d c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have hres : η + (designatedBase base d c : ℝ) * χ ≤ δ * residualBase base d c :=
    (hnum c).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hrone hδ)
  apply (div_le_iff₀ (mul_pos htpos hrpos)).mpr
  calc
    (t : ℝ) * η + ((t : ℝ) * designatedBase base d c) * χ =
        (t : ℝ) * (η + (designatedBase base d c : ℝ) * χ) := by ring
    _ ≤ (t : ℝ) * (δ * residualBase base d c) :=
      mul_le_mul_of_nonneg_left hres htpos.le
    _ = δ * ((t : ℝ) * residualBase base d c) := by ring

omit [DecidableEq C] in
theorem exists_uniform_sideEntropyControl
    (Pos : ℕ → C → Type*) [∀ t c, Fintype (Pos t c)] [∀ t c, DecidableEq (Pos t c)]
    (Pair : C → Type*) [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (part : ∀ c, Pair c → A c)
    (h0 : ∀ c u a, 0 ≤ law c u a) (h1 : ∀ c u a, law c u a ≤ 1)
    {ε χMax ηMax : ℝ} (hε : 0 < ε) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ (t : ℕ) (pairCounts : ∀ c, Pair c → ℕ)
        (w : FixedClassWords (Pos t) Shape (fun c u => t * base c u)),
        (∀ c a, |((∑ s : {s : Pair c // part c s = a}, pairCounts c s.val : ℕ) : ℝ) -
          (t : ℝ) * totalCenterCount base law c a| ≤ (t : ℝ) * η) →
        Nonempty (SideEntropyControl (Pos t) Shape Pair A (fun c u => t * base c u)
          pairCounts part d law χ (groupCap base d law ε) w) := by
  obtain ⟨δ, hδ, hwindow⟩ := exists_group_entropy_window base d law hε
  let D : ℕ := ∑ c, designatedBase base d c
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hden : 0 < 2 * ((D : ℝ) + 1) := by positivity
  let χ₀ : ℝ := δ / (2 * ((D : ℝ) + 1))
  have hχ₀ : 0 < χ₀ := div_pos hδ hden
  have heq : (2 * ((D : ℝ) + 1)) * χ₀ = δ := mul_div_cancel₀ _ hden.ne'
  have hχδ : χ₀ ≤ δ := by nlinarith [mul_nonneg hD hχ₀.le]
  have hDχ : (D : ℝ) * χ₀ ≤ δ / 2 := by nlinarith
  let χ := min χMax χ₀
  let η := min ηMax (δ / 2)
  have hχ : 0 < χ := lt_min hχMax hχ₀
  have hη : 0 < η := lt_min hηMax (half_pos hδ)
  have hχδ' : χ ≤ δ := (min_le_right _ _).trans hχδ
  have hnum (c : C) : η + (designatedBase base d c : ℝ) * χ ≤ δ := by
    have hc : (designatedBase base d c : ℝ) ≤ D := by
      exact_mod_cast (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c) : designatedBase base d c ≤ ∑ c, designatedBase base d c)
    have hm : (designatedBase base d c : ℝ) * χ ≤ (D : ℝ) * χ₀ :=
      mul_le_mul hc (min_le_right _ _) hχ.le hD
    have he : η ≤ δ / 2 := min_le_right _ _
    linarith
  refine ⟨χ, η, hχ, min_le_left _ _, hη, min_le_left _ _, ?_⟩
  intro t pairCounts w haggr
  refine ⟨{
    residualLaw := residualCenter base d law
    totalTarget := fun c a => (t : ℝ) * totalCenterCount base law c a
    totalError := fun _ => (t : ℝ) * η
    aggregate_window := haggr
    mixture_balance := repeated_mixture_balance base d law t w
    nonneg := groupCap_nonneg base d law h0 h1 hε.le
    designated_entropy := ?_
    residual_entropy := ?_ }⟩
  · intro c u _ q hq
    exact hwindow ⟨c, some u⟩ q (fun a => (hq a).trans hχδ')
  · intro c q hq
    exact hwindow ⟨c, none⟩ q (fun a => (hq a).trans
      (repeated_residual_width_le base d t w χ η δ hδ.le hnum c))

def control_mono_width
    {Pos Pair : C → Type*}
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
    (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
    (part : ∀ c, Pair c → A c) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) {χ χ' : ℝ}
    (H : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape shapeCounts)
    (control : SideEntropyControl Pos Shape Pair A shapeCounts pairCounts part d law χ H w)
    (hχ : χ' ≤ χ) :
    SideEntropyControl Pos Shape Pair A shapeCounts pairCounts part d law χ' H w where
  residualLaw := control.residualLaw
  totalTarget := control.totalTarget
  totalError := control.totalError
  aggregate_window := control.aggregate_window
  mixture_balance := control.mixture_balance
  nonneg := control.nonneg
  designated_entropy c u hu q hq :=
    control.designated_entropy c u hu q (fun a => (hq a).trans hχ)
  residual_entropy c q hq := by
    apply control.residual_entropy c q
    intro a
    apply (hq a).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_left hχ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

end MatrixMultiplication.JointCompatibilityControls

end

end OAI
