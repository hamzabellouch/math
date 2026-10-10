import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupAssignmentRetention
import OAI.LinearAlgebra.MatrixFields.Entropy.JointCompatibilityRateLimit

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence

namespace MatrixMultiplication.JointCompatibilityControls

attribute [local instance] Classical.propDecidable

private theorem exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityControls {K : Type*} [Fintype K]
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
private theorem exists_group_entropy_window_inline_MatrixMultiplication_JointCompatibilityControls (base : ∀ c, Shape c → ℕ)
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
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityControls δ hδ
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
private theorem repeated_residual_width_le_inline_MatrixMultiplication_JointCompatibilityControls
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
  obtain ⟨δ, hδ, hwindow⟩ := exists_group_entropy_window_inline_MatrixMultiplication_JointCompatibilityControls base d law hε
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
      (repeated_residual_width_le_inline_MatrixMultiplication_JointCompatibilityControls base d t w χ η δ hδ.le hnum c))

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
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_left hχ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

end MatrixMultiplication.JointCompatibilityControls

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPairMixtureControls

open JointCompatibilityControls JointCompatibilityScaling
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A B : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

def pairMixture (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (c : C) (ab : A c × B c) : ℝ :=
  (∑ u, (base c u : ℝ) * left c u ab.1 * right c u ab.2) / baseSize base c

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (B c)] in
theorem sum_first_fiber (c : C) (q : A c × B c → ℝ) (a : A c) :
    (∑ ab : {ab : A c × B c // ab.1 = a}, q ab.val) = ∑ b, q (a, b) := by
  let e : B c ≃ {ab : A c × B c // ab.1 = a} :=
    { toFun := fun b => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.2
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext ab.property.symm rfl }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem sum_second_fiber (c : C) (q : A c × B c → ℝ) (b : B c) :
    (∑ ab : {ab : A c × B c // ab.2 = b}, q ab.val) = ∑ a, q (a, b) := by
  let e : A c ≃ {ab : A c × B c // ab.2 = b} :=
    { toFun := fun a => ⟨(a, b), rfl⟩
      invFun := fun ab => ab.val.1
      left_inv := fun _ => rfl
      right_inv := fun ab => by apply Subtype.ext; exact Prod.ext rfl ab.property.symm }
  exact (e.sum_comp (fun ab => q ab.val)).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)] in
theorem base_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (c : C) (hz : baseSize base c = 0) (u : Shape c) : base c u = 0 :=
  Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ u)).trans_eq hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem totalCenterCount_eq_zero_of_size_eq_zero (base : ∀ c, Shape c → ℕ)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (hz : baseSize base c = 0) (a : A c) :
    totalCenterCount base law c a = 0 := by
  simp only [totalCenterCount, base_eq_zero_of_size_eq_zero base c hz,
    Nat.cast_zero, zero_mul, Finset.sum_const_zero]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (B c)] in
theorem pairMixture_left_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ b, right c u b = 1)
    (c : C) (a : A c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.1 = a}, pairMixture base left right c ab.val) =
      totalCenterCount base left c a := by
  rw [sum_first_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ b : B c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base left c a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.mul_sum, hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base left c hz a]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, DecidableEq (A c)] in
theorem pairMixture_right_balance (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (hnormalized : ∀ c u, 0 < base c u → ∑ a, left c u a = 1)
    (c : C) (b : B c) :
    (baseSize base c : ℝ) *
      (∑ ab : {ab : A c × B c // ab.2 = b}, pairMixture base left right c ab.val) =
      totalCenterCount base right c b := by
  rw [sum_second_fiber]
  simp only [pairMixture, ← Finset.sum_div]
  have hnum : (∑ a : A c, ∑ u : Shape c,
      (base c u : ℝ) * left c u a * right c u b) = totalCenterCount base right c b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : base c u = 0
    · simp [hu]
    · rw [← Finset.sum_mul, ← Finset.mul_sum,
        hnormalized c u (Nat.pos_of_ne_zero hu), mul_one]
  rw [hnum]
  by_cases hz : baseSize base c = 0
  · rw [totalCenterCount_eq_zero_of_size_eq_zero base right c hz b]
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

end MatrixMultiplication.JointPairMixtureControls

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairWindows

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryMasks AllFieldHistoryMaskLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

def base (allocation : Allocation) (sigma : Placement) (side : Fin 3) :=
  JointPopulationCompatibility.classCounts
    (Counts (K := K) (tick := tick) allocation 1 sigma) (sigma side)

def q (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → ℝ :=
  JointPairMixtureControls.pairMixture (base (K := K) (tick := tick) allocation sigma side)
    (fun c u => supportedHalfLaw allocation false c.1.val u (sigma side))
    (fun c u => supportedHalfLaw allocation true c.1.val u (sigma side)) c

abbrev Positions (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.ClassPos (Counts (K := K) (tick := tick) allocation m sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w)

def pairCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.statisticCounts (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w) w

def parentBase (allocation : Allocation) (h : ActiveOrder K tick sigma) : ℕ :=
  population allocation 1 (h.val.val.1.source, h.val.val.2)

def parentPair (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) : ℝ :=
  (∑ u, (activeCounts allocation 1 h.val u : ℝ) *
    supportedHalfLaw allocation false h.val u (sigma side) a.1 *
    supportedHalfLaw allocation true h.val u (sigma side) a.2) / parentBase (K := K) (tick := tick) allocation h

def classMass (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : ℝ :=
  (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) / parentBase (K := K) (tick := tick) allocation c.1

def windowFactor (allocation : Allocation) (sigma : Placement) : ℝ :=
  1 + ∑ h : ActiveOrder K tick sigma, (parentBase (K := K) (tick := tick) allocation h : ℝ)

theorem windowFactor_pos (allocation : Allocation) (sigma : Placement) :
    0 < windowFactor (K := K) (tick := tick) allocation sigma := by
  unfold windowFactor
  positivity

theorem parentBase_pos (allocation : Allocation) (h : ActiveOrder K tick sigma) :
    0 < parentBase (K := K) (tick := tick) allocation h :=
  AllFieldHistorySupport.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val.val

theorem parent_positions_card (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) :
    Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      m * parentBase (K := K) (tick := tick) allocation h := by
  change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
  rw [Fintype.card_fin, jointCounts_sum]
  exact population_dilation allocation m _

theorem positions_card (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) =
      m * baseSize (base (K := K) (tick := tick) allocation sigma side) c := by
  have he : JointPopulationCompatibility.FixedSideTargets (Counts (K := K) (tick := tick) allocation m sigma)
      (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) :=
    ⟨e, fun h j => (hw.1.1 h j).symm⟩
  rw [JointPopulationCompatibility.classCounts_size
    (Counts (K := K) (tick := tick) allocation m sigma) (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) he c]
  simp only [JointPopulationCompatibility.classCounts, Counts, groupCounts,
    activeCounts_dilation allocation m, base, baseSize, Finset.mul_sum, mul_ite, mul_zero]

theorem parentPair_eq_parentCenter (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = parentCenter allocation (sigma side) h.val a.1 a.2 := by
  unfold parentPair parentCenter parentBase
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · simp only [supportedHalfLaw, ite_eq_left hu, halfLawAt, Bool.false_eq_true,
      ite_false, ite_true]
    ring
  · have hz := Nat.eq_zero_of_not_pos hu
    simp only [hz, Nat.cast_zero, zero_mul, zero_div]

theorem parentPair_eq_native (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = orderPairMixture h side a := by
  rw [parentPair_eq_parentCenter]
  unfold parentCenter orderPairMixture
  apply Finset.sum_congr rfl
  intro u _
  rw [show (activeCounts allocation 1 h.val u : ℝ) /
      population allocation 1 (h.val.val.1.source, h.val.val.2) =
      (AllFieldActiveLaws.orderLaw h).mass u from
    AllFieldActiveLaws.jointCounts_ratio allocation (by decide : 0 < (1 : ℕ)) h.val.val u]
  ring

def parentStatistic (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (h : ActiveOrder K tick sigma)
    (j : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    Statistic h.val × Statistic h.val :=
  (statistic h.val (w h j).1, statistic h.val (w h j).2)

theorem parent_window (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) :
    |(wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) /
      Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) -
        parentPair (K := K) (tick := tick) allocation sigma side h a| ≤ pairWidth ε h.val := by
  let defaults : SymbolChoice K tick := fun h => statistic h (fun _ => 0)
  let l : SymbolChoice K tick := Function.update defaults h.val a.1
  let r : SymbolChoice K tick := Function.update defaults h.val a.2
  have hp := hw (h.val, l, r) h.property
  rw [center_eq_parentCenter] at hp
  simp only [l, r, Function.update_self] at hp
  rw [parentPair_eq_parentCenter]
  have hpop : Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
    rw [Fintype.card_fin]
    exact jointCounts_sum allocation m h.val.val
  rw [hpop]
  have hcount : (wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) =
      ∑ j : JointPopulation.Positions (activeCounts allocation m) h.val,
        if statistic h.val (w h j).1 = a.1 ∧ statistic h.val (w h j).2 = a.2
          then (1 : ℝ) else 0 := by
    rcases a with ⟨a₁, a₂⟩
    simp only [wordPopulation, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      parentStatistic, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hcount]
  exact hp

def weightCode {K : ℕ} (w : Work K) : w.Statistic → Fin 17 :=
  match w with
  | .stageA _ => AllFieldPairMarginals.halfWeightCode
  | .stageB _ => AllFieldPairMarginals.statisticWeightCode
  | .stageC _ => fun _ => 0

@[simp] theorem weightCode_val {K : ℕ} (w : Work K) (a : w.Statistic) :
    (weightCode w a).val = w.statisticWeight a := by
  cases w <;> rfl

theorem weightCode_statistic {K : ℕ} (w : Work K) (hs : w.stage ≠ 2)
    (x : CWWindowedLeaves.Raw w.halfLength) :
    (weightCode w (w.statistic x)).val = CWStrands.weight x :=
  (weightCode_val w _).trans (w.statistic_weight hs x).symm

theorem left_supported_zero (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2)
    (u : JointPopulation.Shape) (a : Statistic h.val)
    (ha : weightCode h.val.val.1 a ≠ JointPopulation.shapeSide (sigma side) u) :
    supportedHalfLaw allocation false h.val u (sigma side) a = 0 := by
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · rw [supportedHalfLaw_eq_of_counts_pos allocation 1 false h.val u hu, halfLawAt_eq]
    apply Rat.cast_eq_zero.mpr
    apply h.val.val.1.childLaw_outside_support hs _
      (halfShape_mem_of_counts_pos allocation 1 false h.val u hu) _ a
    rw [halfShape_childWeight]
    simpa only [childWeight, Bool.false_eq_true, ite_false, ← weightCode_val,
      ne_eq, Fin.ext_iff] using ha
  · simp only [supportedHalfLaw, ite_eq_right hu]

theorem filtered_pair_sum (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        ∑ u, (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
  have hterm (u : JointPopulation.Shape) :
      (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
        supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
        supportedHalfLaw allocation true c.1.val u (sigma side) a.2 =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
    by_cases hu : JointPopulation.shapeSide (sigma side) u = c.2
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_true]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · rw [ite_eq_left ha]
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => ha (he.trans hu))
        simp only [ha, ite_false, hz, mul_zero, zero_mul]
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_false, Nat.cast_zero, zero_mul]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => hu (he.symm.trans ha))
        simp only [ha, ite_true, hz, mul_zero, zero_mul]
      · rw [ite_eq_right ha]
  simp_rw [hterm]
  split_ifs <;> simp

theorem q_eq_conditionalCenter (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2) :
    q (K := K) (tick := tick) allocation sigma side c = JointPairClassWindows.conditionalCenter
      (fun a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c => weightCode c.1.val.val.1 a.1)
      c.2 (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c) := by
  funext a
  rw [q, JointPairMixtureControls.pairMixture, filtered_pair_sum (K := K) (tick := tick) allocation sigma side c hs]
  unfold JointPairClassWindows.conditionalCenter parentPair classMass
  by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
  · simp only [ha, ite_true]
    have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
    rw [div_div_div_cancel_right₀ hp]
  · simp only [ha, ite_false, zero_div]

theorem classMass_pos (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    0 < classMass (K := K) (tick := tick) allocation sigma side c :=
  div_pos (Nat.cast_pos.mpr hc) (Nat.cast_pos.mpr (parentBase_pos (K := K) (tick := tick) allocation c.1))

theorem fiber_mass (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) =
      (Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1) : ℝ) *
        classMass (K := K) (tick := tick) allocation sigma side c := by
  rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw, parent_positions_card]
  rw [Nat.cast_mul, Nat.cast_mul]
  unfold classMass
  have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
  rw [mul_assoc, mul_div_cancel₀ _ hp]

theorem width_le (allocation : Allocation) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3) (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    pairWidth ε c.1.val / classMass (K := K) (tick := tick) allocation sigma side c ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  have hpw : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hw : pairWidth ε c.1.val ≤ ε :=
    div_le_self hε (one_le_pow₀ (by norm_num))
  have hb : (1 : ℝ) ≤ baseSize (base (K := K) (tick := tick) allocation sigma side) c := by exact_mod_cast hc
  have hn : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≤ windowFactor (K := K) (tick := tick) allocation sigma := by
    unfold windowFactor
    exact (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ c.1)).trans
      (le_add_of_nonneg_left zero_le_one)
  unfold classMass
  rw [div_div_eq_mul_div]
  calc
    pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) /
        (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) ≤
        pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) :=
      div_le_self (mul_nonneg hpw (Nat.cast_nonneg _)) hb
    _ ≤ ε * windowFactor (K := K) (tick := tick) allocation sigma := mul_le_mul hw hn (Nat.cast_nonneg _) hε
    _ = _ := mul_comm _ _

theorem sharing_window (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    |(pairCounts (K := K) (tick := tick) allocation m sigma w c a : ℝ) /
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) - q (K := K) (tick := tick) allocation sigma side c a| ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  let z := parentStatistic (K := K) (tick := tick) allocation m sigma w c.1
  let k : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1 → Fin 17 :=
    fun j => ownWord (K := K) (tick := tick) allocation m sigma w ⟨c.1, j⟩
  let f : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → Fin 17 :=
    fun a => weightCode c.1.val.val.1 a.1
  have hf (j) : f (z j) = k j := by
    apply Fin.ext
    exact weightCode_statistic c.1.val.val.1 hs (w c.1 j).1
  have hη : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hh := JointPairClassWindows.fiber_window z k f hf c.2
    (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c)
    (pairWidth ε c.1.val) (classMass_pos (K := K) (tick := tick) allocation sigma side c hc) hη
    (fiber_mass (K := K) (tick := tick) allocation m ε sigma side e w hw c)
    (parent_window (K := K) (tick := tick) allocation m ε sigma side w hp c.1) a
  rw [← q_eq_conditionalCenter (K := K) (tick := tick) allocation sigma side c hs] at hh
  exact hh.trans (width_le (K := K) (tick := tick) allocation hε sigma side c hc)

theorem q_eq_one_of_subsingleton (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) [Subsingleton (Symbol (K := K) (tick := tick) sigma c)]
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) : q (K := K) (tick := tick) allocation sigma side c a = 1 := by
  have hl (right : Bool) (u : JointPopulation.Shape)
      (hu : 0 < base (K := K) (tick := tick) allocation sigma side c u) :
      supportedHalfLaw allocation right c.1.val u (sigma side) (if right then a.2 else a.1) = 1 := by
    have hu' : 0 < activeCounts allocation 1 c.1.val u := by
      unfold base JointPopulationCompatibility.classCounts Counts groupCounts at hu
      split_ifs at hu with he
      · exact hu
      · omega
    rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right c.1.val u hu']
    have ht := halfLawAt_normalized allocation 1 right c.1.val u hu' (sigma side)
    have he : (∑ b, halfLawAt right c.1.val u (sigma side) b) =
        halfLawAt right c.1.val u (sigma side) (if right then a.2 else a.1) :=
      Fintype.sum_subsingleton _ _
    exact he.symm.trans ht
  unfold q JointPairMixtureControls.pairMixture
  have hn : (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) := by
    rw [baseSize, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : 0 < base (K := K) (tick := tick) allocation sigma side c u
    · have hleft : supportedHalfLaw allocation false c.1.val u (sigma side) a.1 = 1 := by
        simpa only [Bool.false_eq_true, ite_false] using hl false u hu
      have hright : supportedHalfLaw allocation true c.1.val u (sigma side) a.2 = 1 := by
        simpa only [ite_true] using hl true u hu
      rw [hleft, hright, mul_one, mul_one]
    · simp only [Nat.eq_zero_of_not_pos hu, Nat.cast_zero, zero_mul]
  rw [hn]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))

theorem pairWindow_of_completeKeep (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : completeKeep allocation m ε (sigma side) sigma w) :
    PairWindow (base (K := K) (tick := tick) allocation sigma side) (q (K := K) (tick := tick) allocation sigma side)
      (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts (K := K) (tick := tick) allocation m sigma w)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  intro c hc a
  by_cases hs : c.1.val.val.1.stage ≠ 2
  · exact sharing_window (K := K) (tick := tick) allocation m hε sigma side e w hw hp.2.2 c hs hc a
  · have hstage : c.1.val.val.1.stage = 2 := not_ne_iff.mp hs
    have : Subsingleton (Symbol (K := K) (tick := tick) sigma c) := by
      change Subsingleton c.1.val.val.1.Statistic
      cases hh : c.1.val.val.1 with
      | stageA h => simp [hh, Work.stage] at hstage
      | stageB h => simp [hh, Work.stage] at hstage
      | stageC h => dsimp [Work.Statistic]; infer_instance
    have hpc : pairCounts (K := K) (tick := tick) allocation m sigma w c a =
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) := by
      unfold pairCounts JointPopulationCompatibility.statisticCounts
      have hall : ∀ i, JointPopulationCompatibility.statisticWord
          (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
          (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
          (ownWord (K := K) (tick := tick) allocation m sigma w) w c i = a := fun _ => Subsingleton.elim _ _
      simp [wordPopulation, hall]
    have hn : (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) ≠ 0 := by
      rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw c]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hm hc))
    rw [hpc, div_self hn, q_eq_one_of_subsingleton (K := K) (tick := tick) allocation sigma side c hc a,
      sub_self, abs_zero]
    exact mul_nonneg (windowFactor_pos (K := K) (tick := tick) allocation sigma).le hε

theorem passing_pairWindow (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
    PairWindow (base (K := K) (tick := tick) allocation sigma v.1) (q (K := K) (tick := tick) allocation sigma v.1)
      (Positions (K := K) (tick := tick) allocation m sigma v.2) (pairCounts (K := K) (tick := tick) allocation m sigma v.2)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  have hpass := (mem_passing allocation m ε sigma e o v).mp hv
  exact pairWindow_of_completeKeep (K := K) (tick := tick) allocation hm hε sigma v.1 e v.2
    (AllFieldGroupAdmissible.full_admissible allocation m ε sigma e o ho v hpass.1) hpass.2

end MatrixMultiplication.AllFieldGroupPairWindows

end
end

end MatrixAllFields

end OAI
