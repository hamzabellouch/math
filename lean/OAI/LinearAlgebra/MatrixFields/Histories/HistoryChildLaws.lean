import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.ShapeEncoding
import OAI.LinearAlgebra.MatrixFields.Entropy.ParametersHalfLaws
import OAI.LinearAlgebra.MatrixFields.Parameters.PopulationCounts
import OAI.LinearAlgebra.MatrixFields.Tensors.CWCompleteStatistics

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

abbrev Capacity := Fin 3 → ℝ

def totalCapacity (a b : Capacity) (base : ℝ) : ℝ :=
  base + (∑ i, (a i + b i)) / 3

def balanceFraction (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  (high - totalCapacity a b base + (a i + b i)) / (3 * (high - base))

def thirdCapacity (a b : Capacity) (high base : ℝ) (i : Fin 3) : ℝ :=
  high - 3 * balanceFraction a b high base i * (high - base)

theorem balanceFraction_pos (a b : Capacity) (high base : ℝ)
    (hbase : base < high)
    (hfeas : ∀ i, totalCapacity a b base - (a i + b i) < high) (i : Fin 3) :
    0 < balanceFraction a b high base i := by
  apply div_pos
  · linarith [hfeas i]
  · exact mul_pos (by norm_num) (sub_pos.mpr hbase)

theorem sum_balanceFraction (a b : Capacity) (high base : ℝ)
    (hbase : base < high) : ∑ i, balanceFraction a b high base i = 1 := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  simp only [balanceFraction, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  unfold totalCapacity
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  field_simp
  ring

theorem thirdCapacity_eq (a b : Capacity) (high base : ℝ)
    (hbase : base < high) (i : Fin 3) :
    thirdCapacity a b high base i = totalCapacity a b base - (a i + b i) := by
  have hn : high - base ≠ 0 := ne_of_gt (sub_pos.mpr hbase)
  unfold thirdCapacity balanceFraction
  field_simp
  ring

theorem balanced (a b : Capacity) (high base : ℝ) (hbase : base < high)
    (i : Fin 3) : a i + b i + thirdCapacity a b high base i =
      totalCapacity a b base := by
  rw [thirdCapacity_eq a b high base hbase]
  ring

def minCapacity (a : Capacity) : ℝ := min (a 0) (min (a 1) (a 2))

def maxCapacity (a : Capacity) : ℝ := max (a 0) (max (a 1) (a 2))

theorem minCapacity_pos (a : Capacity) (h : ∀ i, 0 < a i) :
    0 < minCapacity a := by
  exact lt_min (h 0) (lt_min (h 1) (h 2))

theorem minCapacity_le_maxCapacity (a : Capacity) : minCapacity a ≤ maxCapacity a := by
  exact (min_le_left _ _).trans (le_max_left _ _)

theorem minCapacity_complement (a : Capacity) (c : ℝ) :
    minCapacity (fun i => c - a i) = c - maxCapacity a := by
  simp only [minCapacity, maxCapacity, min_def, max_def]
  split_ifs <;> linarith

def boundaryDeficit (a b c : Capacity) (full : ℝ) : ℝ :=
  2 * full - minCapacity a - minCapacity (fun i => a i + b i) -
    minCapacity (fun i => b i + c i) - minCapacity c

theorem boundaryDeficit_eq_ranges (a b c : Capacity) (full : ℝ)
    (h : ∀ i, a i + b i + c i = full) :
    boundaryDeficit a b c full =
      (maxCapacity a - minCapacity a) + (maxCapacity c - minCapacity c) := by
  have hab : (fun i => a i + b i) = (fun i => full - c i) := by
    funext i
    linarith [h i]
  have hbc : (fun i => b i + c i) = (fun i => full - a i) := by
    funext i
    linarith [h i]
  rw [boundaryDeficit, hab, hbc, minCapacity_complement, minCapacity_complement]
  ring

theorem boundaryDeficit_nonneg (a b c : Capacity) (full : ℝ)
    (h : ∀ i, a i + b i + c i = full) : 0 ≤ boundaryDeficit a b c full := by
  rw [boundaryDeficit_eq_ranges a b c full h]
  exact add_nonneg (sub_nonneg.mpr (minCapacity_le_maxCapacity a))
    (sub_nonneg.mpr (minCapacity_le_maxCapacity c))

theorem finite_schedule_yield (a b c : Capacity) (full : ℝ) (K : ℕ) (hK : 2 ≤ K) :
    (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
      minCapacity (fun i => b i + c i) + minCapacity c =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [Nat.cast_sub hK]
  norm_num [boundaryDeficit]
  ring

theorem physical_order_unique (rho sigma : Equiv.Perm (Fin 3)) :
    ∃! phi : Equiv.Perm (Fin 3), rho.trans phi = sigma := by
  refine ⟨rho.symm.trans sigma, ?_, ?_⟩
  · ext i
    simp
  · intro phi hphi
    apply Equiv.ext
    intro i
    have h := Equiv.congr_fun hphi (rho.symm i)
    simpa using h

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

def lotTick {K : ℕ} (j : Fin K) (stage : Fin 3) : ℕ := j.val + stage.val

theorem lotTick_lt {K : ℕ} (j : Fin K) (stage : Fin 3) :
    lotTick j stage < K + 2 := by
  have hj := j.isLt
  have hs := stage.isLt
  dsimp [lotTick]
  omega

def stageActive (K tick : ℕ) (stage : Fin 3) : Prop :=
  stage.val ≤ tick ∧ tick < K + stage.val

instance (K tick : ℕ) (stage : Fin 3) : Decidable (stageActive K tick stage) :=
  inferInstanceAs (Decidable (stage.val ≤ tick ∧ tick < K + stage.val))

theorem stageActive_iff_unique_lot (K tick : ℕ) (stage : Fin 3) :
    stageActive K tick stage ↔ ∃! j : Fin K, lotTick j stage = tick := by
  constructor
  · rintro ⟨hle, hlt⟩
    refine ⟨⟨tick - stage.val, by omega⟩, ?_, ?_⟩
    · dsimp [lotTick]
      omega
    · intro j hj
      apply Fin.ext
      dsimp [lotTick] at hj ⊢
      omega
  · rintro ⟨j, hj, _⟩
    have hjlt := j.isLt
    dsimp [stageActive, lotTick] at *
    omega

theorem lot_active_at_its_tick {K : ℕ} (j : Fin K) (stage : Fin 3) :
    stageActive K (lotTick j stage) stage := by
  have hj := j.isLt
  dsimp [stageActive, lotTick]
  omega

def tickCapacity (K : ℕ) (a b c : Capacity) (tick : ℕ) : Capacity := fun i =>
  (if stageActive K tick 0 then a i else 0) +
    (if stageActive K tick 1 then b i else 0) +
    (if stageActive K tick 2 then c i else 0)

theorem tickCapacity_first (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 0 = a := by
  funext i
  have h0 : 0 < K := by omega
  simp [tickCapacity, stageActive, h0]

theorem tickCapacity_second (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 1 = fun i => a i + b i := by
  funext i
  have h1 : 1 < K := by omega
  have h2 : 1 < K + 1 := by omega
  simp [tickCapacity, stageActive, h1, h2]

theorem tickCapacity_interior (K tick : ℕ) (ht : 2 ≤ tick) (htK : tick < K)
    (a b c : Capacity) :
    tickCapacity K a b c tick = fun i => a i + b i + c i := by
  funext i
  have h1 : 1 ≤ tick := by omega
  have ht1 : tick < K + 1 := by omega
  have ht2 : tick < K + 2 := by omega
  simp [tickCapacity, stageActive, ht, htK, h1, ht1, ht2]

theorem tickCapacity_penultimate (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c K = fun i => b i + c i := by
  funext i
  have h1 : 1 ≤ K := by omega
  simp [tickCapacity, stageActive, hK, h1]

theorem tickCapacity_last (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c (K + 1) = c := by
  funext i
  have h1 : 2 ≤ K + 1 := by omega
  simp [tickCapacity, stageActive, h1]

theorem sum_tick_minima (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
        minCapacity (fun i => b i + c i) + minCapacity c := by
  let f : ℕ → ℝ := fun tick => minCapacity (tickCapacity K a b c tick)
  have hhead : ∑ tick ∈ Finset.range 2, f tick =
      minCapacity a + minCapacity (fun i => a i + b i) := by
    simp [f, Finset.sum_range_succ, tickCapacity_first K hK,
      tickCapacity_second K hK]
  have hinterior : (∑ tick ∈ Finset.range (K - 2), f (2 + tick)) =
      (K - 2 : ℕ) * full := by
    calc
      _ = ∑ _tick ∈ Finset.range (K - 2), full := by
        apply Finset.sum_congr rfl
        intro tick htick
        have hlt := Finset.mem_range.mp htick
        dsimp [f]
        rw [tickCapacity_interior K (2 + tick) (by omega) (by omega)]
        simp [minCapacity, hfull]
      _ = _ := by simp
  have htail : (∑ tick ∈ Finset.range 2, f (K + tick)) =
      minCapacity (fun i => b i + c i) + minCapacity c := by
    simp [f, Finset.sum_range_succ, tickCapacity_penultimate K hK,
      tickCapacity_last K hK]
  change (∑ tick ∈ Finset.range (K + 2), f tick) = _
  rw [Finset.sum_range_add f K 2, htail]
  have hsplit : (∑ tick ∈ Finset.range K, f tick) =
      (∑ tick ∈ Finset.range 2, f tick) +
        ∑ tick ∈ Finset.range (K - 2), f (2 + tick) := by
    have hKsum : 2 + (K - 2) = K := by omega
    simpa only [hKsum] using Finset.sum_range_add f 2 (K - 2)
  rw [hsplit, hhead, hinterior]
  ring

theorem finite_schedule_yield (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [sum_tick_minima K hK a b c full hfull]
  exact Staggering.finite_schedule_yield a b c full K hK

theorem fixed_lot_boundary_limit {Y beta w S R : ℝ}
    (hfixed : ∀ K : ℕ, 2 ≤ K → Y - beta / (K : ℝ) + w * S / 3 ≤ R) :
    Y + w * S / 3 ≤ R := by
  by_contra hnot
  have hgap : 0 < Y + w * S / 3 - R := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max (beta / (Y + w * S / 3 - R)) (2 : ℝ))
  have hKtwo : (2 : ℝ) < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hKnat : 2 ≤ K := Nat.ofNat_le_cast.mp hKtwo.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsmall : beta / (K : ℝ) < Y + w * S / 3 - R := by
    apply (div_lt_iff₀ hKpos).2
    have hquot : beta / (Y + w * S / 3 - R) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hK
    simpa only [mul_comm] using (div_lt_iff₀ hgap).1 hquot
  have hbound := hfixed K hKnat
  linarith

end MatrixMultiplication.FiniteSchedule

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.PhysicalOrders

open Staggering

abbrev PhysicalOrder := Equiv.Perm (Fin 3)

theorem card_physical_orders : Fintype.card PhysicalOrder = 6 := by
  norm_num [PhysicalOrder, Fintype.card_perm, Nat.factorial_succ]

def placementAmount (amount : ℝ) (_phi : PhysicalOrder) : ℝ := amount / 6

theorem placementAmount_eq (amount : ℝ) (phi psi : PhysicalOrder) :
    placementAmount amount phi = placementAmount amount psi := rfl

theorem sum_placementAmount (amount : ℝ) :
    ∑ phi : PhysicalOrder, placementAmount amount phi = amount := by
  simp only [placementAmount, Finset.sum_const, Finset.card_univ,
    card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

theorem placement_has_unique_order (rho phi : PhysicalOrder) :
    ∃! sigma : PhysicalOrder, rho.trans phi = sigma := by
  refine ⟨rho.trans phi, rfl, ?_⟩
  intro sigma hsigma
  exact hsigma.symm

theorem sum_selected_placement (rho sigma : PhysicalOrder) (value : ℝ) :
    (∑ phi : PhysicalOrder, if rho.trans phi = sigma then value else 0) = value := by
  classical
  obtain ⟨phi, hphi, hunique⟩ := physical_order_unique rho sigma
  calc
    _ = ∑ psi : PhysicalOrder, if psi = phi then value else 0 := by
      apply Finset.sum_congr rfl
      intro psi _
      have hiff : rho.trans psi = sigma ↔ psi = phi := by
        constructor
        · exact hunique psi
        · rintro rfl
          exact hphi
      simp only [hiff]
    _ = value := by simp

variable {History : Type*} [Fintype History]

def aggregateCapacity (amount : History → ℝ) (capacity : History → Capacity) : Capacity :=
  fun i => ∑ h, amount h * capacity h i

def perPhysicalOrderCapacity (amount : History → ℝ) (capacity : History → Capacity)
    (priority : History → PhysicalOrder) (sigma : PhysicalOrder) : Capacity := by
  classical
  exact fun i => ∑ h, ∑ phi : PhysicalOrder,
    if (priority h).trans phi = sigma then amount h / 6 * capacity h i else 0

theorem perPhysicalOrderCapacity_apply (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) (i : Fin 3) :
    perPhysicalOrderCapacity amount capacity priority sigma i =
      (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  classical
  unfold perPhysicalOrderCapacity aggregateCapacity
  simp only [sum_selected_placement]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem perPhysicalOrderCapacity_eq (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder)
    (sigma : PhysicalOrder) :
    perPhysicalOrderCapacity amount capacity priority sigma =
      fun i => (1 / 6 : ℝ) * aggregateCapacity amount capacity i := by
  funext i
  exact perPhysicalOrderCapacity_apply amount capacity priority sigma i

theorem minCapacity_mul (a : Capacity) (r : ℝ) (hr : 0 ≤ r) :
    minCapacity (fun i => r * a i) = r * minCapacity a := by
  unfold minCapacity
  rw [mul_min_of_nonneg _ _ hr, mul_min_of_nonneg _ _ hr]

theorem sum_physical_order_minima (amount : History → ℝ)
    (capacity : History → Capacity) (priority : History → PhysicalOrder) :
    (∑ sigma : PhysicalOrder,
      minCapacity (perPhysicalOrderCapacity amount capacity priority sigma)) =
        minCapacity (aggregateCapacity amount capacity) := by
  simp_rw [perPhysicalOrderCapacity_eq,
    minCapacity_mul _ (1 / 6 : ℝ) (by norm_num)]
  simp only [Finset.sum_const, Finset.card_univ, card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

end MatrixMultiplication.PhysicalOrders

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

structure Allocation where
  mass : Fin 3 → ℚ
  positive : ∀ i, 0 < mass i
  total : ∑ i, mass i = 1

abbrev Placement := PhysicalOrders.PhysicalOrder
abbrev Initial (K : ℕ) := Fin K × Fin sortedInitial.length

def initialShape {K : ℕ} (h : Initial K) : Shape := sortedInitial.get h.2

theorem initialShape_mem {K : ℕ} (h : Initial K) : initialShape h ∈ sortedInitial :=
  List.get_mem _ _

abbrev InitialPositive (K : ℕ) := {h : Initial K // initialShape h ∈ positiveInitial}

abbrev ASplit {K : ℕ} (h : InitialPositive K) := Fin (below (initialShape h.val)).length
abbrev AfterA (K : ℕ) := Σ h : InitialPositive K, ASplit h × Bool

def aSplit {K : ℕ} (h : AfterA K) : Shape :=
  (below (initialShape h.1.val)).get h.2.1

def halfShape (parent left : Shape) (right : Bool) : Shape :=
  if right then complement parent left else left

def aShape {K : ℕ} (h : AfterA K) : Shape :=
  halfShape (initialShape h.1.val) (aSplit h) h.2.2

theorem aSplit_mem {K : ℕ} (h : AfterA K) : aSplit h ∈ below (initialShape h.1.val) :=
  List.get_mem _ _

theorem aShape_mem {K : ℕ} (h : AfterA K) : aShape h ∈ below (initialShape h.1.val) := by
  have hc := (stageA_support_complement _ h.1.property _ (aSplit_mem h)).1
  cases hh : h.2.2 <;> simp [aShape, halfShape, hh, aSplit_mem h, hc]

theorem stageA_children_size : ∀ g ∈ positiveInitial, ∀ t ∈ below g, t ∈ shapes 8 := by
  decide +kernel

theorem aShape_size {K : ℕ} (h : AfterA K) : aShape h ∈ shapes 8 :=
  stageA_children_size _ h.1.property _ (aShape_mem h)

abbrev APositive (K : ℕ) := {h : AfterA K // aShape h ∈ positiveSecond}
abbrev BSplit {K : ℕ} (h : APositive K) := Fin (below (aShape h.val)).length
abbrev AfterB (K : ℕ) := Σ h : APositive K, BSplit h × Bool

def bSplit {K : ℕ} (h : AfterB K) : Shape :=
  (below (aShape h.1.val)).get h.2.1

def bShape {K : ℕ} (h : AfterB K) : Shape :=
  halfShape (aShape h.1.val) (bSplit h) h.2.2

theorem bSplit_mem {K : ℕ} (h : AfterB K) : bSplit h ∈ below (aShape h.1.val) :=
  List.get_mem _ _

theorem bShape_mem {K : ℕ} (h : AfterB K) : bShape h ∈ below (aShape h.1.val) := by
  have hc := (stageB_support_complement _ h.1.property _ (bSplit_mem h)).1
  cases hh : h.2.2 <;> simp [bShape, halfShape, hh, bSplit_mem h, hc]

theorem stageB_children_size : ∀ t ∈ positiveSecond, ∀ u ∈ below t, u ∈ shapes 4 := by
  decide +kernel

theorem bShape_size {K : ℕ} (h : AfterB K) : bShape h ∈ shapes 4 :=
  stageB_children_size _ h.1.property _ (bShape_mem h)

abbrev BPositive (K : ℕ) := {h : AfterB K // positive (bShape h) = true}
abbrev PartC (K : ℕ) := BPositive K × Fin 3
abbrev AfterC (K : ℕ) := PartC K × Fin 4 × Bool

def cParameterParent {K : ℕ} (h : PartC K) : Shape := aShape h.1.val.1.val
def cShapeParent {K : ℕ} (h : PartC K) : Shape := bShape h.1.val

def cSplit {K : ℕ} (h : AfterC K) : Shape := stageCAtom (cShapeParent h.1) h.2.1

def cShape {K : ℕ} (h : AfterC K) : Shape :=
  halfShape (cShapeParent h.1) (cSplit h) h.2.2

theorem cShape_zero {K : ℕ} (h : AfterC K) : ∃ i, cShape h i = 0 := by
  have hg := stageC_children_geometry (cShapeParent h.1)
    (bShape_size h.1.1.val) h.1.1.property (cSplit h)
    (stageCAtom_mem _ (bShape_size h.1.1.val) h.1.1.property h.2.1)
  cases hh : h.2.2 with
  | false => simpa [cShape, halfShape, hh] using hg.2.2.1
  | true => simpa [cShape, halfShape, hh] using hg.2.2.2

instance initialPositiveFintype (K : ℕ) : Fintype (InitialPositive K) :=
  Fintype.ofFinite _

instance aPositiveFintype (K : ℕ) : Fintype (APositive K) :=
  Fintype.ofFinite _

instance bPositiveFintype (K : ℕ) : Fintype (BPositive K) :=
  Fintype.ofFinite _

inductive CanonicalHistory (K : ℕ) where
  | initial (h : Initial K)
  | afterA (h : AfterA K)
  | afterB (h : AfterB K)
  | partC (h : PartC K)
  | afterC (h : AfterC K)
  deriving Fintype

abbrev History (K : ℕ) := CanonicalHistory K × Placement

def initialAmount {K : ℕ} (h : Initial K) : ℚ := initialLaw (initialShape h)
def aAmount {K : ℕ} (h : AfterA K) : ℚ :=
  initialAmount h.1.val * stageALaw (initialShape h.1.val) (aSplit h)
def bAmount {K : ℕ} (h : AfterB K) : ℚ :=
  aAmount h.1.val * stageBLaw (aShape h.1.val) (bSplit h)
def partAmount {K : ℕ} (allocation : Allocation) (h : PartC K) : ℚ :=
  bAmount h.1.val * allocation.mass h.2
def cAmount {K : ℕ} (allocation : Allocation) (h : AfterC K) : ℚ :=
  partAmount allocation h.1 * stageCWeight (cParameterParent h.1) (cShapeParent h.1) h.2.1

def canonicalAmount {K : ℕ} (allocation : Allocation) : CanonicalHistory K → ℚ
  | .initial h => initialAmount h
  | .afterA h => aAmount h
  | .afterB h => bAmount h
  | .partC h => partAmount allocation h
  | .afterC h => cAmount allocation h

def amount {K : ℕ} (allocation : Allocation) (h : History K) : ℚ :=
  canonicalAmount allocation h.1 / 6

theorem initialAmount_pos {K : ℕ} (h : Initial K) : 0 < initialAmount h :=
  initialLaw_positive _ (initialShape_mem h)

theorem aAmount_pos {K : ℕ} (h : AfterA K) : 0 < aAmount h :=
  mul_pos (initialAmount_pos _) (stageALaw_positive _ _ (aSplit_mem h))

theorem bAmount_pos {K : ℕ} (h : AfterB K) : 0 < bAmount h :=
  mul_pos (aAmount_pos _) (stageBLaw_positive _ _ (bSplit_mem h))

theorem partAmount_pos {K : ℕ} (allocation : Allocation) (h : PartC K) :
    0 < partAmount allocation h := mul_pos (bAmount_pos _) (allocation.positive _)

theorem cAmount_nonneg {K : ℕ} (allocation : Allocation) (h : AfterC K) :
    0 ≤ cAmount allocation h :=
  mul_nonneg (partAmount_pos allocation _).le (stageCWeight_nonnegative _ _ _)

theorem amount_nonneg {K : ℕ} (allocation : Allocation) (h : History K) :
    0 ≤ amount allocation h := by
  apply div_nonneg _ (by norm_num)
  cases h.1 with
  | initial h => exact (initialAmount_pos h).le
  | afterA h => exact (aAmount_pos h).le
  | afterB h => exact (bAmount_pos h).le
  | partC h => exact (partAmount_pos allocation h).le
  | afterC h => exact cAmount_nonneg allocation h

theorem placement_amount_eq {K : ℕ} (allocation : Allocation)
    (h : CanonicalHistory K) (phi psi : Placement) :
    amount allocation (h, phi) = amount allocation (h, psi) := rfl

theorem sum_placement_amount {K : ℕ} (allocation : Allocation) (h : CanonicalHistory K) :
    ∑ phi : Placement, amount allocation (h, phi) = canonicalAmount allocation h := by
  simp only [amount, Finset.sum_const, Finset.card_univ,
    PhysicalOrders.card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

theorem initial_amount_sum (K : ℕ) (j : Fin K) :
    ∑ g : Fin sortedInitial.length, initialAmount (j, g) = 1 := by
  change (∑ g : Fin sortedInitial.length, initialLaw sortedInitial[g.val]) = 1
  rw [Fin.sum_univ_fun_getElem]
  exact initialLaw_normalized

theorem root_mass_sum_lot {K : ℕ} (allocation : Allocation) (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      amount allocation (.initial (j, g), phi)) = 1 := by
  simp only [sum_placement_amount, canonicalAmount]
  exact initial_amount_sum K j

theorem a_transition {K : ℕ} (h : InitialPositive K) (right : Bool) :
    ∑ k : ASplit h, aAmount ⟨h, k, right⟩ = initialAmount h.val := by
  change (∑ k : ASplit h, initialAmount h.val *
    stageALaw (initialShape h.val) (below (initialShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageALaw_normalized _ h.property, mul_one]

theorem b_transition {K : ℕ} (h : APositive K) (right : Bool) :
    ∑ k : BSplit h, bAmount ⟨h, k, right⟩ = aAmount h.val := by
  change (∑ k : BSplit h, aAmount h.val *
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val]) = _
  rw [← Finset.mul_sum, Fin.sum_univ_fun_getElem,
    stageBLaw_normalized _ h.property, mul_one]

theorem part_transition {K : ℕ} (allocation : Allocation) (h : BPositive K) :
    ∑ i : Fin 3, partAmount allocation (h, i) = bAmount h.val := by
  simp only [partAmount, ← Finset.mul_sum, allocation.total, mul_one]

theorem c_transition {K : ℕ} (allocation : Allocation) (h : PartC K) (right : Bool) :
    ∑ k : Fin 4, cAmount allocation (h, k, right) = partAmount allocation h := by
  simp only [cAmount, ← Finset.mul_sum, stageCWeight_normalized, mul_one]

def population {K : ℕ} (allocation : Allocation) (dilation : ℕ) : History K → ℕ :=
  AllFieldPopulationCounts.count (amount allocation) dilation

def populationLength {K : ℕ} (allocation : Allocation) (dilation : ℕ) : ℕ :=
  AllFieldPopulationCounts.blockLength (amount (K := K) allocation) dilation

theorem population_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ) (h : History K) :
    (population allocation dilation h : ℚ) =
      (populationLength (K := K) allocation dilation : ℚ) * amount allocation h :=
  AllFieldPopulationCounts.count_cast_blockLength _ (amount_nonneg allocation) dilation h

theorem population_zero_iff {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (h : History K) :
    population allocation dilation h = 0 ↔ amount allocation h = 0 :=
  AllFieldPopulationCounts.count_zero_iff _ (amount_nonneg allocation) hd h

theorem initial_population_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      population allocation dilation (.initial (j, g), phi)) =
        populationLength (K := K) allocation dilation := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, ← Finset.mul_sum,
    root_mass_sum_lot allocation j, mul_one]

theorem a_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (right : Bool) (phi : Placement) :
    (∑ k : ASplit h, population allocation dilation (.afterA ⟨h, k, right⟩, phi)) =
      population allocation dilation (.initial h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, a_transition]

theorem b_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (right : Bool) (phi : Placement) :
    (∑ k : BSplit h, population allocation dilation (.afterB ⟨h, k, right⟩, phi)) =
      population allocation dilation (.afterA h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, b_transition]

theorem part_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    (∑ i : Fin 3, population allocation dilation (.partC (h, i), phi)) =
      population allocation dilation (.afterB h.val, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, part_transition]

theorem c_population_transition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (right : Bool) (phi : Placement) :
    (∑ k : Fin 4, population allocation dilation (.afterC (h, k, right), phi)) =
      population allocation dilation (.partC h, phi) := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, amount, canonicalAmount,
    ← Finset.mul_sum, ← Finset.sum_div, c_transition]

theorem a_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (k : ASplit h) (phi : Placement) :
    population allocation dilation (.afterA ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterA ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem b_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (k : BSplit h) (phi : Placement) :
    population allocation dilation (.afterB ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterB ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem c_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (k : Fin 4) (phi : Placement) :
    population allocation dilation (.afterC (h, k, false), phi) =
      population allocation dilation (.afterC (h, k, true), phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialAncestor {K : ℕ} : CanonicalHistory K → Initial K
  | .initial h => h
  | .afterA h => h.1.val
  | .afterB h => h.1.val.1.val
  | .partC h => h.1.val.1.val.1.val
  | .afterC h => h.1.1.val.1.val.1.val

def ancestrySplits {K : ℕ} : CanonicalHistory K → List (Shape × Bool)
  | .initial _ => []
  | .afterA h => [(aSplit h, h.2.2)]
  | .afterB h => [(aSplit h.1.val, h.1.val.2.2), (bSplit h, h.2.2)]
  | .partC h => [(aSplit h.1.val.1.val, h.1.val.1.val.2.2),
      (bSplit h.1.val, h.1.val.2.2)]
  | .afterC h => [(aSplit h.1.1.val.1.val, h.1.1.val.1.val.2.2),
      (bSplit h.1.1.val, h.1.1.val.2.2), (cSplit h, h.2.2)]

def ancestrySubdivisions {K : ℕ} : CanonicalHistory K → List ℕ
  | .initial _ | .afterA _ | .afterB _ => []
  | .partC h => [h.2.val]
  | .afterC h => [h.1.2.val]

def historyKey {K : ℕ} (h : History K) : JointPopulation.HistoryKey where
  lot := (initialAncestor h.1).1.val
  initialShape := initialShape (initialAncestor h.1)
  physicalPlacement := h.2
  parentSplits := ancestrySplits h.1
  subdivisions := ancestrySubdivisions h.1

theorem placement_preserved {K : ℕ} (h : CanonicalHistory K) (phi psi : Placement)
    (heq : historyKey (h, phi) = historyKey (h, psi)) : phi = psi :=
  congrArg JointPopulation.HistoryKey.physicalPlacement heq

inductive Work (K : ℕ) where
  | stageA (h : InitialPositive K)
  | stageB (h : APositive K)
  | stageC (h : PartC K)
  deriving Fintype

def Work.source {K : ℕ} : Work K → CanonicalHistory K
  | .stageA h => .initial h.val
  | .stageB h => .afterA h.val
  | .stageC h => .partC h

def Work.stage {K : ℕ} : Work K → Fin 3
  | .stageA _ => 0
  | .stageB _ => 1
  | .stageC _ => 2

def Work.lot {K : ℕ} (w : Work K) : Fin K := (initialAncestor w.source).1

def Work.halfLength {K : ℕ} : Work K → ℕ
  | .stageA _ => 4
  | .stageB _ => 2
  | .stageC _ => 1

def Work.parentShape {K : ℕ} : Work K → Shape
  | .stageA h => initialShape h.val
  | .stageB h => aShape h.val
  | .stageC h => cShapeParent h

def Work.Branch {K : ℕ} : Work K → Type
  | .stageA h => ASplit h
  | .stageB h => BSplit h
  | .stageC _ => Fin 4

instance {K : ℕ} (w : Work K) : Fintype w.Branch := by
  cases w <;> dsimp [Work.Branch] <;> infer_instance

def Work.child {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) : CanonicalHistory K :=
  match w with
  | .stageA h => .afterA ⟨h, b, right⟩
  | .stageB h => .afterB ⟨h, b, right⟩
  | .stageC h => .afterC (h, b, right)

def Work.splitShape {K : ℕ} (w : Work K) (b : w.Branch) : Shape :=
  match w with
  | .stageA h => aSplit ⟨h, b, false⟩
  | .stageB h => bSplit ⟨h, b, false⟩
  | .stageC h => cSplit (h, b, false)

abbrev PlacedWork (K : ℕ) := Work K × Placement
abbrev Active (K tick : ℕ) := {w : PlacedWork K //
  FiniteSchedule.lotTick w.1.lot w.1.stage = tick}

theorem active_tick_lt {K tick : ℕ} (h : Active K tick) : tick < K + 2 := by
  rw [← h.property]
  exact FiniteSchedule.lotTick_lt h.val.1.lot h.val.1.stage

def branchPopulation {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) : ℕ :=
  population allocation dilation (w.1.child b false, w.2)

theorem branchPopulation_half {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    population allocation dilation (w.1.child b right, w.2) =
      branchPopulation allocation dilation w b := by
  rcases w with ⟨w, phi⟩
  cases right with
  | false => rfl
  | true =>
      cases w with
      | stageA h => exact (a_half_counts_eq allocation dilation h b phi).symm
      | stageB h => exact (b_half_counts_eq allocation dilation h b phi).symm
      | stageC h => exact (c_half_counts_eq allocation dilation h b phi).symm

theorem branchPopulation_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (∑ b : w.1.Branch, branchPopulation allocation dilation w b) =
      population allocation dilation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact a_population_transition allocation dilation h false phi
  | stageB h => exact b_population_transition allocation dilation h false phi
  | stageC h => exact c_population_transition allocation dilation h false phi

def terminal {K : ℕ} : CanonicalHistory K → Prop
  | .initial h => initialShape h ∉ positiveInitial
  | .afterA h => aShape h ∉ positiveSecond
  | .afterB h => positive (bShape h) ≠ true
  | .partC _ => False
  | .afterC _ => True

def resident {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial → tick ≤ h.1.val
  | .afterA h => h.1.val.1.val + 1 ≤ tick ∧
      (aShape h ∈ positiveSecond → tick ≤ h.1.val.1.val + 1)
  | .afterB h => h.1.val.1.val.1.val + 2 ≤ tick ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC h => h.1.1.val.1.val.1.val.1.val + 3 ≤ tick

abbrev State (K tick : ℕ) := {h : History K // resident tick h.1}

theorem terminal_carries {K tick : ℕ} (h : CanonicalHistory K)
    (hr : resident tick h) (ht : terminal h) : resident (tick + 1) h := by
  cases h with
  | initial h => exact fun hp => False.elim (ht hp)
  | afterA h => exact ⟨by have := hr.1; omega, fun hp => False.elim (ht hp)⟩
  | afterB h => exact ⟨by have := hr.1; omega, hr.2⟩
  | partC h => exact False.elim ht
  | afterC h => dsimp [resident] at hr ⊢; omega

theorem work_source_resident {K : ℕ} (w : Work K) :
    resident (FiniteSchedule.lotTick w.lot w.stage) w.source := by
  cases w with
  | stageA h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageB h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageC h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]

theorem a_child_resident {K : ℕ} (h : InitialPositive K) (b : ASplit h) (right : Bool) :
    resident (h.val.1.val + 1) (.afterA ⟨h, b, right⟩) := by
  simp [resident]

theorem c_child_resident {K : ℕ} (h : PartC K) (b : Fin 4) (right : Bool) :
    resident ((Work.stageC h).lot.val + 3) (.afterC (h, b, right)) := by
  simp [resident, Work.lot, Work.source, initialAncestor]

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def shapeCounts {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) : ℕ :=
  ∑ i, if code i = u then weight i else 0

theorem shapeCounts_sum {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) : ∑ u, shapeCounts code weight u = ∑ i, weight i := by
  unfold shapeCounts
  rw [Finset.sum_comm]
  simp

theorem shapeCounts_positive {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) (hu : 0 < shapeCounts code weight u) :
    ∃ i, code i = u ∧ 0 < weight i := by
  by_contra hn
  have hz : shapeCounts code weight u = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with heq
    · by_contra hne
      exact hn ⟨i, heq, Nat.pos_of_ne_zero hne⟩
    · rfl
  omega

theorem shapeCounts_at {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (hi : Function.Injective code) (i : I) :
    shapeCounts code weight (code i) = weight i := by
  unfold shapeCounts
  simp only [hi.eq_iff]
  simp

theorem Work.parentShape_spec {K : ℕ} (w : Work K) :
    ShapeBounded w.parentShape ∧ shapeTotal w.parentShape = 4 * w.halfLength := by
  cases w with
  | stageA h => exact positiveInitial_shape_spec _ h.property
  | stageB h => exact positiveSecond_shape_spec _ h.property
  | stageC h =>
      exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
        mem_shapes_total (bShape_size h.1.val)⟩

theorem Work.splitShape_spec {K : ℕ} (w : Work K) (b : w.Branch) :
    ShapeBounded (w.splitShape b) ∧ shapeTotal (w.splitShape b) = 2 * w.halfLength := by
  cases w with
  | stageA h => exact stageA_shape_spec _ _ h.property (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact stageB_shape_spec _ _ h.property (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact stageC_shape_spec _ (bShape_size h.1.val) h.1.property b

theorem Work.splitShape_le {K : ℕ} (w : Work K) (b : w.Branch) :
    ∀ i, w.splitShape b i ≤ w.parentShape i := by
  cases w with
  | stageA h => exact below_le (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact below_le (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact below_le (stageCAtom_mem _ (bShape_size h.1.val) h.1.property b)

theorem Work.splitShape_injective {K : ℕ} (w : Work K) :
    Function.Injective w.splitShape := by
  cases w with
  | stageA h => exact stageA_get_injective _ h.property
  | stageB h => exact stageB_get_injective _ h.property
  | stageC h => exact stageCAtom_injective _ (bShape_size h.1.val) h.1.property

def branchShape {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) : JointPopulation.Shape :=
  encodePhysicalShape w.2 (w.1.splitShape b) (w.1.splitShape_spec b).1

theorem branchShape_injective {K : ℕ} (w : PlacedWork K) :
    Function.Injective (branchShape w) := by
  intro a b hab
  exact w.1.splitShape_injective (encodePhysicalShape_inj w.2 hab)

def jointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : JointPopulation.Shape → ℕ :=
  shapeCounts (branchShape w) (branchPopulation allocation dilation w)

def activeCounts {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) : JointPopulation.Shape → ℕ := jointCounts allocation dilation h.val

def activeParentShape {K tick : ℕ} (h : Active K tick) : Shape :=
  physicalShape h.val.2 h.val.1.parentShape

def activeHalfLength {K tick : ℕ} (h : Active K tick) : ℕ := h.val.1.halfLength

theorem jointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : ∑ u, jointCounts allocation dilation w u =
      population allocation dilation (w.1.source, w.2) := by
  rw [jointCounts, shapeCounts_sum, branchPopulation_sum]

theorem jointCounts_at {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    jointCounts allocation dilation w (branchShape w b) =
      branchPopulation allocation dilation w b :=
  shapeCounts_at _ _ (branchShape_injective w) b

theorem jointCounts_support_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) :
    u.1.val + u.2.1.val + u.2.2.val = 2 * w.1.halfLength := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (w.1.splitShape_spec b).2

theorem jointCounts_support_le {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (s : Fin 3) :
    (JointPopulation.shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

def shapePositionMap {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) →
      (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :=
  fun p => ⟨branchShape w p.1,
    ⟨p.2.val, by rw [jointCounts_at]; exact p.2.isLt⟩⟩

theorem shapePositionMap_injective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Injective (shapePositionMap allocation dilation w) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ heq
  have hbc : b = c := branchShape_injective w (congrArg Sigma.fst heq)
  subst c
  have hij : i.val = j.val := congrArg (fun p => p.2.val) heq
  have : i = j := Fin.ext hij
  subst j
  rfl

theorem shapePositionMap_surjective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Surjective (shapePositionMap allocation dilation w) := by
  rintro ⟨u, i⟩
  obtain ⟨b, heq, hb⟩ := shapeCounts_positive _ _ u (Nat.zero_lt_of_lt i.isLt)
  subst u
  refine ⟨⟨b, ⟨i.val, ?_⟩⟩, ?_⟩
  · simpa only [jointCounts_at] using i.isLt
  · rfl

def branchPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) ≃
      (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) :=
  (Equiv.ofBijective (shapePositionMap allocation dilation w)
    ⟨shapePositionMap_injective allocation dilation w,
      shapePositionMap_surjective allocation dilation w⟩).symm

@[simp] theorem branchPositionEquiv_shape {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K)
    (p : Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :
    branchShape w (branchPositionEquiv allocation dilation w p).1 = p.1 := by
  exact congrArg Sigma.fst ((branchPositionEquiv allocation dilation w).symm_apply_apply p)

def rootShape {K : ℕ} (h : Initial K) (phi : Placement) : JointPopulation.Shape :=
  encodePhysicalShape phi (initialShape h) (root_shape_spec _ (initialShape_mem h)).1

def initialJointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : JointPopulation.Shape → ℕ :=
  shapeCounts (fun p : Fin sortedInitial.length × Placement => rootShape (j, p.1) p.2)
    (fun p => population allocation dilation (.initial (j, p.1), p.2))

theorem initialJointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : ∑ u, initialJointCounts allocation dilation j u =
      populationLength (K := K) allocation dilation := by
  rw [initialJointCounts, shapeCounts_sum, Fintype.sum_prod_type]
  exact initial_population_sum allocation dilation j

theorem initialJointCounts_support {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape)
    (hu : 0 < initialJointCounts allocation dilation j u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  obtain ⟨p, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (root_shape_spec _ (initialShape_mem _)).2

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

def priorityPermutation (k : Fin 6) : Placement :=
  (Matrix.vecCons (Equiv.refl (Fin 3)) (Matrix.vecCons (Equiv.swap 1 2) (Matrix.vecCons (Equiv.swap 0 1) (Matrix.vecCons ((Equiv.swap 0 1).trans (Equiv.swap 0 2)) (Matrix.vecCons ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) (Matrix.vecCons (Equiv.swap 0 2) Matrix.vecEmpty)))))) k

def PriorityLexLE (rho sigma : Placement) : Prop :=
  rho 0 < sigma 0 ∨ rho 0 = sigma 0 ∧
    (rho 1 < sigma 1 ∨ rho 1 = sigma 1 ∧ rho 2 ≤ sigma 2)

instance (rho sigma : Placement) : Decidable (PriorityLexLE rho sigma) :=
  inferInstanceAs (Decidable (rho 0 < sigma 0 ∨ rho 0 = sigma 0 ∧
    (rho 1 < sigma 1 ∨ rho 1 = sigma 1 ∧ rho 2 ≤ sigma 2)))

theorem priorityPermutation_surjective : Function.Surjective priorityPermutation := by
  decide +kernel

theorem priorityPermutation_order : ∀ j k : Fin 6,
    PriorityLexLE (priorityPermutation j) (priorityPermutation k) ↔ j ≤ k := by
  decide +kernel

def stageBRepresentatives : List Shape :=
  [shape 1 1 6, shape 1 2 5, shape 1 3 4, shape 2 2 4, shape 3 2 3]

def readInPriority (t : Shape) (rho : Placement) : Shape := fun i => t (rho i)

def stageBPriorityIndex (t : Shape) : Fin 6 :=
  ((List.finRange 6).find? fun k =>
    stageBRepresentatives.contains (readInPriority t (priorityPermutation k))).getD 0

def stageBPriority (t : Shape) : Placement := priorityPermutation (stageBPriorityIndex t)

theorem stageBPriority_finite_spec : ∀ t ∈ positiveSecond,
    stageBRepresentatives.contains (readInPriority t (stageBPriority t)) = true ∧
      ∀ k : Fin 6,
        stageBRepresentatives.contains (readInPriority t (priorityPermutation k)) = true →
          PriorityLexLE (stageBPriority t) (priorityPermutation k) := by
  decide +kernel

theorem stageBPriority_reads_representative (t : Shape) (ht : t ∈ positiveSecond) :
    readInPriority t (stageBPriority t) ∈ stageBRepresentatives := by
  simpa using (stageBPriority_finite_spec t ht).1

theorem stageBPriority_lex_first (t : Shape) (ht : t ∈ positiveSecond)
    (rho : Placement) (hrho : readInPriority t rho ∈ stageBRepresentatives) :
    PriorityLexLE (stageBPriority t) rho := by
  obtain ⟨k, rfl⟩ := priorityPermutation_surjective rho
  exact (stageBPriority_finite_spec t ht).2 k (by simpa using hrho)

theorem stageBPriority_233 :
    stageBPriority (shape 2 3 3) 0 = 1 ∧
      stageBPriority (shape 2 3 3) 1 = 0 ∧
        stageBPriority (shape 2 3 3) 2 = 2 := by
  decide +kernel

def cPriorityIndex : Fin 3 → Fin 3 → Fin 6 :=
  (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (2) (Matrix.vecCons (3) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (2) (Matrix.vecCons (0) (Matrix.vecCons (1) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (4) (Matrix.vecCons (1) (Matrix.vecCons (0) Matrix.vecEmpty)))) Matrix.vecEmpty)))

def stageCPriorityLabel (distinguished part : Fin 3) : Placement :=
  priorityPermutation (cPriorityIndex distinguished part)

theorem stageCPriorityLabel_at_part : ∀ distinguished part : Fin 3,
    stageCPriorityLabel distinguished part part = distinguished := by
  decide +kernel

theorem stageCPriorityLabel_remaining_order : ∀ distinguished part j k : Fin 3,
    j ≠ part → k ≠ part → j < k →
      stageCPriorityLabel distinguished part j < stageCPriorityLabel distinguished part k := by
  decide +kernel

def cPriority {K : ℕ} (h : PartC K) : Placement :=
  stageCPriorityLabel (stageCDistinguished (cShapeParent h)) h.2

theorem cPriority_at_part {K : ℕ} (h : PartC K) :
    cPriority h h.2 = stageCDistinguished (cShapeParent h) :=
  stageCPriorityLabel_at_part _ _

theorem cPriority_at_part_two {K : ℕ} (h : PartC K) :
    cShapeParent h (cPriority h h.2) = 2 := by
  rw [cPriority_at_part]
  exact (stageCDistinguished_spec (cShapeParent h)
    (bShape_size h.1.val) h.1.property).1

theorem cPriority_remaining_order {K : ℕ} (h : PartC K)
    (j k : Fin 3) (hj : j ≠ h.2) (hk : k ≠ h.2) (hjk : j < k) :
    cPriority h j < cPriority h k :=
  stageCPriorityLabel_remaining_order _ _ _ _ hj hk hjk

def Work.priority {K : ℕ} : Work K → Placement
  | .stageA _ => Equiv.refl (Fin 3)
  | .stageB h => stageBPriority (aShape h.val)
  | .stageC h => cPriority h

@[simp] theorem Work.priority_stageA {K : ℕ} (h : InitialPositive K) :
    (Work.stageA h).priority = Equiv.refl (Fin 3) := rfl

theorem Work.priority_stageB {K : ℕ} (h : APositive K) :
    readInPriority (Work.stageB h).parentShape (Work.stageB h).priority ∈
      stageBRepresentatives := stageBPriority_reads_representative _ h.property

theorem Work.priority_stageC {K : ℕ} (h : PartC K) :
    (Work.stageC h).priority h.2 = stageCDistinguished (cShapeParent h) :=
  cPriority_at_part h

def PlacedWork.physicalOrder {K : ℕ} (w : PlacedWork K) : Placement :=
  w.1.priority.trans w.2

theorem work_placement_for_order_unique {K : ℕ} (w : Work K) (sigma : Placement) :
    ∃! phi : Placement, PlacedWork.physicalOrder (w, phi) = sigma :=
  Staggering.physical_order_unique w.priority sigma

abbrev CanonicalActive (K tick : ℕ) :=
  {w : Work K // FiniteSchedule.lotTick w.lot w.stage = tick}

abbrev ActiveOrder (K tick : ℕ) (sigma : Placement) :=
  {w : Active K tick // w.val.physicalOrder = sigma}

def canonicalActiveEquivOrder (K tick : ℕ) (sigma : Placement) :
    CanonicalActive K tick ≃ ActiveOrder K tick sigma where
  toFun w := ⟨⟨(w.val, w.val.priority.symm.trans sigma), w.property⟩, by
    change w.val.priority.trans (w.val.priority.symm.trans sigma) = sigma
    ext i
    simp⟩
  invFun w := ⟨w.val.val.1, w.val.property⟩
  left_inv _ := rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hw : w.val.val.1.priority.trans w.val.val.2 = sigma := w.property
      apply Equiv.ext
      intro i
      have hh := Equiv.congr_fun hw (w.val.val.1.priority.symm i)
      simpa using hh.symm

def workAmount {K : ℕ} (allocation : Allocation) (w : Work K) : ℝ :=
  canonicalAmount allocation w.source

def activeAggregateCapacity {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) : Staggering.Capacity :=
  PhysicalOrders.aggregateCapacity (fun w : CanonicalActive K tick => workAmount allocation w.val)
    (fun w => capacity w.val)

def physicalTickCapacity {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) : Staggering.Capacity :=
  fun i => ∑ w : CanonicalActive K tick, ∑ phi : Placement,
    if PlacedWork.physicalOrder (w.val, phi) = sigma then
      (amount allocation (w.val.source, phi) : ℝ) * capacity w.val i else 0

theorem physicalTickCapacity_eq_partition {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) :
    physicalTickCapacity allocation tick capacity sigma =
      PhysicalOrders.perPhysicalOrderCapacity
        (fun w : CanonicalActive K tick => workAmount allocation w.val)
        (fun w => capacity w.val) (fun w => w.val.priority) sigma := by
  funext i
  simp only [physicalTickCapacity, PhysicalOrders.perPhysicalOrderCapacity,
    PlacedWork.physicalOrder, amount, workAmount, Rat.cast_div, Rat.cast_ofNat]

theorem physicalTickCapacity_eq_sixth {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) (sigma : Placement) :
    physicalTickCapacity allocation tick capacity sigma =
      fun i => (1 / 6 : ℝ) * activeAggregateCapacity allocation tick capacity i := by
  rw [physicalTickCapacity_eq_partition]
  exact PhysicalOrders.perPhysicalOrderCapacity_eq _ _ _ _

theorem sum_physicalTick_minima {K : ℕ} (allocation : Allocation) (tick : ℕ)
    (capacity : Work K → Staggering.Capacity) :
    (∑ sigma : Placement, Staggering.minCapacity
      (physicalTickCapacity allocation tick capacity sigma)) =
        Staggering.minCapacity (activeAggregateCapacity allocation tick capacity) := by
  simp_rw [physicalTickCapacity_eq_partition]
  exact PhysicalOrders.sum_physical_order_minima _ _ _

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def Work.Statistic {K : ℕ} : Work K → Type
  | .stageA _ => PairSlot
  | .stageB _ => Fin 6
  | .stageC _ => PUnit

instance {K : ℕ} (w : Work K) : Fintype w.Statistic := by
  cases w <;> dsimp [Work.Statistic] <;> infer_instance

instance {K : ℕ} (w : Work K) : DecidableEq w.Statistic := Classical.decEq _

def Work.statistic {K : ℕ} (w : Work K) : Raw w.halfLength → w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.fourStatistic
  | .stageB _ => CWCompleteStatistics.twoStatistic
  | .stageC _ => fun _ => PUnit.unit

def Work.statisticWeight {K : ℕ} (w : Work K) : w.Statistic → ℕ :=
  match w with
  | .stageA _ => fun a => AllFieldParameters.statisticWeight a.1 +
      AllFieldParameters.statisticWeight a.2
  | .stageB _ => AllFieldParameters.statisticWeight
  | .stageC _ => fun _ => 0

theorem Work.statistic_weight {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (x : Raw w.halfLength) : CWStrands.weight x = w.statisticWeight (w.statistic x) := by
  cases w with
  | stageA h => exact CWCompleteStatistics.four_weight x
  | stageB h => exact CWCompleteStatistics.two_weight x
  | stageC h => exact False.elim (hsharing rfl)

def Work.childLaw {K : ℕ} (w : Work K) (u : Shape) (side : Fin 3) :
    w.Statistic → ℚ :=
  match w with
  | .stageA _ => halfLaw u side
  | .stageB h => littleLaw (aShape h.val) u side
  | .stageC _ => fun _ => 1

theorem Work.childLaw_nonnegative {K : ℕ} (w : Work K) (u : Shape)
    (side : Fin 3) (a : w.Statistic) : 0 ≤ w.childLaw u side a := by
  cases w with
  | stageA h => exact halfLaw_nonnegative u side a
  | stageB h => exact littleLaw_nonnegative (aShape h.val) u side a
  | stageC h => exact zero_le_one

theorem Work.childLaw_normalized {K : ℕ} (w : Work K) (u : Shape)
    (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3) :
    ∑ a : w.Statistic, w.childLaw u side a = 1 := by
  cases w with
  | stageA h => exact halfLaw_normalized u hu side
  | stageB h => exact littleLaw_normalized (aShape h.val) u side
  | stageC h =>
      change (∑ _ : PUnit, (1 : ℚ)) = 1
      simp

theorem Work.childLaw_outside_support {K : ℕ} (w : Work K) (hsharing : w.stage ≠ 2)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength)) (side : Fin 3)
    (a : w.Statistic) (ha : w.statisticWeight a ≠ u side) : w.childLaw u side a = 0 := by
  cases w with
  | stageA h => exact halfLaw_outside_support u hu side a ha
  | stageB h =>
      have hbound : u side < 5 :=
        lt_of_le_of_lt (mem_shapes_bound hu side) (by norm_num [Work.halfLength])
      exact littleLaw_outside_support (aShape h.val) u side hbound a ha
  | stageC h => exact False.elim (hsharing rfl)

def canonicalChildShape {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape) : Shape :=
  fun i => decodeShape u (w.2 i)

@[simp] theorem canonicalChildShape_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) : canonicalChildShape w (branchShape w b) = w.1.splitShape b := by
  funext i
  simp [canonicalChildShape, branchShape, physicalShape]

theorem Work.halfShape_mem {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) :
    halfShape w.parentShape (w.splitShape b) right ∈ shapes (2 * w.halfLength) := by
  cases w with
  | stageA h => exact aShape_size ⟨h, b, right⟩
  | stageB h => exact bShape_size ⟨h, b, right⟩
  | stageC h =>
      have hi := stageCAtom_mem (cShapeParent h) (bShape_size h.1.val) h.1.property b
      have hs := stageC_children_geometry (cShapeParent h)
        (bShape_size h.1.val) h.1.property (stageCAtom (cShapeParent h) b)
        hi
      have ht : shapeTotal (cShapeParent h) = 4 := mem_shapes_total (bShape_size h.1.val)
      cases right
      · change stageCAtom (cShapeParent h) b ∈ shapes 2
        simpa only [ht, Nat.reduceDiv] using below_mem_shapes hi
      · change complement (cShapeParent h) (stageCAtom (cShapeParent h) b) ∈ shapes 2
        simpa only [ht, Nat.reduceDiv] using below_mem_shapes hs.1

def placedChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (right : Bool) : w.1.Statistic → ℚ :=
  w.1.childLaw (halfShape w.1.parentShape (canonicalChildShape w u) right)
    (w.2.symm side)

def childLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side false

def rightChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side true

@[simp] theorem placedChildLawRat_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (right : Bool) :
    placedChildLawRat w (branchShape w b) side right =
      w.1.childLaw (halfShape w.1.parentShape (w.1.splitShape b) right)
        (w.2.symm side) := by
  simp only [placedChildLawRat, canonicalChildShape_branchShape]

theorem placedChildLawRat_nonnegative {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (side : Fin 3) (right : Bool) (a : w.1.Statistic) :
    0 ≤ placedChildLawRat w u side right a :=
  w.1.childLaw_nonnegative _ _ a

theorem placedChildLawRat_normalized_of_pos {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) (side : Fin 3) (right : Bool) :
    ∑ a : w.1.Statistic, placedChildLawRat w u side right a = 1 := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  simp only [placedChildLawRat_branchShape]
  exact w.1.childLaw_normalized _ (w.1.halfShape_mem b right) _

def childLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := childLawRat w u side a

def rightChildLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := rightChildLawRat w u side a

abbrev ActiveStatistic {K tick : ℕ} (h : Active K tick) := h.val.1.Statistic

def activeStatistic {K tick : ℕ} (h : Active K tick) :
    Raw (activeHalfLength h) → ActiveStatistic h := h.val.1.statistic

def leftChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  childLaw c.1.val c.2 side

def rightClassChildLaw {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) : ActiveStatistic c.1 → ℝ :=
  rightChildLaw c.1.val c.2 side

theorem leftChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ leftChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side false a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side false a

theorem rightClassChildLaw_nonnegative {K tick : ℕ} (side : Fin 3)
    (c : Active K tick × JointPopulation.Shape) (a : ActiveStatistic c.1) :
    0 ≤ rightClassChildLaw side c a := by
  change (0 : ℝ) ≤ (placedChildLawRat c.1.val c.2 side true a : ℝ)
  exact_mod_cast placedChildLawRat_nonnegative c.1.val c.2 side true a

theorem leftChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, leftChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side false a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side false

theorem rightClassChildLaw_normalized_of_pos {K tick : ℕ} (allocation : Allocation)
    (dilation : ℕ) (side : Fin 3) (c : Active K tick × JointPopulation.Shape)
    (hc : 0 < activeCounts allocation dilation c.1 c.2) :
    ∑ a : ActiveStatistic c.1, rightClassChildLaw side c a = 1 := by
  change (∑ a : c.1.val.1.Statistic,
    (placedChildLawRat c.1.val c.2 side true a : ℝ)) = 1
  exact_mod_cast placedChildLawRat_normalized_of_pos allocation dilation
    c.1.val c.2 hc side true

end MatrixMultiplication.AllFieldHistory

namespace MatrixMultiplication.AllFieldHistoryChildLaws

open AllFieldHistory
open scoped BigOperators

abbrev Statistic {K tick : ℕ} (h : Active K tick) := ActiveStatistic h

abbrev statistic {K tick : ℕ} (h : Active K tick) :
    CWWindowedLeaves.Raw (activeHalfLength h) → Statistic h := activeStatistic h

abbrev leftLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := childLaw h.val u side

abbrev rightLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := rightChildLaw h.val u side

theorem leftLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ leftLaw h u side a :=
  leftChildLaw_nonnegative side (h, u) a

theorem rightLaw_nonnegative {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) (a : Statistic h) : 0 ≤ rightLaw h u side a :=
  rightClassChildLaw_nonnegative side (h, u) a

theorem leftLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, leftLaw h u side a = 1 :=
  leftChildLaw_normalized_of_pos allocation dilation side (h, u) hu

theorem rightLaw_normalized {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation dilation h u) (side : Fin 3) :
    ∑ a : Statistic h, rightLaw h u side a = 1 :=
  rightClassChildLaw_normalized_of_pos allocation dilation side (h, u) hu

theorem singleton_typeWindow {P : Type*} [Fintype P] [DecidableEq P] [Nonempty P]
    (η : ℝ) (hη : 0 ≤ η) (w : P → PUnit) :
    InheritedMasks.typeWindow (fun _ : PUnit => 1) η w := by
  intro a
  have hcount : MatrixMultiplication.Foundation.wordPopulation w a = Fintype.card P := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim _ _⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  have hpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  simpa only [InheritedMasks.empiricalLaw, hcount, div_self (ne_of_gt hpos),
    sub_self, abs_zero] using hη

end MatrixMultiplication.AllFieldHistoryChildLaws

end
end

end MatrixAllFields

end OAI
