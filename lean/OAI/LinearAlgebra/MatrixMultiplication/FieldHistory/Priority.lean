import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Schedule

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

def priorityPermutation (k : Fin 6) : Placement :=
  ![Equiv.refl (Fin 3), Equiv.swap 1 2, Equiv.swap 0 1,
    (Equiv.swap 0 1).trans (Equiv.swap 0 2),
    (Equiv.swap 0 2).trans (Equiv.swap 0 1), Equiv.swap 0 2] k

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
  ![![0, 2, 3], ![2, 0, 1], ![4, 1, 0]]

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

end OAI
