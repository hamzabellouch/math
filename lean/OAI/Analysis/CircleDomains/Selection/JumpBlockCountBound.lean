import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes

namespace OAI

/-! The positive toll floor gives one finite code space for every chain
under a fixed budget, independent of its original code bound. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem exists_uniform_block_pattern_bound
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ)
    (hr : ENNReal.ofReal δ ≤ r) (hT : ∀i, ENNReal.ofReal δ ≤ T i)
    {M : ℝ≥0∞} (hM : M < ∞) :
    ∃N : ℕ, ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      jumpBlockCost d B g m r τ T P Z ≤ M →
      P.1.val ≤ N ∧ ∀b, (P.2.2 b).val ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_jump_count_bound hδ hM
  refine ⟨N, fun n P Z hc => ⟨?_, fun b => ?_⟩⟩
  · apply hN P.1.val (fun i => T (P.2.1 i)) (fun i => hT (P.2.1 i))
    exact (le_add_left le_rfl).trans hc
  · apply hN (P.2.2 b).val (fun i => fixedWidthJumpToll B m r τ (Z.disks b i))
      (fun i => hr.trans (fixedWidthJumpToll_ge_floor B m r τ (Z.disks b i)))
    have hsingle : (∑j, physicalTollCost d g m (Z.paths b j).1) +
        (∑i, fixedWidthJumpToll B m r τ (Z.disks b i)) ≤
        ∑a, ((∑j, physicalTollCost d g m (Z.paths a j).1) +
          (∑i, fixedWidthJumpToll B m r τ (Z.disks a i))) :=
      Finset.single_le_sum
        (f := fun a : Fin (P.1.val+1) => (∑j, physicalTollCost d g m (Z.paths a j).1) +
          (∑i, fixedWidthJumpToll B m r τ (Z.disks a i)))
        (fun _ _ => zero_le) (Finset.mem_univ b)
    exact (le_add_left le_rfl).trans (hsingle.trans ((le_add_right le_rfl).trans hc))

def reboundBlockPattern {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) : BoundedBlockPattern I N :=
  ⟨⟨P.1.val, Nat.lt_succ_of_le hold⟩, P.2.1,
    fun b => ⟨(P.2.2 b).val, Nat.lt_succ_of_le (hnew b)⟩⟩

def reboundJumpBlock (d : PathCodeData X Y) {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P) :
    JumpBlockCode d (reboundBlockPattern P hold hnew) := ⟨Z.paths, Z.disks⟩

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem reboundJumpBlock_valid (d : PathCodeData X Y) (ν : Measure X)
    (Ntags : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P)
    (hZ : IsJumpBlockCode d ν Ntags B F H O P Z) :
    IsJumpBlockCode d ν Ntags B F H O (reboundBlockPattern P hold hnew)
      (reboundJumpBlock d P hold hnew Z) :=
  ⟨hZ.allowed, hZ.start, hZ.finish, hZ.left, hZ.right, hZ.meets⟩

omit [MeasurableSpace X] in
@[simp] theorem reboundJumpBlock_cost (d : PathCodeData X Y) (B : Set X)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞)
    {n N : ℕ} (P : BoundedBlockPattern I n) (hold : P.1.val ≤ N)
    (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P) :
    jumpBlockCost d B g m r τ T (reboundBlockPattern P hold hnew)
      (reboundJumpBlock d P hold hnew Z) = jumpBlockCost d B g m r τ T P Z := rfl

end CircleDomainRigidity

end

end OAI
