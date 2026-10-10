import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceIntegrality
import OAI.NumberTheory.Ostmann.Construction.RecursiveTransferWeight

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

structure MovingSlotState (σ : Type*) where
  depth : ℕ
  data : MovingSlotData σ depth
  leftGiant : ℕ
  rightGiant : ℕ

def MovingSlotState.leftProduct {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ CL _ _ _ _, XL, _⟩ => XL * MovingSlotReversal.naturalProduct value CL

def MovingSlotState.rightProduct {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ CR _ _ _, _, XR⟩ => XR * MovingSlotReversal.naturalProduct value CR

def MovingSlotState.compensation {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ _ u _ _, _, _⟩ => MovingSlotReversal.naturalProduct value u

def MovingSlotState.child {σ : Type*} (value : σ → ℕ) (left : Bool)
    (x : MovingSlotState σ) (P : ℕ) : MovingSlotState σ :=
  match x with
  | ⟨0, .leaf s regular, XL, XR⟩ => ⟨0, .leaf s regular, XL, XR⟩
  | ⟨n + 1, .node _ _ _ u L R, XL, XR⟩ =>
      ⟨n, if left then L else R, P / MovingSlotReversal.naturalProduct value u,
        if left then XL else XR⟩

def movingSlotSystem {σ : Type*} (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ) :
    TransferHistorySystem (MovingSlotState σ) where
  leftProduct := MovingSlotState.leftProduct value
  rightProduct := MovingSlotState.rightProduct value
  childBound x := childBound x.depth
  pivotBound x := pivotBound x.depth
  leftState := MovingSlotState.child value true
  rightState := MovingSlotState.child value false

/-- The extra support test is literal divisibility of the composite pivot by
its sampled compensation product. All smooth and other support factors stay
in `extra`. -/
noncomputable def movingSlotCutoff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  if 0 < x.compensation value ∧
      x.compensation value ∣ historyPivot (movingSlotSystem value childBound pivotBound) x s v w
  then extra x s v w else 0

def MovingSlotData.Follows {σ : Type*} : {n : ℕ} →
    MovingSlotData σ n → FrequencyTree ℤ n → Prop
  | _, .leaf s _, t => s = frequencyRoot 0 t
  | _n + 1, .node s _ _ _ left right, t =>
      s = t.1 ∧ left.Follows t.2.1 ∧ right.Follows t.2.2

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem buildMovingSlotData_follows {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).Follows t := by
  induction samples with
  | leaf => rfl
  | node samples left right ihL ihR => exact ⟨rfl, ihL _ _ _, ihR _ _ _⟩

/-- Nonzero original recursive coefficients force exactly the integral support
of the concrete moving-giant sampler. This does not assign any prime law to
its reconstructed integer pivot. -/
theorem movingSlotWeight_nonzero_integral {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (leaf : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) leaf
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    T.Integral value XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular => trivial
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hvalid : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P := by
      by_contra h
      apply hw
      change recursiveTransferWeight sys leaf cutoff (n + 1) x t = 0
      simp only [recursiveTransferWeight, P, h, ite_false]
    have hnode := recursiveTransferWeight_node sys leaf cutoff n x t P hvalid
    have hcut : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
      intro h
      apply hw
      rw [hnode, h, Complex.ofReal_zero, zero_mul, zero_mul]
    have hdiv : 0 < MovingSlotReversal.naturalProduct value u ∧
        MovingSlotReversal.naturalProduct value u ∣ P := by
      by_contra h
      apply hcut
      change (if 0 < MovingSlotReversal.naturalProduct value u ∧
        MovingSlotReversal.naturalProduct value u ∣ P then _ else 0) = 0
      exact ite_eq_right h
    let p := P / MovingSlotReversal.naturalProduct value u
    have hP : P = MovingSlotReversal.naturalProduct value u * p := by
      exact (Nat.mul_div_cancel' hdiv.2).symm
    have hp : 0 < p := by
      by_contra hp
      have hz : p = 0 := Nat.eq_zero_of_not_pos hp
      have := hvalid.pivot_pos
      rw [hP, hz, Nat.mul_zero] at this
      omega
    have hL : recursiveTransferWeight sys leaf cutoff n
        ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro h
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys leaf cutoff n ⟨n, left, p, XL⟩ t.2.1 * _ = 0
      rw [h, mul_zero, zero_mul]
    have hR : recursiveTransferWeight sys leaf cutoff n
        ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro h
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys leaf cutoff n ⟨n, right, p, XR⟩ t.2.2) = 0
      rw [h, star_zero, mul_zero]
    have hrel : left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
        s * ((MovingSlotReversal.naturalProduct value u * p : ℕ) : ℤ) := by
      simpa only [sys, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct,
        x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, hP, Int.cast_natCast] using hvalid.relation
    have hnat : (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR = p := by
      unfold MovingSlotReversal.naturalPivot movingGiantPivot
      simp only [MovingSlotData.step, Nat.mul_one]
      rw [reconstructedPivot_of_eq _ _ (by simpa only [← hT.1] using hvalid.root_ne_zero)
        (MovingSlotReversal.naturalProduct value u * p) hrel]
      exact Nat.mul_div_cancel_left p hdiv.1
    change (_ ∧ _ ∧ _)
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR ∧ _
      constructor
      · exact hnat.symm ▸ hp
      · change left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
          right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((MovingSlotReversal.naturalProduct value u *
            (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR : ℕ) : ℤ)
        rw [hnat]
        exact hrel
    · rw [hnat]
      exact ihL t.2.1 hT.2.1 p XL hL
    · rw [hnat]
      exact ihR t.2.2 hT.2.2 p XR hR

end Ostmann

end OAI
