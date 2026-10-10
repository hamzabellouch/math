import OAI.Analysis.Nonexpansive.TreeEvaluation

namespace OAI

/-!
# Finite, already evaluated tree frontiers

A frontier contains only the current finite level and the actual evaluation
of the part already built. The root and extension operations below construct
that evaluation by recursion. In particular, a prediction made at a frontier
does not inspect any future tree level.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The current maps and the evaluation strictly above a finite cutoff. -/
structure TreeFrontier (K : Set X) where
  convex : Convex ℝ K
  size : ℕ
  size_pos : 0 < size
  map : Fin size → K → K
  nonexpansive : ∀ p, LipschitzWith 1 (map p)
  evaluate : (Fin size → K) → K
  evaluate_norm_sub_le_of_forall : ∀ H H' {ε : ℝ},
    (∀ p, ‖(H p : X) - (H' p : X)‖ ≤ ε) →
    ‖(evaluate H : X) - (evaluate H' : X)‖ ≤ ε

namespace TreeFrontier

variable {K : Set X}

/-- At depth zero the sole cutoff output is already the root output. -/
def root (hK : Convex ℝ K) : TreeFrontier K where
  convex := hK
  size := 1
  size_pos := Nat.zero_lt_one
  map := fun _ => id
  nonexpansive := fun _ => LipschitzWith.id
  evaluate := fun H => H ⟨0, Nat.zero_lt_one⟩
  evaluate_norm_sub_le_of_forall := fun _ _ _ h => h ⟨0, Nat.zero_lt_one⟩

@[simp] theorem root_size (hK : Convex ℝ K) : (root hK).size = 1 := rfl

@[simp] theorem root_map (hK : Convex ℝ K) (p : Fin (root hK).size) :
    (root hK).map p = id := rfl

@[simp] theorem root_evaluate (hK : Convex ℝ K) (H : Fin 1 → K) :
    (root hK).evaluate H = H ⟨0, Nat.zero_lt_one⟩ := rfl

end TreeFrontier

/-- One concrete finite successor level. Its parentwise positive weights
are supplied only after the corresponding adaptive selections stop. -/
structure FrontierExtension {K : Set X} (F : TreeFrontier K) where
  size : ℕ
  size_pos : 0 < size
  parent : Fin size → Fin F.size
  parent_monotone : Monotone parent
  parent_surjective : Function.Surjective parent
  weight : Fin size → ℝ
  weight_pos : ∀ c, 0 < weight c
  weight_sum : ∀ p,
    (∑ c ∈ Finset.univ.filter (fun c => parent c = p), weight c) = 1
  map : Fin size → K → K
  nonexpansive : ∀ c, LipschitzWith 1 (map c)

namespace FrontierExtension

variable {K : Set X} {F : TreeFrontier K} (C : FrontierExtension F)

/-- Actual parentwise convex average of the new cutoff outputs. -/
def childAverage (H : Fin C.size → K) (p : Fin F.size) : K := by
  classical
  refine ⟨∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
    C.weight c • (H c : X), ?_⟩
  exact F.convex.sum_mem (fun c _ => (C.weight_pos c).le)
    (C.weight_sum p) (fun c _ => (H c).property)

@[simp] theorem childAverage_val (H : Fin C.size → K) (p : Fin F.size) :
    (C.childAverage H p : X) =
      ∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
        C.weight c • (H c : X) := rfl

/-- The current maps act once, after the new child averages. -/
def collapse (H : Fin C.size → K) (p : Fin F.size) : K :=
  F.map p (C.childAverage H p)

/-- A uniform cutoff bound remains a uniform bound after averaging. -/
theorem childAverage_norm_sub_le_of_forall
    (H H' : Fin C.size → K) {ε : ℝ}
    (h : ∀ c, ‖(H c : X) - (H' c : X)‖ ≤ ε) (p : Fin F.size) :
    ‖(C.childAverage H p : X) - (C.childAverage H' p : X)‖ ≤ ε := by
  classical
  rw [C.childAverage_val, C.childAverage_val, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
        C.weight c • ((H c : X) - (H' c : X))‖ ≤
        ∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
          ‖C.weight c • ((H c : X) - (H' c : X))‖ := norm_sum_le _ _
    _ = ∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
        C.weight c * ‖(H c : X) - (H' c : X)‖ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (C.weight_pos c)]
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c => C.parent c = p),
        C.weight c * ε := by
      exact Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (h c) (C.weight_pos c).le
    _ = ε := by rw [← Finset.sum_mul, C.weight_sum, one_mul]

theorem collapse_norm_sub_le_of_forall
    (H H' : Fin C.size → K) {ε : ℝ}
    (h : ∀ c, ‖(H c : X) - (H' c : X)‖ ≤ ε) (p : Fin F.size) :
    ‖(C.collapse H p : X) - (C.collapse H' p : X)‖ ≤ ε := by
  have hm : ‖(C.collapse H p : X) - (C.collapse H' p : X)‖ ≤
      ‖(C.childAverage H p : X) - (C.childAverage H' p : X)‖ := by
    simpa only [collapse, Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (F.nonexpansive p).dist_le_mul (C.childAverage H p) (C.childAverage H' p)
  exact hm.trans (C.childAverage_norm_sub_le_of_forall H H' h p)

/-- The next frontier evaluation is built from the preceding one. -/
def toFrontier : TreeFrontier K where
  convex := F.convex
  size := C.size
  size_pos := C.size_pos
  map := C.map
  nonexpansive := C.nonexpansive
  evaluate := fun H => F.evaluate (C.collapse H)
  evaluate_norm_sub_le_of_forall := fun H H' _ h =>
    F.evaluate_norm_sub_le_of_forall (C.collapse H) (C.collapse H')
      (C.collapse_norm_sub_le_of_forall H H' h)

@[simp] theorem toFrontier_size : C.toFrontier.size = C.size := rfl

@[simp] theorem toFrontier_map (c : Fin C.size) :
    C.toFrontier.map c = C.map c := rfl

@[simp] theorem toFrontier_evaluate (H : Fin C.size → K) :
    C.toFrontier.evaluate H = F.evaluate (C.collapse H) := rfl

end FrontierExtension
end ReflexiveFixedPoints

end

end OAI
