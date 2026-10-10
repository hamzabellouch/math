import Mathlib

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹

def neighbor (v : Vertex) (k : Fin 3) : Vertex :=
  match v with
  | .up i j => if k = 0 then .down i (j - 1)
      else if k = 1 then .down i j else .down (i - 1) j
  | .down i j => if k = 0 then .up i (j + 1)
      else if k = 1 then .up i j else .up (i + 1) j

abbrev Germ := Vertex × Fin 3

def outgoingSlot (g : Germ) (b : Bool) : Fin 3 :=
  g.2 + (if b then 2 else 1)

def advance (g : Germ) (b : Bool) : Germ :=
  (neighbor g.1 (outgoingSlot g b), outgoingSlot g b)

def Stopped : Finset Vertex → Germ → List Bool → Prop
  | D, g, [] => g.1 ∉ D
  | D, g, b :: w => g.1 ∈ D ∧ Stopped (D.erase g.1) (advance g b) w

def leaves (D : Finset Vertex) (g : Germ) : Finset (List Bool) :=
  if g.1 ∈ D then
    ((leaves (D.erase g.1) (advance g true)).image (List.cons true)) ∪
    ((leaves (D.erase g.1) (advance g false)).image (List.cons false))
  else {[]}
termination_by D.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem (by assumption)

noncomputable def turnAngle (b : Bool) : ℝ :=
  if b then Real.pi / 3 else -(Real.pi / 3)

noncomputable def stepWeight (b : Bool) : ℂ :=
  (criticalActivity : ℂ) * Complex.exp (((3 / 8 : ℝ) * turnAngle b : ℝ) * Complex.I)

noncomputable def wordWeight (w : List Bool) : ℂ := (w.map stepWeight).prod

def traced : Germ → List Bool → List Vertex
  | _, [] => []
  | g, b :: w => g.1 :: traced (advance g b) w

def terminalGerm : Germ → List Bool → Germ
  | g, [] => g
  | g, b :: w => terminalGerm (advance g b) w

noncomputable def explorationTotal (D : Finset Vertex) (v : Vertex) : ℂ :=
  ∑ k : Fin 3, ∑ w ∈ leaves (D.erase v) (neighbor v k, k), wordWeight w

@[simp] theorem neighbor_neighbor (v : Vertex) (k : Fin 3) :
    neighbor (neighbor v k) k = v := by
  cases v <;> fin_cases k <;> simp [neighbor]

theorem adjacent_neighbor (v : Vertex) (k : Fin 3) : adjacent v (neighbor v k) := by
  cases v <;> fin_cases k <;> simp [neighbor, adjacent]

theorem neighbor_injective (v : Vertex) : Function.Injective (neighbor v) := by
  intro a b hab
  cases v <;> fin_cases a <;> fin_cases b <;> simp_all [neighbor] <;> omega

@[simp] theorem advance_adjacent (g : Germ) (b : Bool) :
    adjacent g.1 (advance g b).1 := adjacent_neighbor _ _

theorem advance_not_backtracking (g : Germ) (b : Bool) :
    (advance g b).1 ≠ neighbor g.1 g.2 := by
  intro heq
  have hk := neighbor_injective g.1 heq
  obtain ⟨v, k⟩ := g
  fin_cases k <;> cases b <;> simp [outgoingSlot] at hk

@[simp] theorem wordWeight_nil : wordWeight [] = 1 := rfl
@[simp] theorem wordWeight_cons (b : Bool) (w : List Bool) :
    wordWeight (b :: w) = stepWeight b * wordWeight w := rfl

theorem critical_cos_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem stepWeight_sum : stepWeight true + stepWeight false = 1 := by
  have hc : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt critical_cos_pos
  simp only [stepWeight, turnAngle, Bool.false_eq_true, ite_false, ite_true]
  have ht : (3 / 8 : ℝ) * (Real.pi / 3) = Real.pi / 8 := by ring
  have hf : (3 / 8 : ℝ) * -(Real.pi / 3) = -(Real.pi / 8) := by ring
  rw [ht, hf, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  calc
    _ = ((criticalActivity * (2 * Real.cos (Real.pi / 8)) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = 1 := by
      have hw : criticalActivity * (2 * Real.cos (Real.pi / 8)) = 1 :=
        inv_mul_cancel₀ (mul_ne_zero (by norm_num) hc)
      rw [hw]
      norm_num

theorem mem_leaves_iff (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ leaves D g ↔ Stopped D g w := by
  induction w generalizing D g with
  | nil =>
      rw [leaves]
      by_cases h : g.1 ∈ D <;> simp [h, Stopped]
  | cons b w ih =>
      rw [leaves]
      by_cases h : g.1 ∈ D
      · cases b <;> simp [h, Stopped, ih]
      · simp [h, Stopped]

theorem stopped_traced (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : Stopped D g w) :
    (traced g w).Nodup ∧ ∀ v ∈ traced g w, v ∈ D := by
  induction w generalizing D g with
  | nil => simp [traced]
  | cons b w ih =>
      obtain ⟨hg, hw⟩ := hw
      obtain ⟨hn, hD⟩ := ih (D.erase g.1) (advance g b) hw
      constructor
      · simp only [traced, List.nodup_cons]
        refine ⟨?_, hn⟩
        intro hmem
        exact (Finset.mem_erase.mp (hD g.1 hmem)).1 rfl
      · intro v hv
        simp only [traced, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hg
        · exact (Finset.mem_erase.mp (hD v hv)).2

theorem traced_length (g : Germ) (w : List Bool) : (traced g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [traced, List.length_cons, ih]

theorem trace_chain (g : Germ) (w : List Bool) :
    (traced g w ++ [(terminalGerm g w).1]).IsChain adjacent := by
  induction w generalizing g with
  | nil => simp [traced, terminalGerm]
  | cons b w ih =>
      simp only [traced, List.cons_append, terminalGerm]
      apply List.IsChain.cons (ih (advance g b))
      cases w with
      | nil => simp [traced, terminalGerm, advance_adjacent]
      | cons c w => simp [traced, terminalGerm, advance_adjacent]

theorem wordWeight_physical (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((3 / 8 : ℝ) * (w.map turnAngle).sum : ℝ) * Complex.I) := by
  induction w with
  | nil => simp [wordWeight]
  | cons b w ih =>
      simp only [wordWeight_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
      simp only [stepWeight, mul_add, Complex.ofReal_add, Complex.ofReal_mul]
      rw [add_mul, Complex.exp_add, pow_succ]
      ring

theorem sum_cons_image (s : Finset (List Bool)) (b : Bool) :
    ∑ w ∈ s.image (List.cons b), wordWeight w =
      stepWeight b * ∑ w ∈ s, wordWeight w := by
  rw [Finset.sum_image]
  · simp only [wordWeight_cons, Finset.mul_sum]
  · intro a ha c hc hac
    exact List.cons.inj hac |>.2

theorem disjoint_cons_images (s t : Finset (List Bool)) :
    Disjoint (s.image (List.cons true)) (t.image (List.cons false)) := by
  apply Finset.disjoint_left.mpr
  intro w hs ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp ht
  exact Bool.false_ne_true (List.cons.inj heq).1

theorem leaf_balance (D : Finset Vertex) (g : Germ) :
    ∑ w ∈ leaves D g, wordWeight w = 1 := by
  induction D using Finset.strongInductionOn generalizing g with
  | _ D ih =>
      rw [leaves]
      by_cases hg : g.1 ∈ D
      · simp only [hg, ite_true]
        rw [Finset.sum_union (disjoint_cons_images _ _), sum_cons_image, sum_cons_image]
        have hers : D.erase g.1 ⊂ D := Finset.erase_ssubset hg
        rw [ih _ hers _, ih _ hers _]
        simpa only [mul_one] using stepWeight_sum
      · simp [hg]

theorem visit_exploration_balance (D : Finset Vertex) (v : Vertex) (_hv : v ∈ D) :
    explorationTotal D v = 3 := by
  simp [explorationTotal, leaf_balance]

noncomputable def complexPosition (v : Vertex) : ℂ :=
  (position v).1 + (position v).2 * Complex.I

theorem exp_turnAngle (b : Bool) :
    Complex.exp ((turnAngle b : ℝ) * Complex.I) =
      (1 / 2 : ℂ) + (if b then 1 else -1) * (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  cases b <;> simp only [turnAngle, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [Complex.exp_ofReal_mul_I] <;>
    simp [Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

theorem advance_rotation (g : Germ) (b : Bool) :
    complexPosition (advance g b).1 - complexPosition g.1 =
      Complex.exp ((turnAngle b : ℝ) * Complex.I) *
        (complexPosition g.1 - complexPosition (neighbor g.1 g.2)) := by
  rw [exp_turnAngle]
  obtain ⟨v, k⟩ := g
  have hsq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  cases v <;> fin_cases k <;> cases b <;>
    simp [advance, outgoingSlot, neighbor, complexPosition, position] <;>
    ring_nf <;> simp [hsq] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI
