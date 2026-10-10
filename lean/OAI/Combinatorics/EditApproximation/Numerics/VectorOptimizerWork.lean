import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork
import OAI.Combinatorics.EditApproximation.Geometry.OnlineActionDraw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Materialized rational optimizer iterates. Finite vectors store the
previous iterate and its gradient, and a scored scan stores the current
best score. Counters charge rational arithmetic, comparisons, array
accesses and array writes. Integer/rational bit costs are separate. -/

namespace EditApproximation

open Finset

def naturalPowerWithWork (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => let previous := naturalPowerWithWork a k
    (previous.1 * a, previous.2 + 1)

theorem naturalPowerWithWork_spec (a k : ℕ) : naturalPowerWithWork a k = (a ^ k, k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [naturalPowerWithWork, ih, pow_succ]

theorem vector_get_ofFn {α : Type*} {d : ℕ} (f : Fin d → α) (i : Fin d) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

/-- A single materializing array pass. The operation count includes
array construction, the value/counter traversals, and summing counters. -/


theorem vectorMapWithWork_value {α : Type*} (d : ℕ) (f : Fin d → α × ℕ) (i : Fin d) :
    (vectorMapWithWork d f).1.get i = (f i).1 := by
  change (Vector.ofFn f |>.map Prod.fst)[i.val] = _
  simp only [Vector.getElem_map, Vector.getElem_ofFn]

theorem vectorMapWithWork_cost {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (C : ℕ) (hC : ∀ i, (f i).2 = C) :
    (vectorMapWithWork d f).2 = d * (C + 6) := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, hC, List.ofFn_const, List.sum_replicate, smul_eq_mul]
  ring

/-- Dot product over an explicit list of array indices. -/
def vectorDotListWithWork {d : ℕ} (left right : Vector ℚ d) : List (Fin d) → ℚ × ℕ
  | [] => (0, 0)
  | i :: indices =>
    let rest := vectorDotListWithWork left right indices
    (left.get i * right.get i + rest.1, rest.2 + 8)

theorem vectorDotListWithWork_spec {d : ℕ} (left right : Vector ℚ d) (indices : List (Fin d)) :
    vectorDotListWithWork left right indices =
      ((indices.map fun i => left.get i * right.get i).sum, 8 * indices.length) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [vectorDotListWithWork, ih, List.map_cons, List.sum_cons, List.length_cons]
    congr 1

def vectorDotWithWork {d : ℕ} (left right : Vector ℚ d) : ℚ × ℕ :=
  vectorDotListWithWork left right (List.finRange d)

theorem vectorDotWithWork_spec {d : ℕ} (left right : Vector ℚ d) :
    vectorDotWithWork left right = (∑ i : Fin d, left.get i * right.get i, 8 * d) := by
  simp only [vectorDotWithWork, vectorDotListWithWork_spec, List.length_finRange]
  congr 1

def rationalGradientCellWithWork {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) : ℚ × ℕ :=
  let smoothing := rationalPowerWithWork (G : ℚ) 50
  let truncation := naturalPowerWithWork G 60
  let logarithm := rationalLogApproximationWithWork (point.get i + 1 / smoothing.1) truncation.1
  (-logarithm.1 - 1 + linear.get i, smoothing.2 + truncation.2 + logarithm.2 + 7)

theorem rationalGradientCellWithWork_spec {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) :
    rationalGradientCellWithWork G linear point i =
      (rationalSmoothedGradient G linear.get point.get i, G ^ 120 + 2 * G ^ 60 + 121) := by
  simp only [rationalGradientCellWithWork, rationalPowerWithWork_spec, naturalPowerWithWork_spec,
    rationalLogApproximationWithWork_spec, rationalSmoothedGradient]
  congr 1
  rw [show (120 : ℕ) = 60 * 2 by rfl, pow_mul]
  ring

def vectorGradientWithWork {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) : Vector ℚ d × ℕ :=
  vectorMapWithWork d (rationalGradientCellWithWork G linear point)

theorem vectorGradientWithWork_value {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) :
    (vectorGradientWithWork G linear point).1.get i =
      rationalSmoothedGradient G linear.get point.get i := by
  rw [vectorGradientWithWork, vectorMapWithWork_value, rationalGradientCellWithWork_spec]

theorem vectorGradientWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) :
    (vectorGradientWithWork G linear point).2 = d * (G ^ 120 + 2 * G ^ 60 + 127) := by
  unfold vectorGradientWithWork
  rw [vectorMapWithWork_cost _ _ (G ^ 120 + 2 * G ^ 60 + 121) (fun i => congrArg Prod.snd
    (rationalGradientCellWithWork_spec G linear point i))]

/-- A scored scan keeps the winning score instead of recomputing it.
It retains the first maximizer, including ties. -/
def scoredArgmaxWithWork {α : Type*} (score : α → ℚ × ℕ) : List α → Option (α × ℚ) × ℕ
  | [] => (none, 0)
  | a :: rest =>
    let tail := scoredArgmaxWithWork score rest
    let current := score a
    match tail.1 with
    | none => (some (a, current.1), tail.2 + current.2 + 1)
    | some best =>
      (if current.1 < best.2 then some best else some (a, current.1), tail.2 + current.2 + 2)

theorem scoredArgmaxWithWork_value {α : Type*} (score : α → ℚ × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1) with
    | none => rfl
    | some best => simp only [Option.map_some]; split_ifs <;> rfl

theorem scoredArgmaxWithWork_cost {α : Type*} (score : α → ℚ × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (score a).2 ≤ C) :
    (scoredArgmaxWithWork score values).2 ≤ values.length * (C + 2) := by
  induction values with
  | nil => simp only [scoredArgmaxWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
    have ha := hC a (List.mem_cons_self)
    simp only [scoredArgmaxWithWork, List.length_cons]
    split <;> dsimp only <;> nlinarith only [htail, ha]

def vectorMaximizerWithWork {d : ℕ} (gradient : Vector ℚ d)
    (vertices : List (Vector ℚ d)) : Vector ℚ d × ℕ :=
  let selected := scoredArgmaxWithWork (vectorDotWithWork gradient) vertices
  ((selected.1.map Prod.fst).getD (Vector.replicate d 0), selected.2 + d + 1)

theorem vectorMaximizerWithWork_value {d : ℕ} (gradient : Vector ℚ d)
    (vertices : List (Vector ℚ d)) :
    (vectorMaximizerWithWork gradient vertices).1.get =
      rationalLinearizationMaximizer univ (vertices.map Vector.get) gradient.get := by
  have hmap := argmax_map_commutes (fun vertex : Vector ℚ d => vertex.get)
    (fun vertex => ∑ i : Fin d, gradient.get i * vertex i) vertices
  simp only [vectorMaximizerWithWork, scoredArgmaxWithWork_value, vectorDotWithWork_spec,
    Option.map_map, Function.comp_def] at hmap ⊢
  unfold rationalLinearizationMaximizer
  rw [hmap]
  cases h : vertices.argmax (fun vertex => ∑ i : Fin d, gradient.get i * vertex.get i) with
  | none => funext i; exact Vector.getElem_replicate i.isLt
  | some selected => rfl

theorem vectorMaximizerWithWork_cost {d : ℕ} (gradient : Vector ℚ d)
    (vertices : List (Vector ℚ d)) :
    (vectorMaximizerWithWork gradient vertices).2 ≤ vertices.length * (8 * d + 2) + d + 1 := by
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (scoredArgmaxWithWork_cost _ _ (8 * d) (fun vertex _ =>
      (congrArg Prod.snd (vectorDotWithWork_spec gradient vertex)).le)) d) 1

def materializedOptimizerWithWork {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G : ℕ) : ℕ → Vector ℚ d × ℕ
  | 0 => (vertices.headD (Vector.replicate d 0), d + 1)
  | j + 1 =>
    let previous := materializedOptimizerWithWork vertices linear G j
    let gradient := vectorGradientWithWork G linear previous.1
    let selected := vectorMaximizerWithWork gradient.1 vertices
    let step : ℚ := 2 / ((j : ℚ) + 2)
    let updated := vectorMapWithWork d fun i =>
      ((1 - step) * previous.1.get i + step * selected.1.get i, 5)
    (updated.1, previous.2 + gradient.2 + selected.2 + updated.2 + 3)

theorem materializedOptimizerWithWork_value {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G j : ℕ) :
    (materializedOptimizerWithWork vertices linear G j).1.get =
      finiteRationalOptimizer univ (vertices.map Vector.get) linear.get G j := by
  induction j with
  | zero =>
    cases vertices with
    | nil => funext i; exact Vector.getElem_replicate i.isLt
    | cons vertex rest => rfl
  | succ j ih =>
    funext i
    simp only [materializedOptimizerWithWork, vectorMapWithWork_value, finiteRationalOptimizer]
    rw [congrFun ih i, vectorMaximizerWithWork_value]
    congr 2
    congr 1
    funext k
    rw [vectorGradientWithWork_value, ih]

def materializedOptimizerStepBudget (d v G : ℕ) : ℕ :=
  d * (G ^ 120 + 2 * G ^ 60 + 127) + v * (8 * d + 2) + d + 1 + 11 * d + 3

theorem materializedOptimizerWithWork_cost {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G j : ℕ) :
    (materializedOptimizerWithWork vertices linear G j).2 ≤
      d + 1 + j * materializedOptimizerStepBudget d vertices.length G := by
  induction j with
  | zero => simp only [materializedOptimizerWithWork, Nat.zero_mul, Nat.add_zero, le_refl]
  | succ j ih =>
    have hselected := vectorMaximizerWithWork_cost
      (vectorGradientWithWork G linear (materializedOptimizerWithWork vertices linear G j).1).1 vertices
    simp only [materializedOptimizerWithWork, vectorGradientWithWork_cost]
    rw [vectorMapWithWork_cost _ _ 5 (fun _ => rfl)]
    dsimp only [materializedOptimizerStepBudget] at ih ⊢
    nlinarith only [ih, hselected]

private theorem optimizerStepArithmetic_bound (d v x y U : ℕ)
    (hx : x ≤ U) (hy : y ≤ U) (hU : 1 ≤ U) :
    d * (x + 2 * y + 127) + v * (8 * d + 2) + d + 1 + 11 * d + 3 ≤
      156 * ((v + 1) * (d + 1) * U) := by
  let C := (v + 1) * (d + 1) * U
  have hd : d * U ≤ C := Nat.mul_le_mul_right U (by nlinarith)
  have hv : v * (d + 1) * U ≤ C :=
    Nat.mul_le_mul_right U (Nat.mul_le_mul_right (d + 1) (by omega))
  have hdu : (d + 1) * U ≤ C := Nat.mul_le_mul_right U (by nlinarith)
  have hfirst : d * (x + 2 * y + 127) ≤ 130 * C := by
    calc
      _ ≤ d * (130 * U) := Nat.mul_le_mul_left d (by omega)
      _ = 130 * (d * U) := by ring
      _ ≤ 130 * C := Nat.mul_le_mul_left 130 hd
  have hsecond : v * (8 * d + 2) ≤ 10 * C := by
    calc
      _ ≤ 10 * (v * (d + 1)) := by nlinarith
      _ ≤ 10 * (v * (d + 1) * U) := Nat.mul_le_mul_left 10 (Nat.le_mul_of_pos_right _ hU)
      _ ≤ 10 * C := Nat.mul_le_mul_left 10 hv
  have hrest : d + 1 + 11 * d + 3 ≤ 16 * C := by
    calc
      _ ≤ 16 * (d + 1) := by omega
      _ ≤ 16 * ((d + 1) * U) := Nat.mul_le_mul_left 16 (Nat.le_mul_of_pos_right _ hU)
      _ ≤ 16 * C := Nat.mul_le_mul_left 16 hdu
  change _ ≤ 156 * C
  omega

private theorem move_outer_factor (a b c d : ℕ) : d * (a * b * c) = a * b * (d * c) := by
  ac_rfl

private theorem move_outer_factor_right (a b c d : ℕ) : d * (a * b * c) = a * b * (c * d) := by
  ac_rfl

theorem materializedOptimizerStepBudget_polynomial (d v G : ℕ) :
    materializedOptimizerStepBudget d v G ≤ (v + 1) * (d + 1) * (G + 2) ^ 128 := by
  have hU : 1 ≤ (G + 2) ^ 120 := Nat.one_le_pow _ _ (by omega)
  have hG120 : G ^ 120 ≤ (G + 2) ^ 120 := Nat.pow_le_pow_left (by omega) _
  have hG60 : G ^ 60 ≤ (G + 2) ^ 120 :=
    (Nat.pow_le_pow_left (show G ≤ G + 2 by omega) 60).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hconstant : 156 ≤ (G + 2) ^ 8 :=
    (show 156 ≤ 2 ^ 8 by norm_num).trans (Nat.pow_le_pow_left (by omega) 8)
  have hpower : (G + 2) ^ 128 = (G + 2) ^ 8 * (G + 2) ^ 120 :=
    pow_add (G + 2) 8 120
  calc
    _ ≤ 156 * ((v + 1) * (d + 1) * (G + 2) ^ 120) :=
      optimizerStepArithmetic_bound d v (G ^ 120) (G ^ 60) _ hG120 hG60 hU
    _ ≤ (G + 2) ^ 8 * ((v + 1) * (d + 1) * (G + 2) ^ 120) :=
      Nat.mul_le_mul_right _ hconstant
    _ = _ := by rw [hpower]; exact move_outer_factor _ _ _ _

theorem materializedOptimizerWithWork_polynomial {d : ℕ}
    (vertices : List (Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) (hj : j ≤ G ^ 80) :
    (materializedOptimizerWithWork vertices linear G j).2 ≤
      (vertices.length + 1) * (d + 1) * (G + 2) ^ 209 := by
  let C := (vertices.length + 1) * (d + 1) * (G + 2) ^ 128
  have hbase : d + 1 ≤ C := by
    have hpow : 1 ≤ (G + 2) ^ 128 := Nat.one_le_pow _ _ (by omega)
    dsimp only [C]
    exact (show d + 1 ≤ (vertices.length + 1) * (d + 1) by nlinarith).trans
      (Nat.le_mul_of_pos_right _ hpow)
  have hj1 : j + 1 ≤ (G + 2) ^ 81 := by
    have hj' : j ≤ (G + 2) ^ 80 := hj.trans (Nat.pow_le_pow_left (by omega) 80)
    have hpow : 1 ≤ (G + 2) ^ 80 := Nat.one_le_pow _ _ (by omega)
    calc
      j + 1 ≤ (G + 2) ^ 80 + (G + 2) ^ 80 := Nat.add_le_add hj' hpow
      _ = (G + 2) ^ 80 * 2 := by omega
      _ ≤ (G + 2) ^ 80 * (G + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = (G + 2) ^ 81 := (pow_succ _ _).symm
  calc
    _ ≤ d + 1 + j * materializedOptimizerStepBudget d vertices.length G :=
      materializedOptimizerWithWork_cost vertices linear G j
    _ ≤ C + j * C := Nat.add_le_add hbase
      (Nat.mul_le_mul_left j (materializedOptimizerStepBudget_polynomial d vertices.length G))
    _ = (j + 1) * C := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ (G + 2) ^ 81 * C := Nat.mul_le_mul_right C hj1
    _ = _ := by
      dsimp only [C]
      have hpower : (G + 2) ^ 209 = (G + 2) ^ 81 * (G + 2) ^ 128 :=
        pow_add (G + 2) 81 128
      rw [hpower]
      exact move_outer_factor _ _ _ _

/-- The final scan retains the original action label, so equal vectors
and tied scores do not change which listed action is returned. -/
def materializedSelectionWithWork {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) : Option α × ℕ :=
  let iterate := materializedOptimizerWithWork (vertices.map Prod.snd) linear G j
  let gradient := vectorGradientWithWork G linear iterate.1
  let selected := scoredArgmaxWithWork (fun vertex => vectorDotWithWork gradient.1 vertex.2) vertices
  (selected.1.map fun chosen => chosen.1.1, iterate.2 + gradient.2 + selected.2 + 1)

theorem materializedSelectionWithWork_value {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) :
    (materializedSelectionWithWork vertices linear G j).1 =
      (vertices.argmax fun vertex =>
        ∑ i : Fin d, rationalSmoothedGradient G linear.get
          (finiteRationalOptimizer univ ((vertices.map Prod.snd).map Vector.get) linear.get G j) i *
          vertex.2.get i).map Prod.fst := by
  simp only [materializedSelectionWithWork, scoredArgmaxWithWork_value,
    vectorDotWithWork_spec, Option.map_map, Function.comp_def]
  congr 2
  funext vertex
  apply sum_congr rfl
  intro i _
  rw [vectorGradientWithWork_value, materializedOptimizerWithWork_value]

theorem materializedSelectionWithWork_cost {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) :
    (materializedSelectionWithWork vertices linear G j).2 ≤
      (materializedOptimizerWithWork (vertices.map Prod.snd) linear G j).2 +
        materializedOptimizerStepBudget d vertices.length G := by
  have hscan := scoredArgmaxWithWork_cost
    (fun vertex : α × Vector ℚ d => vectorDotWithWork
      (vectorGradientWithWork G linear
        (materializedOptimizerWithWork (vertices.map Prod.snd) linear G j).1).1 vertex.2)
    vertices (8 * d) (fun vertex _ =>
      (congrArg Prod.snd (vectorDotWithWork_spec _ _)).le)
  simp only [materializedSelectionWithWork, vectorGradientWithWork_cost]
  unfold materializedOptimizerStepBudget
  omega

theorem materializedSelectionWithWork_polynomial {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ)
    (hj : j ≤ G ^ 80) :
    (materializedSelectionWithWork vertices linear G j).2 ≤
      (vertices.length + 1) * (d + 1) * (G + 2) ^ 210 := by
  have hiter := materializedOptimizerWithWork_polynomial (vertices.map Prod.snd) linear G j hj
  simp only [List.length_map] at hiter
  have hstep := materializedOptimizerStepBudget_polynomial d vertices.length G
  have hexp : (G + 2) ^ 128 ≤ (G + 2) ^ 209 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have htwice : 2 * ((vertices.length + 1) * (d + 1) * (G + 2) ^ 209) ≤
      (vertices.length + 1) * (d + 1) * (G + 2) ^ 210 := by
    have hpower : (G + 2) ^ 210 = (G + 2) ^ 209 * (G + 2) := pow_succ _ _
    rw [hpower]
    calc
      _ ≤ (G + 2) * ((vertices.length + 1) * (d + 1) * (G + 2) ^ 209) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = _ := move_outer_factor_right _ _ _ _
  exact (materializedSelectionWithWork_cost vertices linear G j).trans
    ((Nat.add_le_add hiter (hstep.trans
      (Nat.mul_le_mul_left ((vertices.length + 1) * (d + 1)) hexp))).trans
      (by simpa only [two_mul] using htwice))

end EditApproximation

end OAI
