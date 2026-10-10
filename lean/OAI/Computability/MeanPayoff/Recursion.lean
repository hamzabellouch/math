import OAI.Computability.MeanPayoff.Sampling

namespace OAI

section

namespace MeanPayoff

theorem Budgets.reduceK_rank {n : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter) :
    parameterRank P.reduceK.parameter < parameterRank P.parameter := by
  apply parameterRank_decreases hR
  rw [P.reduceK_parameter]
  linarith

theorem Budgets.reduceM_rank {n : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter) :
    parameterRank P.reduceM.parameter < parameterRank P.parameter := by
  apply parameterRank_decreases hR
  rw [P.reduceM_parameter]
  linarith

theorem Budgets.reweightK_rank {n : ℕ} (P : Budgets n) (hn : 0 < n)
    (hR : 1 ≤ P.parameter) {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    parameterRank (P.reweightK H).parameter < parameterRank P.parameter :=
  parameterRank_decreases hR (P.reweightK_contraction hn hH)

theorem Budgets.reweightM_rank {n : ℕ} (P : Budgets n) (hn : 0 < n)
    (hR : 1 ≤ P.parameter) {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    parameterRank (P.reweightM H).parameter < parameterRank P.parameter :=
  parameterRank_decreases hR (P.reweightM_contraction hn hH)

abbrev LowerSolver {n Bmax : ℕ} (P : Budgets n) :=
  (Q : Budgets n) → parameterRank Q.parameter < parameterRank P.parameter →
    (I : SolveBox n Bmax) → RandomTree (BoxVector I)

abbrev SmallSet {n : ℕ} (P : Budgets n) := {H : Finset (Fin n) // P.measure H ≤ 1 / 2}

structure Orientation {n : ℕ} (P : Budgets n) where
  chooseY : Bool
  exceptions : List (SmallSet P)

namespace SolveBox

def D {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / (32 * globalS Bmax)
def E {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / 8
def delta {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width / (4 * globalS Bmax)
def C {n Bmax : ℕ} (I : SolveBox n Bmax) : ℕ := I.width - I.delta

theorem D_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.D := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem D_small {n Bmax : ℕ} (I : SolveBox n Bmax) : 2 * I.D ≤ I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  change 2 * (I.width / (32 * globalS Bmax)) ≤ I.width
  nlinarith

theorem E_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.E := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem E_smaller {n Bmax : ℕ} (I : SolveBox n Bmax) : 2 * I.E < I.width := by
  have hd := Nat.div_mul_le_self I.width 8
  have hp := I.positive
  change 2 * (I.width / 8) < I.width
  omega

theorem delta_positive {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : 0 < I.delta := by
  have hs := globalS_large Bmax
  exact Nat.div_pos (by omega) (by omega)

theorem delta_smaller {n Bmax : ℕ} (I : SolveBox n Bmax) : I.delta < I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (4 * globalS Bmax)
  have hp := I.positive
  change I.width / (4 * globalS Bmax) < I.width
  nlinarith

theorem C_positive {n Bmax : ℕ} (I : SolveBox n Bmax) : 0 < I.C := by
  have hd := I.delta_smaller
  unfold C
  omega

theorem C_smaller {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) : I.C < I.width := by
  have hd := I.delta_positive h
  have hp := I.C_positive
  unfold C at *
  omega

def narrowCentered {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) (q : Vec (Fin n)) : SolveBox n Bmax :=
  centered q I.D (I.D_positive h) (I.D_small.trans I.bounded)

def wideCentered {n Bmax : ℕ} (I : SolveBox n Bmax)
    (h : 128 * globalS Bmax < I.width) (q : Vec (Fin n)) : SolveBox n Bmax :=
  centered q I.E (I.E_positive h) (I.E_smaller.le.trans I.bounded)

end SolveBox

def centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) : RandomTree (BoxVector I) :=
  let K := I.narrowCentered hB q.val
  (K.repeated (lower P.reduceK (P.reduceK_rank hR) K) (globalJ n Bmax)).bind fun r₁ =>
  (K.repeated (lower P.reduceM (P.reduceM_rank hR) K) (globalJ n Bmax)).map fun r₂ =>
    I.averageClipped r₁.val r₂.val

def centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    ℕ → BoxVector I → RandomTree (List (BoxVector I))
  | 0, q => .leaf [q]
  | t + 1, q =>
    (centerUpdate P hR lower I hB q).bind fun q' =>
    (centerSteps P hR lower I hB t q').map (q :: ·)

def PositiveDisplacement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2 * (I.width : ℤ) <
    (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i))

def NegativeDisplacement {n Bmax : ℕ} (I : SolveBox n Bmax) (q : BoxVector I) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * (q.val i - I.midpoint.val i) <
    -2 * (I.width : ℤ))

def orientBase (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    Orientation P :=
  let p := I.exactVector G
  let H : Finset (Fin G.n) := Finset.univ.filter (fun i => (I.width : ℤ) ≤ 2 * (p.val i - I.a i))
  if hH : 1 / 2 < P.measure H then
    ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else ⟨false, [⟨H, le_of_not_gt hH⟩]⟩

def orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (qs : List (BoxVector I)) (child : BoxVector I → RandomTree (Orientation P)) :
    RandomTree (Orientation P) :=
  let H := PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  let N := NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  if hH : 1 / 2 < P.measure H then
    .leaf ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else if hN : 1 / 2 < P.measure N then
    .leaf ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else
    (RandomTree.uniformBelow (sampleExponent Bmax)).bind fun j =>
      (child (qs.getD j I.midpoint)).map fun O =>
        ⟨O.chooseY, O.exceptions ++ [⟨H, le_of_not_gt hH⟩, ⟨N, le_of_not_gt hN⟩]⟩

def orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    RandomTree (Orientation P) :=
  if hB : I.width ≤ 128 * globalS Bmax then
    .leaf (orientBase G P I)
  else
    let hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind fun qs =>
      orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val))
termination_by I.width
decreasing_by exact I.E_smaller

def combineOrientations {n : ℕ} {P : Budgets n} (os : List (Orientation P)) : Orientation P :=
  ⟨decide (os.length < 2 * (os.filter (fun o => o.chooseY)).length),
      (os.map Orientation.exceptions).flatten⟩

def orientPlus {n : ℕ} {P : Budgets n} (t : RandomTree (Orientation P)) (J : ℕ) :
    RandomTree (Orientation P) :=
  (RandomTree.trials t J).map combineOrientations



structure InnerBox {n Bmax : ℕ} (I : SolveBox n Bmax) where
  box : SolveBox n Bmax
  width_eq : box.width = I.width
  floor_le : I.a ≤ box.a
  ceiling_le : box.b ≤ I.b

def InnerBox.include {n Bmax : ℕ} {I : SolveBox n Bmax} (K : InnerBox I)
    (p : BoxVector K.box) : BoxVector I :=
  ⟨p.val, K.floor_le.trans p.property.1, p.property.2.trans K.ceiling_le⟩

theorem volume_ceiling_decreases {n : ℕ} {a b r : Vec (Fin n)}
    (har : a ≤ r) (hrb : r ≤ b) (hne : r ≠ b) : volume r a < volume b a := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Int.toNat_le_toNat (sub_le_sub_right (hrb i) _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hai : a i ≤ r i := har i
    have hbi : r i ≤ b i := hrb i
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply (Int.toNat_lt_toNat (by omega)).mpr
    omega

def tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : RandomTree (InnerBox I) :=
  (I.repeated (lower P.reduceK (P.reduceK_rank hR) I) (globalJ n Bmax)).bind fun r₁ =>
  if _h₁ : ∃ i, (I.delta : ℤ) ≤ r₁.val i - I.a i then
    let K := I.withFloor r₁
    (tighten P hR lower K hB).map fun T =>
      ⟨T.box, T.width_eq, r₁.property.1.trans T.floor_le, T.ceiling_le⟩
  else
    (I.repeated (lower P.reduceM (P.reduceM_rank hR) I) (globalJ n Bmax)).bind fun r₂ =>
    if _h₂ : ∃ i, (I.delta : ℤ) ≤ I.b i - r₂.val i then
      let K := I.withCeiling r₂
      (tighten P hR lower K hB).map fun T =>
        ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r₂.property.2⟩
    else .leaf ⟨I, rfl, le_refl _, le_refl _⟩
termination_by volume I.b I.a
decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := _h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := _h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

namespace RandomTree

def traverse {α β : Type} (f : α → RandomTree β) : List α → RandomTree (List β)
  | [] => .leaf []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

end RandomTree

namespace SolveBox

def maxVector {n Bmax : ℕ} (I : SolveBox n Bmax) (p q : BoxVector I) : BoxVector I :=
  ⟨fun i => max (p.val i) (q.val i), by
    constructor
    · intro i
      exact (p.property.1 i).trans (le_max_left _ _)
    · intro i
      exact max_le (p.property.2 i) (q.property.2 i)⟩

def minVector {n Bmax : ℕ} (I : SolveBox n Bmax) (p q : BoxVector I) : BoxVector I :=
  ⟨fun i => min (p.val i) (q.val i), by
    constructor
    · intro i
      exact le_min (p.property.1 i) (q.property.1 i)
    · intro i
      exact (min_le_left _ _).trans (p.property.2 i)⟩

def includeCapLow {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) (p : BoxVector (I.capLow C hC hle)) : BoxVector I :=
  ⟨p.val, p.property.1, fun i => (p.property.2 i).trans (min_le_left _ _)⟩

def includeCapHigh {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) (p : BoxVector (I.capHigh C hC hle)) : BoxVector I :=
  ⟨p.val, fun i => (le_max_left _ _).trans (p.property.1 i), p.property.2⟩

end SolveBox

def finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    RandomTree (BoxVector I) :=
  if O.chooseY then
    (RandomTree.traverse (fun H : SmallSet P =>
      I.repeated (lower (P.reweightM H.val)
        (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    up.map fun p => rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p)
  else
    (RandomTree.traverse (fun H : SmallSet P =>
      I.repeated (lower (P.reweightK H.val)
        (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    lo.map fun p => rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p)

def solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) : RandomTree (BoxVector I) :=
  if hB : I.width ≤ 128 * globalS Bmax then .leaf (I.exactVector G)
  else
    (tighten P hR lower I (lt_of_not_ge hB)).bind fun T =>
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by rw [T.width_eq]; omega
    let c := K.C
    have hc : 0 < c := K.C_positive
    have hcsmall : c < K.width := K.C_smaller hK
    (orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind fun O =>
    (finishChoice G P hR lower K hK O
      (solveWidth G P hR lower (K.capHigh c hc hcsmall.le))
      (solveWidth G P hR lower (K.capLow c hc hcsmall.le))).map T.include
termination_by I.width
decreasing_by
  all_goals
    change c < I.width
    rw [← T.width_eq]
    exact hcsmall

def solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    RandomTree (BoxVector I) :=
  if hR : P.parameter < 1 then .leaf (I.smallVector P)
  else solveWidth G P (le_of_not_gt hR) (fun Q _ K => solve G Q K) I
termination_by parameterRank P.parameter

end MeanPayoff
end

end OAI
