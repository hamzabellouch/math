import OAI.MathematicalPhysics.RapidForcing.VelocitySyntax

namespace OAI


open scoped BigOperators Topology
open Set Filter
namespace RapidForcing
namespace EffectiveProfile.Formula

lemma list_sum_range {E : Type} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  have he : (List.range n).toFinset = Finset.range n := by ext i; simp
  rw [← he]
  exact (List.sum_toFinset f (List.nodup_range (n := n))).symm

def sumVector (l : List (Fin 3 → Formula 5)) : Fin 3 → Formula 5 :=
  fun i => listSum (l.map (fun a => a i))

lemma vectorField_sumVector (l : List (Fin 3 → Formula 5)) (ν t : ℝ) (x : Space) :
    vectorField (sumVector l) ν t x = (l.map (fun a => vectorField a ν t x)).sum := by
  induction l with
  | nil => ext i; simp [sumVector, listSum, vectorField, scalarField, value]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    ext i
    simp [sumVector, listSum, value, vectorField, scalarField]

def loadFormula (M : Machine) (w : M.Input) : Fin 3 → Formula 5 :=
  moving (fun _ => 0) ![-1, (M.scaleData w).δQ 0 * M.initialDigit w, 0] 1 0

def addressFormula (M : Machine) (d : ScaleData) (n m : ℕ) : Fin 3 → Formula 5 :=
  moving ![-1, (m : ℚ) * d.δQ n, 0]
    ![-d.bQ n * (M.terminalDigit d (m % d.capacity n) : ℚ),
      d.δQ (n+1) * (M.nextDigit d n (m % d.capacity n) : ℚ), 0]
    (d.δQ n) (1 + (n : ℚ))

def stepFormula (M : Machine) (w : M.Input) (n : ℕ) : Fin 3 → Formula 5 :=
  sumVector ((List.range ((M.scaleData w).D n + 1)).map
    (addressFormula M (M.scaleData w) n))

def velocityFormula (M : Machine) (w : M.Input) (N : ℕ) : Fin 3 → Formula 5 :=
  sumVector (loadFormula M w :: (List.range N).map (stepFormula M w))

lemma vectorField_loadFormula (M : Machine) (w : M.Input) (ν t : ℝ) (x : Space) :
    vectorField (loadFormula M w) ν t x = loadingVelocity M w t x := by
  rw [loadFormula, vectorField_moving]
  have h0 : WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℝ)) = (0 : Space) := by ext i; simp
  have hv : WithLp.toLp 2 (fun i : Fin 3 =>
      ((![-1, (M.scaleData w).δQ 0 * M.initialDigit w, 0] i : ℚ) : ℝ)) =
      vec (-1) ((M.scaleData w).δ 0 * M.initialDigit w) 0 := by
    ext i
    fin_cases i <;> simp [vec]
  simp only [hv, Rat.cast_zero, h0, Rat.cast_one, sub_zero, zero_add, loadingVelocity]

lemma vectorField_addressFormula (M : Machine) (d : ScaleData) (n m : ℕ)
    (ν t : ℝ) (x : Space) :
    vectorField (addressFormula M d n m) ν t x =
      movingCurl (addressPath M d n m) (d.δ n) (t - 1 - (n : ℝ)) x := by
  rw [addressFormula, vectorField_moving]
  have ha : WithLp.toLp 2 (fun i : Fin 3 =>
      ((![-1, (m : ℚ) * d.δQ n, 0] i : ℚ) : ℝ)) = addressCenter d n m := by
    ext i
    fin_cases i <;> simp [addressCenter, vec]
  have hv : WithLp.toLp 2 (fun i : Fin 3 =>
      ((![-d.bQ n * (M.terminalDigit d (m % d.capacity n) : ℚ),
      d.δQ (n+1) * (M.nextDigit d n (m % d.capacity n) : ℚ), 0] i : ℚ) : ℝ)) =
      addressDisplacement M d n m := by
    ext i
    fin_cases i <;> simp [addressDisplacement, vec]
  simp only [ha, hv, ScaleData.cast_deltaQ, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
    sub_add_eq_sub_sub]
  rfl

lemma vectorField_stepFormula (M : Machine) (w : M.Input) (n : ℕ)
    (ν t : ℝ) (x : Space) :
    vectorField (stepFormula M w n) ν t x = stepVelocity M w n t x := by
  simp [stepFormula, vectorField_sumVector, List.map_map, Function.comp_def, vectorField_addressFormula,
    list_sum_range, stepVelocity]

lemma vectorField_velocityFormula (M : Machine) (w : M.Input) (N : ℕ)
    (ν : ℝ) : EqBefore ((N : ℝ) + 1) (addressedVelocity M w)
      (vectorField (velocityFormula M w N) ν) := by
  intro t _ ht x
  have he := congrFun (addressedVelocity_eq_finite M w N ht) x
  simpa [velocityFormula, vectorField_sumVector, List.map_map,
    Function.comp_def, vectorField_loadFormula, vectorField_stepFormula, list_sum_range,
    Finset.sum_apply] using he

def residualFormula (a : Fin 3 → Formula 5) : Fin 3 → Formula 5 := fun j =>
  (Formula.add ((a j).diff 0) (listSum ((List.finRange 3).map fun i =>
    Formula.mul (a i) ((a j).diff (spaceIndex i))))).sub
    (Formula.mul (Formula.var 4) (listSum ((List.finRange 3).map fun i =>
      ((a j).diff (spaceIndex i)).diff (spaceIndex i))))

lemma vectorField_residualFormula (a : Fin 3 → Formula 5) (ν t : ℝ)
    (ht : 0 ≤ t) (x : Space) :
    vectorField (residualFormula a) ν t x = residual ν (vectorField a ν) t x := by
  rw [residual, time_vectorField a ν t ht]
  have hs (i : Fin 3) := congrFun (congrFun (spatial_vectorField a ν i) t) x
  have hs' (i : Fin 3) : spatialD i (spatialD i (vectorField a ν)) t x =
      vectorField (fun j => ((a j).diff (spaceIndex i)).diff (spaceIndex i)) ν t x := by
    rw [spatial_vectorField, spatial_vectorField]
  ext j
  simp [residualFormula, vectorField, scalarField, value, value_sub, value_listSum,
    advection, laplace, hs, hs', Fin.sum_univ_three,
    List.finRange_succ, List.finRange_zero, pack]
  ring

end EffectiveProfile.Formula

lemma EqBefore.residual {R : ℝ} {u v : Field Space} (h : EqBefore R u v) (ν : ℝ) :
    EqBefore R (RapidForcing.residual ν u) (RapidForcing.residual ν v) := by
  intro t ht hR x
  have hs (i : Fin 3) := h.spatial i t ht hR x
  have hs' (i : Fin 3) := (h.spatial i).spatial i t ht hR x
  simp only [RapidForcing.residual, h.time t ht hR x, advection, h t ht hR x, hs,
    laplace, hs']

namespace EffectiveProfile.Formula

def forceFormula (M : Machine) (w : M.Input) (N : ℕ) : Fin 3 → Formula 5 :=
  residualFormula (velocityFormula M w N)

lemma forceFormula_correct (M : Machine) (w : M.Input) (N : ℕ) (ν : ℝ) :
    EqBefore ((N : ℝ) + 1) (addressedForce ν M w)
      (vectorField (forceFormula M w N) ν) := by
  intro t ht hN x
  exact ((vectorField_velocityFormula M w N ν).residual ν t ht hN x).trans
    (vectorField_residualFormula _ ν t ht x).symm

lemma mixed_forceFormula_correct (M : Machine) (w : M.Input) (N l : ℕ)
    (α : MultiIndex) (ν t : ℝ) (ht : 0 ≤ t) (hN : t < (N : ℝ) + 1) (x : Space) :
    mixedD l α (addressedForce ν M w) t x =
      vectorField (fun i => (forceFormula M w N i).mixed l α) ν t x :=
  ((forceFormula_correct M w N ν).mixed l α t ht hN x).trans
    (mixed_vectorField _ ν l α t ht x)

end EffectiveProfile.Formula
end RapidForcing

end OAI
