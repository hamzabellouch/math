import OAI.MathematicalPhysics.Heisenberg.LocalAlgebra

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace SpinEvolution

section
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]

def leftRegular : E →ₐ[ℂ] (E →L[ℂ] E) where
  toFun := ContinuousLinearMap.mul ℂ E
  map_zero' := by ext A; simp
  map_one' := by ext A; simp
  map_add' H K := by ext A; simp
  map_mul' H K := by ext A; simp [mul_assoc]
  commutes' z := by ext A; simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma leftRegular_apply (H A : E) : leftRegular H A = H*A := rfl

lemma leftRegular_continuous : Continuous (leftRegular : E → E →L[ℂ] E) :=
  (ContinuousLinearMap.mul ℂ E).continuous

def rightRegular : Eᵐᵒᵖ →ₐ[ℂ] (E →L[ℂ] E) where
  toFun H := (ContinuousLinearMap.mul ℂ E).flip H.unop
  map_zero' := by ext A; simp
  map_one' := by ext A; simp
  map_add' H K := by ext A; simp
  map_mul' H K := by ext A; simp [mul_assoc]
  commutes' z := by ext A; simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma rightRegular_apply (H : Eᵐᵒᵖ) (A : E) : rightRegular H A = A*H.unop := rfl

lemma rightRegular_continuous : Continuous (rightRegular : Eᵐᵒᵖ → E →L[ℂ] E) :=
  (ContinuousLinearMap.mul ℂ E).flip.continuous.comp MulOpposite.continuous_unop

lemma left_right_commute (H K : E) :
    Commute (leftRegular H) (rightRegular (MulOpposite.op K)) := by
  ext A
  simp [mul_assoc]

variable [CompleteSpace E]

lemma exp_left (H : E) : NormedSpace.exp (leftRegular H) = leftRegular (NormedSpace.exp H) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact (NormedSpace.map_exp leftRegular leftRegular_continuous H).symm

lemma exp_right (H : E) : NormedSpace.exp (rightRegular (MulOpposite.op H)) =
    rightRegular (MulOpposite.op (NormedSpace.exp H)) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  simpa only [NormedSpace.exp_op] using
    (NormedSpace.map_exp (rightRegular (E := E)) rightRegular_continuous
      (MulOpposite.op H)).symm

theorem exp_left_add_right (H K A : E) :
    NormedSpace.exp (leftRegular H + rightRegular (MulOpposite.op K)) A =
      NormedSpace.exp H * A * NormedSpace.exp K := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [NormedSpace.exp_add_of_commute (left_right_commute H K), exp_left, exp_right]
  simp [mul_assoc]

def generator (H : E) : E →L[ℂ] E :=
  leftRegular (Complex.I • H) + rightRegular (MulOpposite.op ((-Complex.I) • H))

omit [CompleteSpace E] in
@[simp] lemma generator_apply (H A : E) : generator H A = Complex.I • (H*A-A*H) := by
  simp [generator, sub_eq_add_neg]

omit [CompleteSpace E] in
lemma time_generator (H : E) (z : ℂ) :
    z • generator H = leftRegular ((z*Complex.I) • H) +
      rightRegular (MulOpposite.op ((-(z*Complex.I)) • H)) := by
  ext A
  simp [generator, smul_add, smul_smul]

theorem exp_generator (H A : E) (z : ℂ) :
    NormedSpace.exp (z • generator H) A =
      NormedSpace.exp ((z*Complex.I) • H) * A * NormedSpace.exp ((-(z*Complex.I)) • H) := by
  rw [time_generator, exp_left_add_right]

lemma exp_operator_apply (D : E →L[ℂ] E) (A : E) :
    NormedSpace.exp D A = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • (D^n) A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact (ContinuousLinearMap.apply ℂ E A).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) D)

theorem dynamics_series (H A : E) (z : ℂ) :
    NormedSpace.exp ((z*Complex.I) • H) * A * NormedSpace.exp ((-(z*Complex.I)) • H) =
      ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * z^n) • ((generator H)^n) A := by
  rw [← exp_generator, exp_operator_apply]
  apply tsum_congr
  intro n
  have hp : ((z • generator H)^n) A = z^n • ((generator H)^n) A := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp,
        smul_apply, ih, map_smul, smul_smul]
      rw [mul_comm]
  rw [hp, smul_smul]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

structure LocalDecomposition (D : E →L[ℂ] E) (Local : ℕ → E → Prop) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  split : ∀ k A, Local k A → ∃ (r : ℕ) (g : Fin r → E),
    D A = ∑ i, g i ∧ (∀ i, Local (k+1) (g i)) ∧
      ∑ i, ‖g i‖ ≤ C * (k+1) * ‖A‖

theorem LocalDecomposition.power_bound {D : E →L[ℂ] E} {Local : ℕ → E → Prop}
    {C : ℝ} (h : LocalDecomposition D Local C) (n k : ℕ) (A : E) (hA : Local k A) :
    ‖(D^n) A‖ ≤ C^n * ((k+1).ascFactorial n : ℝ) * ‖A‖ := by
  induction n generalizing k A with
  | zero => simp
  | succ n ih =>
    obtain ⟨r, g, hsum, hloc, hnorm⟩ := h.split k A hA
    have hc : 0 ≤ C^n * ((k+2).ascFactorial n : ℝ) := mul_nonneg (pow_nonneg h.nonneg _) (Nat.cast_nonneg _)
    calc
      ‖(D^(n+1)) A‖ = ‖∑ i, (D^n) (g i)‖ := by
        rw [pow_succ, mul_apply_eq_comp, hsum, map_sum]
      _ ≤ ∑ i, ‖(D^n) (g i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, C^n * ((k+2).ascFactorial n : ℝ) * ‖g i‖ :=
        Finset.sum_le_sum (fun i _ => ih (k+1) (g i) (hloc i))
      _ = (C^n * ((k+2).ascFactorial n : ℝ)) * ∑ i, ‖g i‖ := by
        rw [Finset.mul_sum]
      _ ≤ (C^n * ((k+2).ascFactorial n : ℝ)) * (C*(k+1)*‖A‖) :=
        mul_le_mul_of_nonneg_left hnorm hc
      _ = C^(n+1) * ((k+1).ascFactorial (n+1) : ℝ) * ‖A‖ := by
        rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
        push_cast
        ring

lemma summable_ascFactorial {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    Summable (fun n : ℕ => q^n * ((k+1).ascFactorial n : ℝ) / n.factorial) := by
  have heq (n : ℕ) : q^n * ((k+1).ascFactorial n : ℝ) / n.factorial =
      ((k+n).choose k : ℝ) * q^n := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose, ← Nat.choose_symm_add]
    push_cast
    field_simp
  simp_rw [heq]
  have hs : Summable (fun n : ℕ => ((k+n : ℕ) : ℝ)^k * q^n) := by
    have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
    have hs (j : ℕ) : Summable (fun n : ℕ =>
        ((k : ℝ)^j * (k.choose j : ℝ)) * ((n : ℝ)^(k-j) * q^n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one (k-j) hqnorm).mul_left _
    convert (summable_sum (s := Finset.range (k+1)) (fun j _ => hs j)) using 1
    ext n
    rw [Nat.cast_add, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow (k+n) k)
      (pow_nonneg hq n)) hs

end SpinEvolution

namespace Heisenberg
def neighbors {d : ℕ} (x : Site d) : Finset (Site d) :=
  Finset.univ.biUnion fun i =>
    {Function.update x i (x i + 1), Function.update x i (x i - 1)}

lemma nearestNeighbor_symm {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  unfold NearestNeighbor at *
  simpa only [abs_sub_comm] using h

lemma nearestNeighbor_coordinate {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    ∃ i, (y i = x i + 1 ∨ y i = x i - 1) ∧ ∀ j, j ≠ i → y j = x j := by
  have hi : ∃ i, x i ≠ y i := by
    by_contra! hh
    have : ∑ i : Fin d, |x i - y i| = (0 : ℤ) := by simp [hh]
    change ∑ i : Fin d, |x i - y i| = (1 : ℤ) at h
    omega
  obtain ⟨i, hi⟩ := hi
  have hain : 1 ≤ |x i-y i| := by
    have hn : x i-y i ≠ 0 := sub_ne_zero.mpr hi
    have := abs_pos.mpr hn
    omega
  have hai : |x i-y i| ≤ 1 := by
    change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
    rw [← h]
    exact Finset.single_le_sum (f := fun j : Fin d => |x j - y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨i, ?_, ?_⟩
  · have hab : x i-y i = 1 ∨ x i-y i = -1 := by
      have : |x i-y i| = 1 := le_antisymm hai hain
      exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp this
    omega
  · intro j hji
    have hsum : |x i-y i| + |x j-y j| ≤ (1 : ℤ) := by
      change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
      rw [← h]
      rw [← Finset.sum_pair (f := fun j : Fin d => |x j-y j|) (Ne.symm hji)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    have : |x j-y j| = 0 := le_antisymm (by omega) (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp this)).symm

lemma mem_neighbors_of_nearestNeighbor {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    y ∈ neighbors x := by
  obtain ⟨i, hi, he⟩ := nearestNeighbor_coordinate h
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rcases hi with hi | hi
  · have hy : y = Function.update x i (x i+1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]
  · have hy : y = Function.update x i (x i-1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]

lemma card_neighbors_le {d : ℕ} (x : Site d) : (neighbors x).card ≤ 2*d := by
  calc
    (neighbors x).card ≤ ∑ i : Fin d,
        ({Function.update x i (x i+1), Function.update x i (x i-1)} : Finset (Site d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin d, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
    _ = 2*d := by simp [mul_comm]

def incidentEdges {d : ℕ} (F : Finset (Site d)) : Finset (Site d × Site d) :=
  F.biUnion fun x => ((neighbors x).image (fun y => (x,y))) ∪
    ((neighbors x).image (fun y => (y,x)))

lemma mem_incidentEdges {d : ℕ} {F : Finset (Site d)} {x y : Site d}
    (h : NearestNeighbor x y) (hm : x ∈ F ∨ y ∈ F) : (x,y) ∈ incidentEdges F := by
  rcases hm with hx | hy
  · exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y, mem_neighbors_of_nearestNeighbor h, rfl⟩)⟩
  · exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, mem_neighbors_of_nearestNeighbor (nearestNeighbor_symm h), rfl⟩)⟩

lemma card_incidentEdges_le {d : ℕ} (F : Finset (Site d)) :
    (incidentEdges F).card ≤ (4*d)*F.card := by
  calc
    _ ≤ ∑ x ∈ F, (((neighbors x).image (fun y => (x,y))) ∪
        ((neighbors x).image (fun y => (y,x)))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4*d := by
      apply Finset.sum_le_sum
      intro x _
      exact (Finset.card_union_le _ _).trans ((add_le_add
        ((Finset.card_image_le).trans (card_neighbors_le x))
        ((Finset.card_image_le).trans (card_neighbors_le x))).trans (by omega))
    _ = (4*d)*F.card := by simp [mul_comm]

def neighborhood {d : ℕ} (F : Finset (Site d)) : Finset (Site d) :=
  F ∪ F.biUnion neighbors

lemma subset_neighborhood {d : ℕ} (F : Finset (Site d)) : F ⊆ neighborhood F :=
  Finset.subset_union_left

lemma nearestNeighbor_mem_neighborhood {d : ℕ} {F : Finset (Site d)} {x y : Site d}
    (h : NearestNeighbor x y) (hm : x ∈ F ∨ y ∈ F) :
    x ∈ neighborhood F ∧ y ∈ neighborhood F := by
  rcases hm with hx | hy
  · exact ⟨subset_neighborhood F hx, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, hx, mem_neighbors_of_nearestNeighbor h⟩)⟩
  · exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨y, hy, mem_neighbors_of_nearestNeighbor (nearestNeighbor_symm h)⟩),
      subset_neighborhood F hy⟩

end Heisenberg
end

end OAI
