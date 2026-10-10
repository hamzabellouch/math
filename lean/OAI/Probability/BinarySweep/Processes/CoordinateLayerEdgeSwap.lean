import Mathlib
import OAI.Probability.BinarySweep.Processes.SupportTimeBoundBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma coordinateLayer_edgeSwap (d : ℕ) (j : Fin d) (x : Slot d) :
    coordinateLayer d j (fun y => decide (y = fun i : {i : Fin d // i ≠ j} => x i)) =
      Equiv.swap x (Function.update x j (!x j)) := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin d => Bool)
  let z : {i : Fin d // i ≠ j} → Bool := fun i => x i
  change (e.trans (Equiv.prodCongrLeft (fun y => boolSwitch (decide (y = z))))).trans e.symm = _
  rw [fiber_boolSwitch_eq_swap z (x j), Equiv.trans_swap_trans_symm]
  have hx : e.symm (x j, z) = x := by
    exact e.symm_apply_apply x
  have hy : e.symm (!x j, z) = Function.update x j (!x j) := by
    ext i
    by_cases h : i = j
    · subst i; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, z, Equiv.piSplitAt_symm_apply, h]
  rw [hx, hy]

lemma swap_update_mem_reachable (d : ℕ) (j : Fin d) (x : Slot d) (b : Bool) :
    Equiv.swap x (Function.update x j b) ∈ sweepReachable d := by
  classical
  by_cases h : b = x j
  · subst b
    simp only [Function.update_eq_self, Equiv.swap_self]
    exact (sweepReachable d).one_mem
  · have hb : b = !x j := by cases b <;> cases hx : x j <;> simp_all
    rw [hb, ← coordinateLayer_edgeSwap]
    exact coordinateLayer_mem_reachable d j _

lemma swap_mem_sweepReachable (d : ℕ) (x y : Slot d) :
    Equiv.swap x y ∈ sweepReachable d := by
  classical
  have h (s : Finset (Fin d)) :
      Equiv.swap x (fun i => if i ∈ s then y i else x i) ∈ sweepReachable d := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false, Equiv.swap_self]
      exact (sweepReachable d).one_mem
    | @insert j s hj ih =>
      have he : (fun i => if i ∈ insert j s then y i else x i) =
          Function.update (fun i => if i ∈ s then y i else x i) j (y j) := by
        ext i
        by_cases hi : i = j
        · subst i; simp
        · simp [hi]
      rw [he]
      exact SubmonoidClass.swap_mem_trans (sweepReachable d) ih
        (swap_update_mem_reachable d j _ _)
  simpa using h Finset.univ

theorem every_permutation_sweepReachable (d : ℕ) (g : Equiv.Perm (Slot d)) :
    g ∈ sweepReachable d := by
  classical
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact (sweepReachable d).one_mem
  | swap_mul g x y h ih =>
    exact (sweepReachable d).mul_mem (swap_mem_sweepReachable d x y) ih

section FiniteRandomWalk
variable {G : Type*} [Fintype G] [Group G]

def IsProbability (p : G → ℝ) : Prop := (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1

lemma sum_mulLeft (a : G) (f : G → ℝ) : ∑ g, f (a * g) = ∑ g, f g :=
  Equiv.sum_comp (Equiv.mulLeft a) f

lemma sum_inv_mulRight (a : G) (f : G → ℝ) : ∑ g, f (g⁻¹ * a) = ∑ g, f g :=
  ((Equiv.inv G).trans (Equiv.mulRight a)).sum_comp f

lemma convolution_sum (p q : G → ℝ) :
    ∑ g, convolution p q g = (∑ g, p g) * (∑ g, q g) := by
  simp only [convolution]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_mulLeft]
  rw [Finset.sum_mul]

lemma convolution_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ convolution p q g := fun _ =>
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hq _))

lemma convolution_probability {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    IsProbability (convolution p q) := by
  exact ⟨convolution_nonneg hp.1 hq.1, by rw [convolution_sum, hp.2, hq.2, one_mul]⟩

lemma convolution_uniform_right {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution p (uniformLaw G) = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.sum_mul, hp]

lemma convolution_uniform_left {p : G → ℝ} (hp : ∑ g, p g = 1) :
    convolution (uniformLaw G) p = uniformLaw G := by
  funext g
  simp [convolution, uniformLaw, ← Finset.mul_sum, sum_inv_mulRight, hp]

lemma convolution_assoc (p q r : G → ℝ) :
    convolution (convolution p q) r = convolution p (convolution q r) := by
  funext g
  simp only [convolution, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← sum_mulLeft x (fun y => p x * q (x⁻¹ * y) * r (y⁻¹ * g))]
  simp [mul_assoc]

omit [Group G] in
lemma totalVariation_nonneg (p q : G → ℝ) : 0 ≤ totalVariation p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

omit [Group G] in
lemma totalVariation_le_one {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    totalVariation p q ≤ 1 := by
  have h : ∑ g, |p g - q g| ≤ 2 := by
    calc
      _ ≤ ∑ g, (p g + q g) := Finset.sum_le_sum (fun g _ =>
        (abs_sub (p g) (q g)).trans_eq (by rw [abs_of_nonneg (hp.1 g), abs_of_nonneg (hq.1 g)]))
      _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num
  unfold totalVariation
  linarith

lemma convolution_tv_contract {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (q r : G → ℝ) :
    totalVariation (convolution p q) (convolution p r) ≤
      (∑ g, p g) * totalVariation q r := by
  have h : ∑ g, |convolution p q g - convolution p r g| ≤
      (∑ g, p g) * ∑ g, |q g - r g| := by
    calc
      _ = ∑ g, |∑ x, p x * (q (x⁻¹ * g) - r (x⁻¹ * g))| := by
        simp_rw [convolution, ← Finset.sum_sub_distrib, ← mul_sub]
      _ ≤ ∑ g, ∑ x, p x * |q (x⁻¹ * g) - r (x⁻¹ * g)| := by
        apply Finset.sum_le_sum
        intro g _
        simpa only [abs_mul, abs_of_nonneg (hp _)] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun x => p x * (q (x⁻¹ * g) - r (x⁻¹ * g))))
      _ = _ := by
        rw [Finset.sum_comm]
        have hs (x : G) : ∑ g, |q (x⁻¹ * g) - r (x⁻¹ * g)| = ∑ g, |q g - r g| :=
          sum_mulLeft x⁻¹ (fun g => |q g - r g|)
        simp_rw [← Finset.mul_sum, hs]
        rw [Finset.sum_mul]
  unfold totalVariation
  nlinarith

end FiniteRandomWalk

abbrev GridSlot {b : ℕ} (bits : Fin b → ℕ) := (j : Fin b) → Slot (bits j)
abbrev GridOutside {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :=
  (i : {i : Fin b // i ≠ j}) → Slot (bits i)
abbrev GridChoices {b : ℕ} (bits : Fin b → ℕ) :=
  (j : Fin b) → GridOutside bits j → Equiv.Perm (Slot (bits j))

def gridSize {b : ℕ} (bits : Fin b → ℕ) := ∏ j, 2 ^ bits j

lemma card_gridSlot {b : ℕ} (bits : Fin b → ℕ) :
    Fintype.card (GridSlot bits) = gridSize bits := by
  simp [GridSlot, Slot, gridSize, Fintype.card_pi]

def gridLayer {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    Equiv.Perm (GridSlot bits) :=
  let e := Equiv.piSplitAt j (fun i => Slot (bits i))
  e.trans ((Equiv.prodCongrLeft (g j)).trans e.symm)

def gridSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    Equiv.Perm (GridSlot bits) := (List.ofFn (gridLayer bits g)).reverse.prod

def lineLaw (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) : ℝ :=
  (1 - z) * uniformLaw (Equiv.Perm (Slot d)) g + z * binaryLaw d g

def gridWeight {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) (g : GridChoices bits) : ℝ :=
  ∏ j, ∏ y, lineLaw (bits j) z (g j y)

structure PathFamily {b : ℕ} (bits : Fin b → ℕ) (h : ℕ) where
  position : Fin (b + 1) → Fin h → GridSlot bits
  disjoint : ∀ t, Function.Injective (position t)
  changes_only_stage : ∀ (j : Fin b) (k : Fin h) (i : Fin b), i ≠ j →
    position j.succ k i = position j.castSucc k i

def pathEvent {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : Prop :=
  ∀ (j : Fin b) (k : Fin h),
    gridLayer bits g j (H.position j.castSucc k) = H.position j.succ k

lemma chronological_trajectory {α : Type*} (b : ℕ) (f : Fin b → Equiv.Perm α)
    (x : Fin (b + 1) → α) (h : ∀ j, f j (x j.castSucc) = x j.succ) :
    (List.ofFn f).reverse.prod (x 0) = x (Fin.last b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp only [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton,
      Equiv.Perm.mul_apply]
    have h0 : f 0 (x 0) = x (Fin.succ 0) := by simpa using h 0
    rw [h0]
    have ht (j : Fin b) : f j.succ (x j.castSucc.succ) = x j.succ.succ := by
      simpa only [Fin.succ_castSucc] using h j.succ
    exact ih (fun j => f j.succ) (fun i => x i.succ) ht

end BinaryCoordinateSweeps
end

end OAI
