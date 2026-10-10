import Mathlib

namespace OAI

/-! Bounded Hochschild cochains, last-input translation and averaging. -/

noncomputable section


namespace BoundedHochschild

abbrev Cochain (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin n => M) M

 
def mergeInputs {M : Type*} [Mul M] {n : ℕ}
    (v : Fin (n + 1) → M) (j : Fin n) : Fin n → M :=
  fun i => if i < j then v i.castSucc
    else if i = j then v i.castSucc * v i.succ else v i.succ

 

noncomputable def differentialValue {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]
    {n : ℕ} (f : Cochain M n) (v : Fin (n + 1) → M) : M :=
  v 0 * f (fun i => v i.succ) +
    ∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (mergeInputs v j) +
    ((-1 : ℂ) ^ (n + 1)) • (f (fun i => v i.castSucc) * v (Fin.last n))

section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

@[simp] theorem differentialValue_add {n : ℕ} (f g : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (f + g) v = differentialValue f v + differentialValue g v := by
  simp only [differentialValue, add_apply, mul_add, add_mul,
    smul_add, Finset.sum_add_distrib]
  abel

@[simp] theorem differentialValue_smul {n : ℕ} (c : ℂ) (f : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (c • f) v = c • differentialValue f v := by
  simp only [differentialValue, smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm c]
  · rw [mul_comm c]

 
noncomputable def insertLast {n : ℕ} (f : Cochain M (n + 1)) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.apply ℂ M) u).compContinuousMultilinearMap f.curryRight

@[simp] theorem insertLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : M)
    (v : Fin n → M) : insertLast f u v = f (Fin.snoc v u) := rfl

theorem norm_insertLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : M) :
    ‖insertLast f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  simpa [mul_assoc, mul_left_comm, mul_comm] using f.norm_map_snoc_le v u

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

theorem snoc_succ_tuple {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    (fun i : Fin (n + 1) => (Fin.snoc v u : Fin (n + 2) → M) i.succ) =
      Fin.snoc (fun i : Fin n => v i.succ) u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [← Fin.castSucc_succ, Fin.snoc_castSucc]

theorem snoc_castSucc_tuple {n : ℕ} (v : Fin n → M) (u : M) :
    (fun i : Fin n => (Fin.snoc v u : Fin (n + 1) → M) i.castSucc) = v := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => M) u v i

@[simp] theorem mergeInputs_snoc_castSucc [Mul M] {n : ℕ} (v : Fin (n + 1) → M)
    (u : M) (j : Fin n) :
    mergeInputs (Fin.snoc v u) j.castSucc = Fin.snoc (mergeInputs v j) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hlt : ¬ Fin.last n < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
    have heq : Fin.last n ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [mergeInputs, hlt, heq]
  · simp [mergeInputs, ← Fin.castSucc_succ]

@[simp] theorem mergeInputs_snoc_last [Mul M] {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    mergeInputs (Fin.snoc v u) (Fin.last n) =
      Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]

end TupleIdentities

section CocycleIdentity
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

 
theorem differentialValue_snoc {n : ℕ} (f : Cochain M (n + 1))
    (v : Fin (n + 1) → M) (u : M) :
    differentialValue f (Fin.snoc v u) =
      v 0 * f (Fin.snoc (fun i : Fin n => v i.succ) u) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (Fin.snoc (mergeInputs v j) u)) +
      ((-1 : ℂ) ^ (n + 1)) •
        f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u)) +
      ((-1 : ℂ) ^ (n + 2)) • (f v * u) := by
  rw [differentialValue, snoc_succ_tuple, snoc_castSucc_tuple, Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc, Fin.val_castSucc, mergeInputs_snoc_last,
    Fin.val_last, Fin.snoc_last]
  have hzero : (Fin.snoc v u : Fin (n + 2) → M) 0 = v 0 := by
    exact Fin.snoc_castSucc (α := fun _ => M) u v 0
  rw [hzero]
  abel

 
noncomputable def rightMultiply {n : ℕ} (f : Cochain M n) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.mul ℂ M).flip u).compContinuousMultilinearMap f

@[simp] theorem rightMultiply_apply {n : ℕ} (f : Cochain M n) (u : M)
    (v : Fin n → M) : rightMultiply f u v = f v * u := rfl

 
noncomputable def lastHomotopy {n : ℕ} (f : Cochain M (n + 1)) (u v : M) : Cochain M n :=
  rightMultiply (insertLast f u) v

@[simp] theorem lastHomotopy_apply {n : ℕ} (f : Cochain M (n + 1)) (u v : M)
    (x : Fin n → M) : lastHomotopy f u v x = f (Fin.snoc x u) * v := rfl

theorem norm_rightMultiply_le {n : ℕ} (f : Cochain M n) (u : M) :
    ‖rightMultiply f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖rightMultiply f u v‖ ≤ ‖f v‖ * ‖u‖ := norm_mul_le _ _
    _ ≤ (‖f‖ * ∏ i, ‖v i‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (f.le_opNorm v) (norm_nonneg _)
    _ = (‖f‖ * ‖u‖) * ∏ i, ‖v i‖ := by ring

theorem norm_lastHomotopy_le {n : ℕ} (f : Cochain M (n + 1)) (u v : M) :
    ‖lastHomotopy f u v‖ ≤ ‖f‖ * ‖u‖ * ‖v‖ := by
  exact (norm_rightMultiply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_insertLast_le _ _) (norm_nonneg _))

 

theorem lastHomotopy_cocycle {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x : Fin (n + 2) → M, differentialValue f x = 0)
    (u u' : M) (hu : u * u' = 1) (x : Fin (n + 1) → M) :
    differentialValue (lastHomotopy f u u') x =
      ((-1 : ℂ) ^ (n + 1)) •
        (f x - f (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) * u)) * u' +
          (lastHomotopy f u u' (fun i : Fin n => x i.castSucc)) * x (Fin.last n)) := by
  have hz := congrArg (fun y : M => y * u') (hf (Fin.snoc x u))
  rw [differentialValue_snoc] at hz
  simp only [add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc, hu, mul_one,
    zero_mul] at hz
  have hp : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul] at hz
  simp only [differentialValue, lastHomotopy_apply, mul_assoc, smul_add, smul_sub]
  apply eq_of_sub_eq_zero
  rw [sub_eq_add_neg]
  have hz' := hz
  abel_nf at hz' ⊢
  simpa only [add_assoc, add_left_comm, add_comm] using hz'

end CocycleIdentity

section UnitaryAveraging
variable {M : Type*} [CStarAlgebra M]

noncomputable def translateLast {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    Cochain M (n + 1) :=
  rightMultiply
    (f.compContinuousLinearMap (fun i : Fin (n + 1) =>
      if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
      else ContinuousLinearMap.id ℂ M)) (star (u : M))

@[simp] theorem translateLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M)
    (x : Fin (n + 1) → M) :
    translateLast f u x =
      f (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) * u)) * star (u : M) := by
  change f (fun i => (if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
    else ContinuousLinearMap.id ℂ M) (x i)) * star (u : M) = _
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem norm_translateLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    ‖translateLast f u‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [translateLast_apply]
  have hnorm (z : M) : ‖z * star (u : M)‖ = ‖z‖ :=
    CStarRing.norm_mul_coe_unitary z (star u)
  rw [hnorm]
  calc
    _ ≤ ‖f‖ * (∏ i : Fin n, ‖x i.castSucc‖) * ‖x (Fin.last n) * (u : M)‖ :=
      f.norm_map_snoc_le _ _
    _ = ‖f‖ * ∏ i, ‖x i‖ := by
      rw [CStarRing.norm_mul_coe_unitary, Fin.prod_univ_castSucc, mul_assoc]

@[simp] theorem translateLast_add {n : ℕ} (f g : Cochain M (n + 1)) (u : unitary M) :
    translateLast (f + g) u = translateLast f u + translateLast g u := by
  ext x
  simp [add_mul]

@[simp] theorem translateLast_smul {n : ℕ} (c : ℂ) (f : Cochain M (n + 1)) (u : unitary M) :
    translateLast (c • f) u = c • translateLast f u := by
  ext x
  simp

 
noncomputable def averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (f : Cochain M (n + 1)) : Cochain M (n + 1) :=
  ∑' j, (p j : ℂ) • translateLast f (u j)

theorem summable_averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (f : Cochain M (n + 1)) :
    Summable (fun j => (p j : ℂ) • translateLast f (u j)) := by
  refine (hs.mul_right ‖f‖).of_norm_bounded (fun j => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)

theorem norm_averageLast_le {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) (f : Cochain M (n + 1)) :
    ‖averageLast p u f‖ ≤ ‖f‖ := by
  have hbound (j : ℕ) : ‖(p j : ℂ) • translateLast f (u j)‖ ≤ p j * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
    exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)
  simpa [averageLast] using tsum_of_norm_bounded (hs.mul_right ‖f‖) hbound

end UnitaryAveraging

end BoundedHochschild
end

end OAI
