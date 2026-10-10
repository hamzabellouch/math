import OAI.GroupTheory.Kervaire.MatrixShifts

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

/-- The finite clock advances by a root of unity, including at the cut. -/
theorem clock_rotate {n : ℕ} (z : ℂ) (hz : z^(n+1) = 1) (i : Fin (n+1)) :
    z^((finRotate (n+1) i).val) = z * z^i.val := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
    rw [← pow_succ']
    exact hz.symm
  · rw [coe_finRotate_of_ne_last hi, pow_succ']

/-- Rephasing a labelled weighted cycle implements scalar rotation exactly. -/
theorem clock_weightedShift (n : ℕ) (z : ℂ) (hz : z^(n+1) = 1)
    (u : Fin (n+1) → ℂ) (a : Fin (n+1) → A) :
    scalarDiagonal (A := A) (fun i : Fin (n+1) => z^i.val) *
        weightedShift (finRotate (n+1)) u a =
      z • (weightedShift (finRotate (n+1)) u a *
        scalarDiagonal (fun i : Fin (n+1) => z^i.val)) := by
  apply ext_delta
  rintro ⟨i,x⟩
  simp only [mul_apply_eq_comp, weightedShift_delta, map_smul,
    scalarDiagonal_delta, smul_apply, smul_smul]
  rw [clock_rotate z hz i]
  congr 1
  ring

/-- Spectral phase of a finite weighted cycle is invariant under every clock rotation. -/
theorem phase_weightedShift_root (n : ℕ) (z : ℂ) (hz : z^(n+1) = 1)
    (hzu : z ∈ unitary ℂ) (u : Fin (n+1) → ℂ) (a : Fin (n+1) → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨z,hzu⟩ (weightedShift_unitary (finRotate (n+1)) u a hu))
    KervaireMatrix.phase (z • weightedShift (finRotate (n+1)) u a) =
      KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) := by
  classical
  let : DecidableEq (Fin (n+1)) := Classical.decEq _
  let T := weightedShift (finRotate (n+1)) u a
  let Q := scalarDiagonal (A := A) (fun i : Fin (n+1) => z^i.val)
  have hT : T ∈ unitary (Operator (Fin (n+1)) A) := weightedShift_unitary (finRotate (n+1)) u a hu
  have hQ : Q ∈ unitary (Operator (Fin (n+1)) A) :=
    scalarDiagonal_unitary _ (fun i => pow_mem hzu i.val)
  have hc : Q*T*star Q = z • T := by
    rw [show Q*T = z • (T*Q) from clock_weightedShift n z hz u a,
      smul_mul_assoc, mul_assoc, (Unitary.mem_iff.mp hQ).2, mul_one]
  let _ := isStarNormal_of_mem_unitary hT
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hzu⟩ hT)
  simpa only [hc] using phase_conjugate T Q hT hQ
    (weightedShift_mem_commutant _ u a)
    (by simpa only [Q, scalarDiagonal] using
      scalarTensor_mem_commutant (A := A) (Matrix.diagonal (fun i : Fin (n+1) => z^i.val)))

/-- The exact first half of the boundary-cycle phase computation. -/
theorem phase_weightedShift_grid (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary (pow_mem (weightedShift_unitary (finRotate (n+1)) u a hu) (n+1))
    (n+1 : ℝ) * KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) =
      (n+1 : ℝ) * (n : ℝ)/2 +
        KervaireMatrix.phase ((weightedShift (finRotate (n+1)) u a)^(n+1)) := by
  let T := weightedShift (finRotate (n+1)) u a
  have hT := weightedShift_unitary (finRotate (n+1)) u a hu
  let _ := isStarNormal_of_mem_unitary hT
  let _ := isStarNormal_of_mem_unitary (pow_mem hT (n+1))
  have h := phase_grid T hT (n+1) (Nat.succ_pos n)
  have he (j : Fin (n+1)) :
      KervaireMatrix.phase (scalarRotation ((j.val : ℝ)/(n+1)) • T) =
        KervaireMatrix.phase T :=
    phase_weightedShift_root n _ (by simpa using scalarRotation_grid_pow j.val (n+1) (Nat.succ_pos n))
      (scalarRotation_unitary _) u a hu
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp_rw [he] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem vectorPhase_eq_of_moments (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : H) (η : K)
    (hm : ∀ n : ℕ, inner ℂ ξ ((U^n) ξ) = inner ℂ η ((V^n) η)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    vectorPhase U ξ = vectorPhase V η := by
  simpa only [sumPhase, vectorSum_apply, Fintype.sum_unique] using
    sumPhase_eq_of_moments U V hU hV (fun _ : Unit => ξ) (fun _ : Unit => η)
      (fun n => by simpa only [vectorSum_apply, Fintype.sum_unique, vectorCLM_apply] using hm n)
end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

def leftOperator (a : A) : Operator A := (left a).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftOperator_delta (a x : A) :
    leftOperator a (delta x) = delta (a*x) := left_delta a x

@[simp] theorem leftOperator_one : leftOperator (1 : A) = 1 := by
  ext f x
  simp [leftOperator]

theorem leftOperator_mul (a b : A) : leftOperator (a*b) = leftOperator a * leftOperator b := by
  ext f x
  simp [leftOperator, mul_apply_eq_comp]

@[simp] theorem leftOperator_pow (a : A) (n : ℕ) : leftOperator (a^n) = leftOperator a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leftOperator_mul, ih, pow_succ]

theorem leftOperator_unitary (a : A) : leftOperator a ∈ unitary (Operator A) := by
  rw [Unitary.mem_iff]
  have hs : star (leftOperator a) = leftOperator a⁻¹ := by
    change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    ext f x
    simp [leftOperator, left, reindex_symm, reindex_apply]
  rw [hs, ← leftOperator_mul, ← leftOperator_mul]
  simp

/-- Exact scalar-rotated fractional phase of a group element. -/
def groupPhase (z : ℂ) (hz : z ∈ unitary ℂ) (a : A) : ℝ :=
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary a))
  vectorPhase (z • leftOperator a) (delta 1)

/-- Scalar moments really are the coefficients of the left-regular circuit word. -/
theorem moment_group_weight (z : ℂ) (a : A) (n : ℕ) :
    inner ℂ (delta (1 : A)) (((z • leftOperator a)^n) (delta 1)) =
      if a^n = 1 then z^n else 0 := by
  classical
  rw [smul_pow, ← leftOperator_pow]
  simp only [smul_apply, leftOperator_delta, mul_one, inner_smul_right, inner_delta_left]
  simp [delta, Pi.single_apply, eq_comm]

/-- Changing the starting point of a labelled circuit preserves its exact phase. -/
theorem groupPhase_conjugate (z : ℂ) (hz : z ∈ unitary ℂ) (a b : A) :
    groupPhase z hz (b*a*b⁻¹) = groupPhase z hz a := by
  apply vectorPhase_eq_of_moments _ _
    (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary _))
    (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary _)) (delta 1) (delta 1)
  intro n
  change inner ℂ (delta 1) (((z • leftOperator (b*a*b⁻¹))^n) (delta 1)) =
    inner ℂ (delta 1) (((z • leftOperator a)^n) (delta 1))
  rw [moment_group_weight, moment_group_weight, conj_pow]
  congr 1
  apply propext
  constructor
  · intro h
    have hh := congrArg (fun x => b⁻¹*x*b) h
    simpa [mul_assoc] using hh
  · intro h
    simp [h]
end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

theorem weightedDiagonal_pow_delta (u : D → ℂ) (a : D → A)
    (n : ℕ) (i : D) (x : A) :
    (weightedShift (Equiv.refl D) u a ^ n) (delta (i,x)) =
      u i ^ n • delta (i,a i ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, weightedShift_delta]
    simp only [Equiv.refl_apply, smul_smul, pow_succ', mul_assoc]
    congr 1
    ring

/-- The phase of the diagonal circuit power is the sum of the literal regular phases. -/
theorem phase_weightedDiagonal (u : D → ℂ) (a : D → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (Equiv.refl D) u a hu)
    phase (weightedShift (Equiv.refl D) u a) = ∑ i, groupPhase (u i) (hu i) (a i) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (Equiv.refl D) u a hu)
  apply Finset.sum_congr rfl
  intro i _
  apply vectorPhase_eq_of_moments _ _
    (weightedShift_unitary (Equiv.refl D) u a hu)
    (Unitary.smul_mem ⟨u i,hu i⟩ (leftOperator_unitary (a i)))
    (delta (i,(1 : A))) (delta 1)
  intro n
  classical
  change inner ℂ (delta (i,1)) ((weightedShift (Equiv.refl D) u a ^ n) (delta (i,1))) =
    inner ℂ (delta 1) (((u i • leftOperator (a i)) ^ n) (delta 1))
  rw [weightedDiagonal_pow_delta, moment_group_weight]
  simp only [mul_one, inner_smul_right, inner_delta_left]
  simp [delta, Pi.single_apply, eq_comm]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

/-- Circuit weights in their actual operator multiplication order. -/
def orbitWeight (σ : Equiv.Perm D) (b : D → B) : ℕ → D → B
  | 0, _ => 1
  | n+1, i => b ((σ^n) i) * orbitWeight σ b n i

@[simp] theorem orbitWeight_zero (σ : Equiv.Perm D) (b : D → B) (i : D) :
    orbitWeight σ b 0 i = 1 := rfl
@[simp] theorem orbitWeight_succ (σ : Equiv.Perm D) (b : D → B) (n : ℕ) (i : D) :
    orbitWeight σ b (n+1) i = b ((σ^n) i) * orbitWeight σ b n i := rfl

/-- Cutting an oriented circuit respects the noncommutative order of labels. -/
theorem orbitWeight_add (σ : Equiv.Perm D) (b : D → B) (n m : ℕ) (i : D) :
    orbitWeight σ b (n+m) i =
      orbitWeight σ b n ((σ^m) i) * orbitWeight σ b m i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, orbitWeight_succ, ih, orbitWeight_succ, pow_add]
    simp only [Equiv.Perm.mul_apply, mul_assoc]

/-- A circuit with trivial permutation has conjugate weights at successive points. -/
theorem orbitWeight_cycle (σ : Equiv.Perm D) (b : D → B) (n : ℕ)
    (hn : σ^n = 1) (i : D) :
    orbitWeight σ b n (σ i) * b i = b i * orbitWeight σ b n i := by
  have h := orbitWeight_add σ b n 1 i
  simpa [orbitWeight_succ, hn] using h.symm

/-- The rotate permutation is addition modulo its size. -/
theorem rotate_pow_apply (d : ℕ) [NeZero d] (n : ℕ) (i : Fin d) :
    ((finRotate d)^n) i = i + (↑n : Fin d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, ih]
    simp [Nat.cast_add, add_assoc]

@[simp] theorem rotate_pow_self (d : ℕ) [NeZero d] : (finRotate d)^d = 1 := by
  ext i
  rw [rotate_pow_apply]
  simp

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

/-- Exact powers of the scalar/group-labelled shift. -/
theorem weightedShift_pow (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) (n : ℕ) :
    weightedShift σ u a ^ n = weightedShift (σ^n)
      (orbitWeight σ u n) (orbitWeight σ a n) := by
  induction n with
  | zero =>
    change 1 = labelledShift (Equiv.refl D) (fun _ => 1) * scalarDiagonal (fun _ => 1)
    rw [labelledShift_one, scalarDiagonal_one, mul_one]
  | succ n ih => rw [pow_succ', ih, weightedShift_mul, pow_succ']; rfl

/-- After one complete circuit the operator is diagonal, with the original circuit weights. -/
theorem weightedShift_cycle_pow (d : ℕ) [NeZero d] (u : Fin d → ℂ) (a : Fin d → A) :
    weightedShift (finRotate d) u a ^ d = weightedShift (Equiv.refl (Fin d))
      (orbitWeight (finRotate d) u d) (orbitWeight (finRotate d) a d) := by
  rw [weightedShift_pow, rotate_pow_self]
  rfl

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

/-- All full and partial circuit products remain in any submonoid containing the labels. -/
theorem orbitWeight_mem (H : Submonoid B) (σ : Equiv.Perm D) (b : D → B)
    (hb : ∀ i, b i ∈ H) (n : ℕ) (i : D) : orbitWeight σ b n i ∈ H := by
  induction n with
  | zero => exact H.one_mem
  | succ n ih => exact H.mul_mem (hb _) ih

/-- Starting a full circuit after a partial traversal conjugates its weight. -/
theorem orbitWeight_start (σ : Equiv.Perm D) (b : D → B) (d j : ℕ)
    (hd : σ^d = 1) (i : D) :
    orbitWeight σ b d ((σ^j) i) * orbitWeight σ b j i =
      orbitWeight σ b j i * orbitWeight σ b d i := by
  rw [← orbitWeight_add, Nat.add_comm d j, orbitWeight_add, hd]
  rfl

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

/-- The scalar circuit weight is independent of its starting point, literally. -/
theorem scalar_orbitWeight_constant (d : ℕ) [NeZero d] (u : Fin d → ℂ)
    (hu : ∀ i, u i ∈ unitary ℂ) (i : Fin d) :
    orbitWeight (finRotate d) u d i = orbitWeight (finRotate d) u d 0 := by
  have h := orbitWeight_start (finRotate d) u d i.val (rotate_pow_self d) 0
  rw [rotate_pow_apply] at h
  simp only [zero_add, Fin.cast_val_eq_self] at h
  have hne : orbitWeight (finRotate d) u i.val 0 ≠ 0 :=
    (Unitary.isUnit_coe (U := ⟨_, orbitWeight_mem (unitary ℂ) _ u hu _ _⟩)).ne_zero
  apply mul_right_cancel₀ hne
  simpa only [mul_comm (orbitWeight (finRotate d) u i.val 0)] using h

/-- The group circuit weight is conjugated in the exact operator order. -/
theorem group_orbitWeight_conjugate (d : ℕ) [NeZero d] (a : Fin d → A) (i : Fin d) :
    orbitWeight (finRotate d) a d i =
      orbitWeight (finRotate d) a i.val 0 * orbitWeight (finRotate d) a d 0 *
        (orbitWeight (finRotate d) a i.val 0)⁻¹ := by
  have h := orbitWeight_start (finRotate d) a d i.val (rotate_pow_self d) 0
  rw [rotate_pow_apply] at h
  simp only [zero_add, Fin.cast_val_eq_self] at h
  exact (eq_mul_inv_iff_mul_eq).mpr h

/-- The diagonal full-circuit power has identical scalar regular phases on every slot. -/
theorem groupPhase_orbitWeight_constant (d : ℕ) [NeZero d] (u : Fin d → ℂ)
    (a : Fin d → A) (hu : ∀ i, u i ∈ unitary ℂ) (i : Fin d) :
    groupPhase (orbitWeight (finRotate d) u d i)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate d) a d i) =
      groupPhase (orbitWeight (finRotate d) u d 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate d) a d 0) := by
  simp only [scalar_orbitWeight_constant d u hu i, group_orbitWeight_conjugate d a i]
  exact groupPhase_conjugate _ _ _ _

/-- The literal weighted boundary-cycle formula, including the phase cut at 1.
No cyclic-word hypothesis, approximation, or finite-group restriction is used. -/
theorem phase_weightedCycle (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    phase (weightedShift (finRotate (n+1)) u a) = (n : ℝ)/2 +
      groupPhase (orbitWeight (finRotate (n+1)) u (n+1) 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate (n+1)) a (n+1) 0) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
  let _ := isStarNormal_of_mem_unitary (pow_mem (weightedShift_unitary (finRotate (n+1)) u a hu) (n+1))
  have h := phase_weightedShift_grid n u a hu
  have hp := phase_weightedDiagonal (orbitWeight (finRotate (n+1)) u (n+1))
    (orbitWeight (finRotate (n+1)) a (n+1))
    (orbitWeight_mem (unitary ℂ) _ u hu (n+1))
  simp_rw [groupPhase_orbitWeight_constant (n+1) u a hu] at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hp
  have hpow : phase (weightedShift (finRotate (n+1)) u a ^ (n+1)) =
      (n+1 : ℝ) * groupPhase (orbitWeight (finRotate (n+1)) u (n+1) 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate (n+1)) a (n+1) 0) := by
    simpa only [weightedShift_cycle_pow] using hp
  dsimp only at h ⊢
  rw [hpow] at h
  have hn : (0 : ℝ) < n+1 := by positivity
  nlinarith
end KervaireMatrix

end

end OAI
