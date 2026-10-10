import OAI.GroupTheory.Kervaire.MatrixTrace

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

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

/-- Projection to a scalar coordinate, on the actual product-index regular Hilbert space. -/
def coordinateProjection (i : D) : Operator D A := by
  classical
  let L : Space D A →ₗ[ℂ] Space D A := {
    toFun := fun f => ⟨fun p => if p.1 = i then f p else 0,
      (lp.memℓp f).mono' (by intro p; split_ifs <;> simp)⟩
    map_add' := by
      intro f g
      ext p
      change (if p.1 = i then f p + g p else 0) =
        (if p.1 = i then f p else 0) + (if p.1 = i then g p else 0)
      split_ifs <;> simp
    map_smul' := by intro c f; ext p; by_cases h : p.1 = i <;> simp [h] }
  exact L.mkContinuous 1 (fun f => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (fun p => by
      change ‖ite (p.1 = i) (f p) 0‖ ≤ _
      split_ifs <;> simp))

@[simp] theorem coordinateProjection_apply (i d : D) (f : Space D A) (a : A) :
    coordinateProjection i f (d,a) = if d = i then f (d,a) else 0 := by
  classical
  rfl

/-- The scalar matrix unit, continuously acting on all (possibly uncountable) group coordinates. -/
def matrixUnit (i j : D) : Operator D A := by
  classical
  exact (coordinateProjection i).comp
    (reindex (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl A))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem matrixUnit_apply (i j d : D) (f : Space D A) (a : A) :
    matrixUnit i j f (d,a) = if d = i then f (j,a) else 0 := by
  classical
  simp only [matrixUnit, ContinuousLinearMap.comp_apply, coordinateProjection_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    reindex_apply, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  split_ifs with h
  · subst d; simp
  · rfl

/-- Equality of operators on the standard orthonormal basis. -/
theorem ext_delta {T U : Operator D A}
    (h : ∀ p : D × A, T (delta p) = U (delta p)) : T = U := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro p
  apply ContinuousLinearMap.ext
  intro c
  have hc : lp.single (E := fun _ : D × A => ℂ) 2 p c = c • delta p := by
    ext q
    simp [delta, Pi.single_apply]
  change T (lp.single 2 p c) = U (lp.single 2 p c)
  rw [hc, map_smul, map_smul, h]

/-- Matrix coefficients suffice to establish an adjoint identity. -/
theorem star_eq_of_coefficients {T U : Operator D A}
    (h : ∀ p q : D × A, star (T (delta p) q) = U (delta q) p) : star T = U := by
  apply ext_delta
  intro q
  ext p
  calc
    (star T) (delta q) p = inner ℂ (delta p) ((star T) (delta q)) :=
      (inner_delta_left _ _).symm
    _ = inner ℂ (T (delta p)) (delta q) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = star (T (delta p) q) := inner_delta_right _ _
    _ = U (delta q) p := h p q

@[simp] theorem matrixUnit_star (i j : D) : star (matrixUnit (A := A) i j) = matrixUnit j i := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨d,a⟩ ⟨e,b⟩
  simp only [matrixUnit_apply]
  by_cases he : e = i <;> by_cases hd : d = j
  · subst e; subst d
    simp [delta, Pi.single_apply, eq_comm]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm hd]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm he]
  · simp [he,hd]

variable [Fintype D]

/-- Scalar matrices embedded without any finite/countable assumption on the group. -/
def scalarTensor (M : Matrix D D ℂ) : Operator D A :=
  ∑ i, ∑ j, M i j • matrixUnit i j

@[simp] theorem scalarTensor_apply (M : Matrix D D ℂ) (f : Space D A) (d : D) (a : A) :
    scalarTensor M f (d,a) = ∑ j, M d j * f (j,a) := by
  classical
  change (∑ i, ∑ j, M i j • matrixUnit (A := A) i j) f (d,a) = _
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [Finset.sum_ite_irrel]

@[simp] theorem scalarTensor_one : scalarTensor (1 : Matrix D D ℂ) = (1 : Operator D A) := by
  classical
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

@[simp] theorem scalarTensor_mul (M N : Matrix D D ℂ) :
    scalarTensor (A := A) (M*N) = scalarTensor M * scalarTensor N := by
  ext f ⟨d,a⟩
  simp only [scalarTensor_apply, mul_apply_eq_comp, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _

@[simp] theorem scalarTensor_star (M : Matrix D D ℂ) :
    star (scalarTensor (A := A) M) = scalarTensor (star M) := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨sourceIndex,sourceElement⟩ ⟨targetIndex,targetElement⟩
  by_cases heq : sourceElement = targetElement
  · subst targetElement
    simp [delta, Pi.single_apply, Prod.mk.injEq]
  · simp [delta, Prod.mk.injEq, heq, Ne.symm heq]

variable [Group A]

/-- Scalar matrices lie in exactly the commutant required by the phase theorem. -/
theorem scalarTensor_mem_commutant (M : Matrix D D ℂ) :
    InCommutant (scalarTensor (A := A) M) := by
  intro a
  change scalarTensor M * (right (D := D) a).toContinuousLinearEquiv.toContinuousLinearMap = _
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp]

/-- The scalar trace on tensoring with the regular identity is unnormalized matrix trace. -/
@[simp] theorem trace_scalarTensor (M : Matrix D D ℂ) :
    trace (scalarTensor (A := A) M) = Matrix.trace M := by
  classical
  simp only [trace_apply, inner_delta_left, scalarTensor_apply, Matrix.trace]
  simp [delta, Pi.single_apply, Prod.mk.injEq]

omit [Group A] in
/-- Unitary scalar matrices remain unitary in the full regular operator algebra. -/
theorem scalarTensor_mem_unitary {M : Matrix D D ℂ} (hM : M ∈ Matrix.unitaryGroup D ℂ) :
    scalarTensor (A := A) M ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff] at hM ⊢
  constructor
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.1, scalarTensor_one]
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.2, scalarTensor_one]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

/-- The coordinate permutation underlying a group-labelled shift.  Labels act
on the left so that the operator commutes with every right translation. -/
def labelledPermutation (σ : Equiv.Perm D) (a : D → A) : Equiv.Perm (D × A) where
  toFun p := (σ p.1, a p.1 * p.2)
  invFun p := (σ.symm p.1, (a (σ.symm p.1))⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- A corner-labelled permutation on the actual arbitrary-group Hilbert space. -/
def labelledShift (σ : Equiv.Perm D) (a : D → A) : Operator D A :=
  (reindex (labelledPermutation σ a)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem labelledShift_apply (σ : Equiv.Perm D) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    labelledShift σ a f (d,x) = f (σ.symm d, (a (σ.symm d))⁻¹ * x) := rfl

@[simp] theorem labelledShift_delta (σ : Equiv.Perm D) (a : D → A) (d : D) (x : A) :
    labelledShift σ a (delta (d,x)) = delta (σ d,a d*x) :=
  reindex_delta _ _

/-- This representation is unitary without dimensional or cardinality assumptions. -/
theorem labelledShift_unitary (σ : Equiv.Perm D) (a : D → A) :
    labelledShift σ a ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff]
  have hs : star (labelledShift σ a) =
      (reindex (labelledPermutation σ a)).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact LinearIsometryEquiv.adjoint_eq_symm _
  rw [hs]
  constructor <;> ext f p <;> simp [labelledShift, mul_apply_eq_comp]

/-- The commutant contains every group-labelled shift. -/
theorem labelledShift_mem_commutant (σ : Equiv.Perm D) (a : D → A) :
    InCommutant (labelledShift σ a) := by
  intro x
  change labelledShift σ a * (right (D := D) x : Operator D A) = _
  ext f ⟨d,y⟩
  simp [mul_apply_eq_comp, mul_assoc]

@[simp] theorem labelledShift_one :
    labelledShift (Equiv.refl D) (fun _ => (1 : A)) = 1 := by
  ext f ⟨d,x⟩
  simp

theorem labelledShift_mul (σ τ : Equiv.Perm D) (a b : D → A) :
    labelledShift σ a * labelledShift τ b =
      labelledShift (σ*τ) (fun d => a (τ d)*b d) := by
  apply ext_delta
  rintro ⟨d,x⟩
  simp [mul_apply_eq_comp, mul_assoc]

variable [Fintype D]

/-- A scalar diagonal on the finite coordinate set. -/
def scalarDiagonal (u : D → ℂ) : Operator D A :=
  scalarTensor (Matrix.diagonal u)

omit [Group A] in
@[simp] theorem scalarDiagonal_apply (u : D → ℂ) (f : Space D A) (d : D) (x : A) :
    scalarDiagonal u f (d,x) = u d * f (d,x) := by
  classical
  simp [scalarDiagonal, Matrix.diagonal]

omit [Group A] in
@[simp] theorem scalarDiagonal_delta (u : D → ℂ) (d : D) (x : A) :
    scalarDiagonal u (delta (d,x)) = u d • delta (d,x) := by
  classical
  ext ⟨e,y⟩
  by_cases h : (e,y) = (d,x)
  · cases h
    simp [delta]
  · simp [delta, Ne.symm h]

omit [Group A] in
@[simp] theorem scalarDiagonal_one : scalarDiagonal (A := A) (fun _ : D => 1) = 1 := by
  ext f ⟨d,x⟩
  simp

omit [Group A] in
@[simp] theorem scalarDiagonal_mul (u v : D → ℂ) :
    scalarDiagonal (A := A) u * scalarDiagonal v = scalarDiagonal (u*v) := by
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp, mul_assoc]

omit [Group A] in
@[simp] theorem scalarDiagonal_star (u : D → ℂ) :
    star (scalarDiagonal (A := A) u) = scalarDiagonal (star u) := by
  dsimp [scalarDiagonal]
  rw [scalarTensor_star]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.star_apply, Matrix.diagonal, h, Ne.symm h]

omit [Group A] in
theorem scalarDiagonal_unitary (u : D → ℂ) (hu : ∀ d, u d ∈ unitary ℂ) :
    scalarDiagonal (A := A) u ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff, scalarDiagonal_star, scalarDiagonal_mul, scalarDiagonal_mul]
  have h1 : star u * u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).1
  have h2 : u * star u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).2
  rw [h1,h2]
  exact ⟨scalarDiagonal_one,scalarDiagonal_one⟩

/-- This includes both shifts: `S` has coefficient labels,
while `Theta` has only scalar phase labels. -/
def weightedShift (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) : Operator D A :=
  labelledShift σ a * scalarDiagonal u

@[simp] theorem weightedShift_apply (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    weightedShift σ u a f (d,x) =
      u (σ.symm d) * f (σ.symm d, (a (σ.symm d))⁻¹*x) := by
  simp [weightedShift, mul_apply_eq_comp]

@[simp] theorem weightedShift_delta (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (d : D) (x : A) :
    weightedShift σ u a (delta (d,x)) = u d • delta (σ d,a d*x) := by
  simp [weightedShift,mul_apply_eq_comp]

theorem weightedShift_unitary (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (hu : ∀ d, u d ∈ unitary ℂ) : weightedShift σ u a ∈ unitary (Operator D A) :=
  mul_mem (labelledShift_unitary σ a) (scalarDiagonal_unitary u hu)

theorem weightedShift_mem_commutant (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) :
    InCommutant (weightedShift σ u a) := by
  intro x
  exact (labelledShift_mem_commutant σ a x).mul_left
    (scalarTensor_mem_commutant (Matrix.diagonal u) x)

/-- Multiplication proves the exact order of coefficient inverses on every boundary step. -/
theorem weightedShift_mul (σ τ : Equiv.Perm D) (u v : D → ℂ) (a b : D → A) :
    weightedShift σ u a * weightedShift τ v b =
      weightedShift (σ*τ) (fun d => u (τ d)*v d) (fun d => a (τ d)*b d) := by
  apply ext_delta
  rintro ⟨d,x⟩
  simp [mul_apply_eq_comp, smul_smul, mul_assoc, mul_comm (v d)]

end KervaireMatrix
namespace KervaireSpectral
@[simp] theorem scalarRotation_nat (j : ℕ) : scalarRotation j = 1 := by
  unfold scalarRotation
  rw [show ((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * Complex.I =
    (j : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I j

theorem scalarRotation_grid_pow (j d : ℕ) (hd : 0 < d) :
    scalarRotation ((j : ℝ)/d)^d = 1 := by
  rw [← scalarRotation_nat_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_cancel₀ _ hd', scalarRotation_nat]
end KervaireSpectral

end

end OAI
