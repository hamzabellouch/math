import OAI.GroupTheory.Kervaire.PhaseGrids

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

namespace KervaireRegular

variable {α β γ : Type*}

/-- Permuting the coordinates of a square-summable family preserves membership,
without requiring a countable set of coordinates. -/
theorem mem_l2_reindex (e : α ≃ β) (f : ℓ²(α, ℂ)) :
    Memℓp (fun j => f (e.symm j)) 2 := by
  apply memℓp_gen
  exact (e.symm.summable_iff).2 ((lp.memℓp f).summable (by norm_num))

/-- Coordinate permutation before adding the isometric structure. -/
def reindexLinear (e : α ≃ β) : ℓ²(α, ℂ) ≃ₗ[ℂ] ℓ²(β, ℂ) where
  toFun f := ⟨fun j => f (e.symm j), mem_l2_reindex e f⟩
  invFun f := ⟨fun i => f (e i), mem_l2_reindex e.symm f⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem reindexLinear_apply (e : α ≃ β) (f : ℓ²(α, ℂ)) (j : β) :
    reindexLinear e f j = f (e.symm j) := rfl

/-- The unitary permutation representation on `ℓ²`, for arbitrary index types. -/
def reindex (e : α ≃ β) : ℓ²(α, ℂ) ≃ₗᵢ[ℂ] ℓ²(β, ℂ) :=
  (reindexLinear e).isometryOfInner (by
    intro f g
    simp only [lp.inner_eq_tsum, reindexLinear_apply]
    exact e.symm.tsum_eq (fun i => inner ℂ (f i) (g i)))

@[simp] theorem reindex_apply (e : α ≃ β) (f : ℓ²(α, ℂ)) (j : β) :
    reindex e f j = f (e.symm j) := rfl

@[simp] theorem reindex_symm (e : α ≃ β) : (reindex e).symm = reindex e.symm := by
  ext f j
  rfl

@[simp] theorem reindex_trans (e : α ≃ β) (d : β ≃ γ) :
    (reindex e).trans (reindex d) = reindex (e.trans d) := by
  ext f j
  rfl

/-- The standard delta vector used for the finite trace. -/
def delta (i : α) : ℓ²(α, ℂ) := by classical exact lp.single 2 i 1

@[simp] theorem reindex_delta (e : α ≃ β) (i : α) :
    reindex e (delta i) = delta (e i) := by
  classical
  ext j
  simp [reindex_apply, delta, Pi.single_apply, Equiv.symm_apply_eq]

@[simp] theorem inner_delta_left (i : α) (f : ℓ²(α, ℂ)) :
    inner ℂ (delta i) f = f i := by
  classical
  simpa [delta] using lp.inner_single_left (𝕜 := ℂ) i (1 : ℂ) f

@[simp] theorem inner_delta_right (i : α) (f : ℓ²(α, ℂ)) :
    inner ℂ f (delta i) = star (f i) := by
  classical
  simpa [delta] using lp.inner_single_right (𝕜 := ℂ) i (1 : ℂ) f

variable {A : Type*} [Group A]

/-- `L(a) δ_x = δ_(ax)` including infinite and uncountable groups. -/
def left (a : A) : ℓ²(A, ℂ) ≃ₗᵢ[ℂ] ℓ²(A, ℂ) := reindex (Equiv.mulLeft a)

def right (a : A) : ℓ²(A, ℂ) ≃ₗᵢ[ℂ] ℓ²(A, ℂ) := reindex (Equiv.mulRight a⁻¹)

@[simp] theorem left_apply (a : A) (f : ℓ²(A, ℂ)) (x : A) :
    left a f x = f (a⁻¹ * x) := rfl

@[simp] theorem right_apply (a : A) (f : ℓ²(A, ℂ)) (x : A) :
    right a f x = f (x * a) := by simp [right]

@[simp] theorem left_delta (a x : A) : left a (delta x) = delta (a * x) :=
  reindex_delta (Equiv.mulLeft a) x

@[simp] theorem right_delta (a x : A) : right a (delta x) = delta (x * a⁻¹) :=
  reindex_delta (Equiv.mulRight a⁻¹) x

@[simp] theorem left_mul (a b : A) (f : ℓ²(A, ℂ)) :
    left (a * b) f = left a (left b f) := by ext x; simp [mul_assoc]

@[simp] theorem right_mul (a b : A) (f : ℓ²(A, ℂ)) :
    right (a * b) f = right a (right b f) := by ext x; simp [mul_assoc]

/-- The commuting left and right regular actions. -/
theorem left_right (a b : A) (f : ℓ²(A, ℂ)) :
    left a (right b f) = right b (left a f) := by ext x; simp [mul_assoc]

abbrev Operator (A : Type*) := ℓ²(A, ℂ) →L[ℂ] ℓ²(A, ℂ)

instance operator_real_smulCommClass : SMulCommClass ℝ (Operator A) (Operator A) :=
  Algebra.to_smulCommClass (R := ℝ) (A := Operator A)

instance operator_real_isScalarTower : IsScalarTower ℝ (Operator A) (Operator A) :=
  IsScalarTower.right (R := ℝ) (A := Operator A)

/-- The commutant of the right regular representation. -/
def InCommutant (T : Operator A) : Prop :=
  ∀ a : A, Commute T (right a : Operator A)

@[simp] theorem right_star (a : A) :
    star (right a : Operator A) = (right a⁻¹ : Operator A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  simp [right, reindex_symm, reindex_apply]

@[simp] theorem right_one (f : ℓ²(A, ℂ)) : right (1 : A) f = f := by
  ext x
  simp

/-- Translation equivariance determines every matrix coefficient from one column. -/
theorem apply_delta_eq_right {T : Operator A} (hT : InCommutant T) (y : A) :
    T (delta y) = right y⁻¹ (T (delta 1)) := by
  have h := DFunLike.congr_fun (hT y⁻¹).eq (delta 1)
  simpa using h

theorem matrix_coefficient {T : Operator A} (hT : InCommutant T) (x y : A) :
    T (delta y) x = T (delta 1) (x * y⁻¹) := by
  rw [apply_delta_eq_right hT, right_apply]

/-- The (unnormalized for one copy) vector trace. -/
def trace : Operator A →L[ℂ] ℂ :=
  (innerSL ℂ (delta 1)).comp (ContinuousLinearMap.apply ℂ (ℓ²(A, ℂ)) (delta 1))

@[simp] theorem trace_apply (T : Operator A) :
    trace T = inner ℂ (delta 1) (T (delta 1)) := rfl

@[simp] theorem trace_eq_coefficient (T : Operator A) : trace T = T (delta 1) 1 := by
  simp

@[simp] theorem trace_one : trace (1 : Operator A) = 1 := by
  classical
  simp [delta]

/-- The reflected coefficient identity needed to evaluate a product trace. -/
theorem star_coefficient {T : Operator A} (hT : InCommutant T) (x : A) :
    star (star T (delta 1) x) = T (delta 1) x⁻¹ := by
  calc
    star (star T (delta 1) x) = inner ℂ (star T (delta 1)) (delta x) :=
      (inner_delta_right _ _).symm
    _ = inner ℂ (delta 1) (T (delta x)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = T (delta x) 1 := inner_delta_left _ _
    _ = T (delta 1) x⁻¹ := by simpa using matrix_coefficient hT 1 x

theorem trace_mul_eq_tsum {S T : Operator A} (hS : InCommutant S) :
    trace (S * T) = ∑' x : A, S (delta 1) x⁻¹ * T (delta 1) x := by
  rw [trace_apply]
  change inner ℂ (delta 1) (S (T (delta 1))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [RCLike.inner_apply, ← ContinuousLinearMap.star_eq_adjoint, mul_comm]
  exact congrArg (fun z : ℂ => z * T (delta 1) x) (star_coefficient hS x)

/-- Cyclicity uses a bijection of the entire index set; countability is unnecessary. -/
theorem trace_mul_comm {S T : Operator A} (hS : InCommutant S) (hT : InCommutant T) :
    trace (S * T) = trace (T * S) := by
  rw [trace_mul_eq_tsum hS, trace_mul_eq_tsum hT]
  calc
    (∑' x : A, S (delta 1) x⁻¹ * T (delta 1) x) =
        ∑' x : A, S (delta 1) x * T (delta 1) x⁻¹ := by
      simpa using (Equiv.inv A).tsum_eq
        (fun x : A => S (delta 1) x * T (delta 1) x⁻¹)
    _ = _ := tsum_congr fun _ => mul_comm _ _

/-- The vector at the identity is separating for the right regular commutant. -/
theorem eq_zero_of_delta_one {T : Operator A} (hT : InCommutant T)
    (h : T (delta 1) = 0) : T = 0 := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    zero_apply]
  have hi : T (delta i) = 0 := by
    rw [apply_delta_eq_right hT, h, map_zero]
  have hc : lp.single 2 i c = c • delta i := by
    simp [delta, ← lp.single_smul]
  rw [hc, map_smul, hi, smul_zero]

/-- Faithfulness in positive-square form, the part needed for positive operators. -/
theorem trace_star_mul_self_eq_zero_iff {T : Operator A} (hT : InCommutant T) :
    trace (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply eq_zero_of_delta_one hT
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [trace_apply] at h
    change inner ℂ (delta 1) (star T (T (delta 1))) = 0 at h
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at h
  · rintro rfl
    simp

local instance : ContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Operator A)

/-- The commutant is closed under the nonnegative continuous square root. -/
theorem InCommutant.sqrt {T : Operator A} (hT : InCommutant T) :
    InCommutant (CFC.sqrt T) := by
  intro a
  exact (hT a).cfcₙ_nnreal NNReal.sqrt

/-- Positivity of the vector functional. -/
theorem trace_nonneg {T : Operator A} (hT : 0 ≤ T) : 0 ≤ (trace T).re :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right _

/-- Faithfulness for every nonnegative operator in the commutant. -/
theorem trace_eq_zero_iff_of_nonneg {T : Operator A} (hT : InCommutant T)
    (hpos : 0 ≤ T) : trace T = 0 ↔ T = 0 := by
  have hs : star (CFC.sqrt T) = CFC.sqrt T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  constructor
  · intro ht
    have hz : trace (star (CFC.sqrt T) * CFC.sqrt T) = 0 := by
      rwa [hs, CFC.sqrt_mul_sqrt_self T hpos]
    have hz' := (trace_star_mul_self_eq_zero_iff hT.sqrt).mp hz
    exact (CFC.sqrt_eq_zero_iff T hpos).mp hz'
  · rintro rfl
    simp

end KervaireRegular

end

end OAI
