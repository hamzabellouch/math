import OAI.Algebra.Finitistic.Ordinary.OrdinaryFreeTensorExactness

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.FreeLeft
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I M : Type u) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]

/-- A coefficient of a free left module acts on the right tensor factor. -/
def coefficientAction : A →ₗ[k] M →ₗ[k] M :=
  (Algebra.lsmul k k M).toLinearMap.comp (MulOpposite.opLinearEquiv k).toLinearMap

def evaluateBilinear : M →ₗ[k] (I →₀ A) →ₗ[k] (I →₀ M) :=
  (Finsupp.lsum k (fun i =>
    (coefficientAction (k := k) (A := A) M).compr₂ (Finsupp.lsingle i))).flip

@[simp] theorem evaluateBilinear_single (i : I) (a : A) (m : M) :
    evaluateBilinear (k := k) I M m (Finsupp.single i a) =
      Finsupp.single i (MulOpposite.op a • m) := by
  simp only [evaluateBilinear,LinearMap.flip_apply,Finsupp.lsum_single]
  rfl

def evaluation : Tensor k A M (I →₀ A) →ₗ[k] (I →₀ M) :=
  lift (evaluateBilinear (k := k) I M) (by
    intro a m n
    induction n using Finsupp.induction_linear with
    | zero => simp only [smul_zero,map_zero]
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
    | single i x =>
      rw [Finsupp.smul_single,evaluateBilinear_single,evaluateBilinear_single]
      change Finsupp.single i (MulOpposite.op x • (MulOpposite.op a • m)) =
        Finsupp.single i (MulOpposite.op (a*x) • m)
      rw [← mul_smul,MulOpposite.op_mul])

@[simp] theorem evaluation_single (i : I) (a : A) (m : M) :
    evaluation (k := k) I M (mk k A M (I →₀ A) m (Finsupp.single i a)) =
      Finsupp.single i (MulOpposite.op a • m) := evaluateBilinear_single I M i a m

def insertion : (I →₀ M) →ₗ[k] Tensor k A M (I →₀ A) :=
  Finsupp.lsum k (fun i => (mk k A M (I →₀ A)).flip (Finsupp.single i 1))

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem insertion_single (i : I) (m : M) :
    insertion (k := k) (A := A) I M (Finsupp.single i m) =
      mk k A M (I →₀ A) m (Finsupp.single i 1) := by
  simp only [insertion,Finsupp.lsum_single,LinearMap.flip_apply]

theorem evaluation_insertion (z : I →₀ M) :
    evaluation (k := k) (A := A) I M (insertion I M z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i m => rw [insertion_single,evaluation_single,MulOpposite.op_one,one_smul]

theorem insertion_evaluation (z : Tensor k A M (I →₀ A)) :
    insertion I M (evaluation (k := k) I M z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction n using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | single i a =>
      rw [evaluation_single,insertion_single,balance]
      congr 1
      rw [Finsupp.smul_single,smul_eq_mul,mul_one]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Tensor with an arbitrary free left module is the direct sum of the right module. -/
def equivalence : Tensor k A M (I →₀ A) ≃ₗ[k] (I →₀ M) where
  __ := evaluation (k := k) I M
  invFun := insertion I M
  left_inv := insertion_evaluation I M
  right_inv := evaluation_insertion I M

variable {M} {M' M'' : Type u}
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']

theorem evaluation_naturality (f : M →ₗ[Aᵐᵒᵖ] M') (z : Tensor k A M (I →₀ A)) :
    evaluation (k := k) I M' (mapLeft (I →₀ A) f z) =
      Finsupp.mapRange.linearMap (f.restrictScalars k) (evaluation (k := k) I M z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction n using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | single i a =>
      simp only [mapLeft_mk,evaluation_single]
      ext j
      change (Finsupp.single i (MulOpposite.op a • f m)) j =
        (Finsupp.mapRange f f.map_zero (Finsupp.single i (MulOpposite.op a • m))) j
      rw [Finsupp.mapRange_single, f.map_smul]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Free left tensor preserves exact sequences of right modules. -/
theorem tensor_exact (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'')
    (h : Function.Exact f g) :
    Function.Exact (mapLeft (k := k) (I →₀ A) f) (mapLeft (k := k) (I →₀ A) g) := by
  intro z
  constructor
  · intro hz
    have hz' : Finsupp.mapRange.linearMap (g.restrictScalars k) (evaluation (k := k) I M' z) = 0 := by
      rw [← evaluation_naturality,hz,map_zero]
    obtain ⟨y,hy⟩ := (Free.finsupp_exact (k := k) I f g h _).mp hz'
    refine ⟨(equivalence (k := k) (A := A) I M).symm y, ?_⟩
    apply (equivalence (k := k) (A := A) I M').injective
    change evaluation (k := k) I M' (mapLeft (I →₀ A) f
      ((equivalence (k := k) (A := A) I M).symm y)) = _
    rw [evaluation_naturality]
    change Finsupp.mapRange.linearMap (f.restrictScalars k)
      ((equivalence (k := k) (A := A) I M) ((equivalence (k := k) (A := A) I M).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      rw [mapLeft_mk,mapLeft_mk,(h (f m)).mpr ⟨m,rfl⟩,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
end LittleFinitistic.BalancedTensor.FreeLeft

end

end OAI
