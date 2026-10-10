import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

noncomputable section

namespace Pureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positive_square_factor (a : A) (ha : 0 ≤ a) : ∃ x : A, star x * x = a := by
  refine ⟨CFC.sqrt a, ?_⟩
  rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]

noncomputable def matrixTraceLinear (τ : TracialState A) : CStarMatrix ι ι A →ₗ[ℂ] ℂ where
  toFun M := ∑ i, τ.functional (M i i)
  map_add' M N := by simp [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' z M := by simp [CStarMatrix.smul_apply, Finset.mul_sum]

lemma matrix_entry_nonneg (M : CStarMatrix ι ι A) (hM : 0 ≤ M) (i : ι) : 0 ≤ M i i := by
  obtain ⟨x, hs⟩ := positive_square_factor M hM
  rw [← hs, CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun j _ => by
    rw [CStarMatrix.star_apply]
    exact star_mul_self_nonneg _

noncomputable def matrixTrace (τ : TracialState A) : CStarMatrix ι ι A →ₚ[ℂ] ℂ :=
  { matrixTraceLinear τ with
    monotone' := by
      intro M N hMN
      apply sub_nonneg.mp
      change 0 ≤ matrixTraceLinear τ N - matrixTraceLinear τ M
      rw [← map_sub]
      exact Finset.sum_nonneg fun i _ => τ.functional.map_nonneg
        (matrix_entry_nonneg (N - M) (sub_nonneg.mpr hMN) i) }

@[simp] lemma matrixTrace_apply (τ : TracialState A) (M : CStarMatrix ι ι A) :
    matrixTrace τ M = ∑ i, τ.functional (M i i) := rfl

lemma matrixTrace_tracial (τ : TracialState A) (M N : CStarMatrix ι ι A) :
    matrixTrace τ (M * N) = matrixTrace τ (N * M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  exact τ.tracial _ _

end Pureness

namespace Pureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma starAlgHom_positive (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
    rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
  rw [← hs, map_mul, map_star]
  exact star_mul_self_nonneg _

end Pureness

namespace Pureness
open scoped ComplexOrder ENNReal NNReal
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def diagonalMatrixHom : (ι → A) →⋆ₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { Matrix.diagonalAlgHom ℂ with
      map_star' := by
        intro a
        exact (Matrix.diagonal_conjTranspose a).symm }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diagonalMatrixHom_apply (a : ι → A) (i j : ι) :
    diagonalMatrixHom a i j = if i = j then a i else 0 := rfl

end Pureness

section
open scoped ENNReal NNReal
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev Positive := {a : A // 0 ≤ a}

end TraceCone
end

section
open scoped ENNReal NNReal
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace Positive
variable {A}

def zero : Positive A := ⟨0, le_rfl⟩

def add (a b : Positive A) : Positive A := ⟨a.1 + b.1, add_nonneg a.2 b.2⟩

def smul (r : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨(r : ℝ) • a.1, smul_nonneg r.2 a.2⟩

def starMul (x : A) : Positive A := ⟨star x * x, star_mul_self_nonneg x⟩

def mulStar (x : A) : Positive A := ⟨x * star x, mul_star_self_nonneg x⟩

def power (r : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨CFC.nnrpow a.1 r, CFC.nnrpow_nonneg⟩

def rootExponent (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)

end Positive
end TraceCone
end

section
open scoped ENNReal NNReal
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure ExtendedTrace where
  toFun : Positive A → ℝ≥0∞
  map_zero : toFun (Positive.zero) = 0
  map_add (a b : Positive A) : toFun (Positive.add a b) = toFun a + toFun b
  map_smul (r : ℝ≥0) (a : Positive A) :
    toFun (Positive.smul r a) = (r : ℝ≥0∞) * toFun a
  tracial (x : A) : toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  lowerSemicontinuous : LowerSemicontinuous toFun

end TraceCone
end

section
open scoped ENNReal NNReal
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace ExtendedTrace
variable {A}

instance : CoeFun (ExtendedTrace A) (fun _ => Positive A → ℝ≥0∞) := ⟨toFun⟩

def rank (τ : ExtendedTrace A) (a : Positive A) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => τ (Positive.power (Positive.rootExponent n) a)) Filter.atTop

@[ext] theorem ext {τ σ : ExtendedTrace A} (h : ∀ a, τ a = σ a) : τ = σ := by
  cases τ
  cases σ
  congr
  exact funext h

instance : Zero (ExtendedTrace A) := ⟨{
  toFun := fun _ => 0
  map_zero := rfl
  map_add := fun _ _ => (zero_add 0).symm
  map_smul := fun _ _ => (mul_zero _).symm
  tracial := fun _ => rfl
  lowerSemicontinuous := lowerSemicontinuous_const }⟩

instance : Add (ExtendedTrace A) := ⟨fun τ σ => {
  toFun := fun a => τ a + σ a
  map_zero := by rw [τ.map_zero, σ.map_zero, add_zero]
  map_add := by
    intro a b
    rw [τ.map_add, σ.map_add]
    ac_rfl
  map_smul := by
    intro r a
    rw [τ.map_smul, σ.map_smul, mul_add]
  tracial := by
    intro x
    rw [τ.tracial, σ.tracial]
  lowerSemicontinuous := τ.lowerSemicontinuous.add σ.lowerSemicontinuous }⟩

@[simp] theorem add_apply (τ σ : ExtendedTrace A) (a : Positive A) :
    (τ + σ) a = τ a + σ a := rfl

instance : AddCommMonoid (ExtendedTrace A) where
  add_assoc a b c := ext fun x => add_assoc (a x) (b x) (c x)
  zero_add a := ext fun x => zero_add (a x)
  add_zero a := ext fun x => add_zero (a x)
  add_comm a b := ext fun x => add_comm (a x) (b x)
  nsmul := nsmulRec

theorem monotone (τ : ExtendedTrace A) : Monotone (fun a : Positive A => τ a) := by
  intro a b hab
  change τ a ≤ τ b
  let c : Positive A := ⟨b.1 - a.1, sub_nonneg.mpr hab⟩
  have heq : Positive.add a c = b := Subtype.ext (add_sub_cancel _ _)
  have h := τ.map_add a c
  rw [heq] at h
  rw [h]
  exact le_self_add

end ExtendedTrace
end TraceCone
end

section
open scoped Topology NNReal
open Filter
namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CuntzBelow (a b : Positive A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : A, ‖star v * b.1 * v - a.1‖ < ε

end TraceCone
end

namespace Pureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l m : ℕ}

noncomputable def corner (_ : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) :
    CStarMatrix (Fin l) (Fin l) A :=
  fun i j =>
    if hi : i.val < k then if hj : j.val < k then a ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma corner_apply_cast (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin k) : corner h a (Fin.castLE h i) (Fin.castLE h j) = a i j := by
  simp [corner, i.isLt, j.isLt]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_row_zero (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin l) (hi : ¬ i.val < k) : corner h a i j = 0 := by simp [corner, hi]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_col_zero (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (i j : Fin l) (hj : ¬ j.val < k) : corner h a i j = 0 := by simp [corner, hj]

lemma sum_corner_support {G : Type*} [AddCommMonoid G] (h : k ≤ l) (f : Fin l → G)
    (hf : ∀ i, ¬ i.val < k → f i = 0) :
    ∑ i, f i = ∑ i : Fin k, f (Fin.castLE h i) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (fun i j hij => Fin.ext (congrArg (fun t : Fin l => t.val) hij))
  · intro i hi
    apply hf i
    intro hik
    exact hi ⟨⟨i.val, hik⟩, Fin.ext rfl⟩
  · intro i; rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_mul (h : k ≤ l) (a b : CStarMatrix (Fin k) (Fin k) A) :
    corner h (a * b) = corner h a * corner h b := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · rw [CStarMatrix.mul_apply, sum_corner_support h _ (fun t ht => by
        rw [corner_col_zero h a i t ht, zero_mul])]
      simp [corner, hi, hj, CStarMatrix.mul_apply]
    · simp [corner_col_zero h _ _ _ hj, CStarMatrix.mul_apply]
  · simp [corner_row_zero h _ _ _ hi, CStarMatrix.mul_apply]

noncomputable def cornerHom (h : k ≤ l) :
    CStarMatrix (Fin k) (Fin k) A →⋆ₙₐ[ℂ] CStarMatrix (Fin l) (Fin l) A where
  toFun := corner h
  map_zero' := by ext i j; simp [corner]
  map_add' a b := by
    ext i j
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [corner, hi, hj]
  map_mul' := corner_mul h
  map_smul' z a := by
    ext i j
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [corner, hi, hj]
  map_star' a := by
    ext i j
    simp only [CStarMatrix.star_apply, corner]
    by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp [hi, hj]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_injective (h : k ≤ l) : Function.Injective (cornerHom (A := A) h) := by
  intro a b hab
  ext i j
  exact (corner_apply_cast h a i j).symm.trans
    ((congrArg (fun M : CStarMatrix (Fin l) (Fin l) A => M (Fin.castLE h i) (Fin.castLE h j)) hab).trans
      (corner_apply_cast h b i j))

@[simp] lemma corner_norm (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A) :
    ‖corner h a‖ = ‖a‖ := NonUnitalStarAlgHom.norm_map (cornerHom h) (corner_injective h) a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma corner_refl (a : CStarMatrix (Fin k) (Fin k) A) : corner le_rfl a = a := by
  ext i j
  simp [corner, i.isLt, j.isLt]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_comp (h : k ≤ l) (g : l ≤ m) (a : CStarMatrix (Fin k) (Fin k) A) :
    corner g (corner h a) = corner (h.trans g) a := by
  ext i j
  by_cases hi : i.val < k <;> by_cases hj : j.val < k
  · simp [corner, hi, hj, hi.trans_le h, hj.trans_le h]
  · simp [corner, hi, hj, hi.trans_le h]
  · simp [corner, hi]
  · simp [corner, hi]

lemma matrixTrace_corner (τ : TracialState A) (h : k ≤ l)
    (a : CStarMatrix (Fin k) (Fin k) A) : matrixTrace τ (corner h a) = matrixTrace τ a := by
  rw [matrixTrace_apply, sum_corner_support h _ (fun i hi => by
    rw [corner_row_zero h a i i hi, map_zero])]
  simp only [corner_apply_cast, matrixTrace_apply]

end Pureness

namespace Pureness
open Filter Topology
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

def compress (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) :
    CStarMatrix (Fin k) (Fin k) A := fun i j => a (Fin.castLE h i) (Fin.castLE h j)

end Pureness

namespace Pureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

noncomputable def cornerProjection (_ : k ≤ l) : CStarMatrix (Fin l) (Fin l) A :=
  diagonalMatrixHom fun i => if i.val < k then 1 else 0

omit [PartialOrder A] [StarOrderedRing A] in
lemma cornerProjection_eq (h : k ≤ l) :
    cornerProjection (A := A) h = corner h (1 : CStarMatrix (Fin k) (Fin k) A) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k <;> simp [cornerProjection, diagonalMatrixHom_apply, corner, hi]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [cornerProjection, diagonalMatrixHom_apply, corner,
      hij, Fin.ext_iff, hv]

omit [PartialOrder A] [StarOrderedRing A] in
lemma cornerProjection_mul (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) (i j : Fin l) :
    (cornerProjection (A := A) h * a) i j = if i.val < k then a i j else 0 := by
  simp [CStarMatrix.mul_apply, cornerProjection, diagonalMatrixHom_apply, ite_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_cornerProjection (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) (i j : Fin l) :
    (a * cornerProjection (A := A) h) i j = if j.val < k then a i j else 0 := by
  simp [CStarMatrix.mul_apply, cornerProjection, diagonalMatrixHom_apply, mul_ite]

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_compress (h : k ≤ l) (a : CStarMatrix (Fin l) (Fin l) A) :
    corner h (compress h a) = cornerProjection h * a * cornerProjection h := by
  ext i j
  rw [mul_cornerProjection, cornerProjection_mul]
  by_cases hi : i.val < k <;> by_cases hj : j.val < k <;>
    simp [corner, compress, hi, hj]

end Pureness

namespace Pureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def TracialState.comap (ρ : TracialState B) (φ : A →⋆ₐ[ℂ] B) : TracialState A where
  functional :=
    { ρ.functional.toLinearMap.comp φ.toLinearMap with
      monotone' := by
        intro a b hab
        change ρ.functional (φ a) ≤ ρ.functional (φ b)
        apply ρ.functional.monotone
        apply sub_nonneg.mp
        rw [← map_sub]
        exact starAlgHom_positive φ (b - a) (sub_nonneg.mpr hab) }
  normalized := by change ρ.functional (φ 1) = 1; rw [map_one, ρ.normalized]
  tracial a b := by
    change ρ.functional (φ (a * b)) = ρ.functional (φ (b * a))
    rw [map_mul φ, map_mul φ, ρ.tracial]

end Pureness

namespace Pureness
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev MatrixStage (k : ℕ) := CStarMatrix (Fin k) (Fin k) A

noncomputable def matrixConnecting (k l : ℕ) (h : k ≤ l) :
    MatrixStage A k →⋆ₙₐ[ℂ] MatrixStage A l := cornerHom h

instance matrixDirectedSystem : DirectedSystem (MatrixStage A) (fun _ _ h => matrixConnecting A _ _ h) where
  map_self := by intro i x; exact corner_refl x
  map_map := by intro k j i h g a; exact corner_comp h g a

abbrev FiniteMatrixLimit := DirectLimit (MatrixStage A) (matrixConnecting A)

noncomputable def finiteMatrixInclude (k : ℕ) : MatrixStage A k →⋆ₙₐ[ℂ] FiniteMatrixLimit A where
  toFun a := Quotient.mk _ ⟨k, a⟩
  map_zero' := (DirectLimit.zero_def k).symm
  map_add' a b := (DirectLimit.add_def k a b).symm
  map_mul' a b := (DirectLimit.mul_def k a b).symm
  map_smul' z a := (DirectLimit.smul_def k a z).symm
  map_star' a := (DirectLimit.star_def k a).symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteMatrixInclude_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    finiteMatrixInclude A l (corner h a) = finiteMatrixInclude A k a :=
  (DirectLimit.eq_of_le ⟨k, a⟩ l h).symm

noncomputable def finiteMatrixNorm : FiniteMatrixLimit A → ℝ :=
  DirectLimit.lift (matrixConnecting A) (fun _ a => ‖a‖)
    (fun _ _ h a => (corner_norm h a).symm)

@[simp] lemma finiteMatrixNorm_include (k : ℕ) (a : MatrixStage A k) :
    finiteMatrixNorm A (finiteMatrixInclude A k a) = ‖a‖ := rfl

noncomputable def finiteMatrixGroupNorm : AddGroupNorm (FiniteMatrixLimit A) where
  toFun := finiteMatrixNorm A
  map_zero' := by rw [← map_zero (finiteMatrixInclude A 0), finiteMatrixNorm_include, norm_zero]
  add_le' := by
    apply DirectLimit.induction₂
    intro k a b
    change finiteMatrixNorm A (finiteMatrixInclude A k a + finiteMatrixInclude A k b) ≤ _
    rw [← map_add, finiteMatrixNorm_include]
    exact norm_add_le a b
  neg' := by
    apply DirectLimit.induction
    intro k a
    change finiteMatrixNorm A (-finiteMatrixInclude A k a) = _
    rw [← map_neg, finiteMatrixNorm_include]
    exact norm_neg a
  eq_zero_of_map_eq_zero' := by
    apply DirectLimit.induction
    intro k a ha
    have hz : a = 0 := norm_eq_zero.mp ha
    change finiteMatrixInclude A k a = 0
    rw [hz, map_zero]

noncomputable instance finiteMatrixNormedAddCommGroup : NormedAddCommGroup (FiniteMatrixLimit A) :=
  (finiteMatrixGroupNorm A).toNormedAddCommGroup

noncomputable instance finiteMatrixTopology : TopologicalSpace (FiniteMatrixLimit A) :=
  (finiteMatrixNormedAddCommGroup A).toMetricSpace.toUniformSpace.toTopologicalSpace

@[simp] lemma finiteMatrixInclude_norm (k : ℕ) (a : MatrixStage A k) :
    ‖finiteMatrixInclude A k a‖ = ‖a‖ := rfl

noncomputable instance finiteMatrixNonUnitalNormedRing : NonUnitalNormedRing (FiniteMatrixLimit A) where
  dist_eq x y := by rw [dist_eq_norm, ← norm_neg]; simp [sub_eq_add_neg, add_comm]
  norm_mul_le := by
    apply DirectLimit.induction₂
    intro k a b
    change ‖finiteMatrixInclude A k a * finiteMatrixInclude A k b‖ ≤ _
    rw [← map_mul, finiteMatrixInclude_norm]
    exact norm_mul_le a b

noncomputable instance finiteMatrixModule : Module ℂ (FiniteMatrixLimit A) where
  one_smul := by
    apply DirectLimit.induction
    intro k a
    simp only [one_smul]
  mul_smul r s := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, mul_smul]
  smul_zero r := by
    rw [DirectLimit.zero_def 0, DirectLimit.smul_def, smul_zero]
  smul_add r := by
    apply DirectLimit.induction₂
    intro k a b
    simp only [DirectLimit.smul_def, DirectLimit.add_def, smul_add]
  add_smul r s := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, DirectLimit.add_def, add_smul]
  zero_smul := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, zero_smul, DirectLimit.zero_def k]

noncomputable instance finiteMatrixNormedSpace : NormedSpace ℂ (FiniteMatrixLimit A) where
  __ : Module ℂ (FiniteMatrixLimit A) := inferInstance
  norm_smul_le z := by
    apply DirectLimit.induction
    intro k a
    change ‖z • finiteMatrixInclude A k a‖ ≤ ‖z‖ * ‖finiteMatrixInclude A k a‖
    rw [← map_smul, finiteMatrixInclude_norm, finiteMatrixInclude_norm]
    exact norm_smul_le z a

noncomputable instance finiteMatrixStarRing : StarRing (FiniteMatrixLimit A) where
  __ : StarAddMonoid (FiniteMatrixLimit A) := inferInstance
  __ : StarMul (FiniteMatrixLimit A) := inferInstance

instance finiteMatrixCStarRing : CStarRing (FiniteMatrixLimit A) where
  norm_mul_self_le := by
    apply DirectLimit.induction
    intro k a
    change ‖finiteMatrixInclude A k a‖ * ‖finiteMatrixInclude A k a‖ ≤
      ‖star (finiteMatrixInclude A k a) * finiteMatrixInclude A k a‖
    rw [← map_star, ← map_mul, finiteMatrixInclude_norm, finiteMatrixInclude_norm]
    exact CStarRing.norm_mul_self_le a

end Pureness

namespace Pureness
open UniformSpace Function Topology
open UniformSpace.Completion
variable (E : Type*) [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
  [NormedSpace ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E]

instance nonUnitalCompletionMul : Mul (Completion E) :=
  ⟨curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
    ((↑) ∘ uncurry (· * · : E → E → E))⟩

instance nonUnitalCompletionContinuousMul : ContinuousMul (Completion E) where
  continuous_mul := by
    let multiplication := (AddMonoidHom.mul : E →+ E →+ E).compr₂ toCompl
    have continuous_multiplication : Continuous fun pair : E × E =>
        multiplication pair.1 pair.2 :=
      (continuous_coe _).comp continuous_mul
    have dense_embedding : IsDenseInducing (toCompl : E → Completion E) := isDenseInducing_coe
    exact (dense_embedding.extend_Z_bilin dense_embedding continuous_multiplication :)

omit [StarRing E] [CStarRing E] [NormedSpace ℂ E] [IsScalarTower ℂ E E]
  [SMulCommClass ℂ E E] [StarModule ℂ E] in
lemma completion_coe_mul (a b : E) :
    ((a * b : E) : Completion E) = (a : Completion E) * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    ((continuous_coe _).comp continuous_mul) (a, b)).symm

instance nonUnitalCompletionNonUnitalRing : NonUnitalRing (Completion E) where
  __ : AddCommGroup (Completion E) := inferInstance
  zero_mul element := Completion.induction_on element
    (isClosed_eq (by fun_prop) continuous_const)
    fun element => by rw [← coe_zero, ← completion_coe_mul, zero_mul]
  mul_zero element := Completion.induction_on element
    (isClosed_eq (by fun_prop) continuous_const)
    fun element => by rw [← coe_zero, ← completion_coe_mul, mul_zero]
  mul_assoc first second third := Completion.induction_on₃ first second third
    (isClosed_eq (by fun_prop) (by fun_prop))
    fun first second third => by simp only [← completion_coe_mul, mul_assoc]
  left_distrib first second third := Completion.induction_on₃ first second third
    (isClosed_eq (by fun_prop) (by fun_prop))
    fun first second third => by simp only [← coe_add, ← completion_coe_mul, mul_add]
  right_distrib first second third := Completion.induction_on₃ first second third
    (isClosed_eq (by fun_prop) (by fun_prop))
    fun first second third => by simp only [← coe_add, ← completion_coe_mul, add_mul]

instance nonUnitalCompletionNonUnitalNormedRing : NonUnitalNormedRing (Completion E) where
  __ : NormedAddCommGroup (Completion E) := inferInstance
  __ : NonUnitalRing (Completion E) := inferInstance
  norm_mul_le first second := Completion.induction_on₂ first second
    (isClosed_le (by fun_prop) (by fun_prop))
    fun first second => by
      simpa only [← completion_coe_mul, norm_coe] using norm_mul_le first second

instance nonUnitalCompletionStar : Star (Completion E) := ⟨Completion.map (star : E → E)⟩

instance nonUnitalCompletionContinuousStar : ContinuousStar (Completion E) :=
  ⟨Completion.continuous_map⟩

omit [NormedSpace ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E] in
lemma completion_coe_star (a : E) :
    ((star a : E) : Completion E) = star (a : Completion E) :=
  (Completion.map_coe star_isometry.uniformContinuous a).symm

instance nonUnitalCompletionStarRing : StarRing (Completion E) where
  star_involutive element := Completion.induction_on element
    (isClosed_eq (by fun_prop) continuous_id)
    fun element => by simp only [← completion_coe_star, star_star]
  star_mul first second := Completion.induction_on₂ first second
    (isClosed_eq (by fun_prop) (by fun_prop))
    fun first second => by simp only [← completion_coe_star, ← completion_coe_mul, star_mul]
  star_add first second := Completion.induction_on₂ first second
    (isClosed_eq (by fun_prop) (by fun_prop))
    fun first second => by simp only [← completion_coe_star, ← coe_add, star_add]

instance nonUnitalCompletionCStarRing : CStarRing (Completion E) where
  norm_mul_self_le element := Completion.induction_on element
    (isClosed_le (by fun_prop) (by fun_prop))
    fun element => by simpa only [← completion_coe_star, ← completion_coe_mul, norm_coe]
      using CStarRing.norm_mul_self_le element

instance nonUnitalCompletionStarModule : StarModule ℂ (Completion E) where
  star_smul scalar element := Completion.induction_on element
    (isClosed_eq (continuous_star.comp (continuous_const_smul scalar))
      ((continuous_const_smul (star scalar)).comp continuous_star))
    fun element => by simp only [← coe_smul, ← completion_coe_star, star_smul]

instance nonUnitalCompletionScalarTower : IsScalarTower ℂ (Completion E) (Completion E) where
  smul_assoc scalar first second := Completion.induction_on₂ first second
    (isClosed_eq ((continuous_fst.const_smul scalar).mul continuous_snd)
      ((continuous_fst.mul continuous_snd).const_smul scalar))
    fun first second => by
      change (scalar • (first : Completion E)) * (second : Completion E) =
        scalar • ((first : Completion E) * second)
      simp only [← coe_smul, ← completion_coe_mul, smul_mul_assoc]

instance nonUnitalCompletionSMulComm : SMulCommClass ℂ (Completion E) (Completion E) where
  smul_comm scalar first second := Completion.induction_on₂ first second
    (isClosed_eq ((continuous_fst.mul continuous_snd).const_smul scalar)
      (continuous_fst.mul (continuous_snd.const_smul scalar)))
    fun first second => by
      change scalar • ((first : Completion E) * second) =
        (first : Completion E) * (scalar • (second : Completion E))
      simp only [← coe_smul, ← completion_coe_mul, mul_smul_comm]

instance nonUnitalCompletionCStarAlgebra : NonUnitalCStarAlgebra (Completion E) where

end Pureness

namespace Pureness
open UniformSpace Function Topology
open UniformSpace.Completion
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev CornerCompletion := Completion (FiniteMatrixLimit A)

instance cornerCompletionCStarAlgebra : NonUnitalCStarAlgebra (CornerCompletion A) := inferInstance

def completedMatrixInclude (k : ℕ) : MatrixStage A k →⋆ₙₐ[ℂ] CornerCompletion A where
  toFun a := (finiteMatrixInclude A k a : CornerCompletion A)
  map_zero' := by simp only [map_zero, coe_zero]
  map_add' a b := by simp only [map_add, coe_add]
  map_mul' a b := by simp only [map_mul, completion_coe_mul]
  map_smul' z a := by simp only [map_smul, coe_smul]; rfl
  map_star' a := by simp only [map_star, completion_coe_star]

lemma completedMatrixInclude_norm (k : ℕ) (a : MatrixStage A k) :
    ‖completedMatrixInclude A k a‖ = ‖a‖ := by
  change ‖(finiteMatrixInclude A k a : CornerCompletion A)‖ = _
  rw [norm_coe, finiteMatrixInclude_norm]

lemma completedMatrixInclude_isometry (k : ℕ) : Isometry (completedMatrixInclude A k) :=
  AddMonoidHomClass.isometry_of_norm _ (completedMatrixInclude_norm A k)

lemma completedMatrixInclude_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedMatrixInclude A l (corner h a) = completedMatrixInclude A k a := by
  change (finiteMatrixInclude A l (corner h a) : CornerCompletion A) = _
  rw [finiteMatrixInclude_corner]
  rfl

theorem completedMatrixInclude_dense :
    Dense (⋃ k : ℕ, Set.range (completedMatrixInclude A k)) := by
  have heq : (⋃ k : ℕ, Set.range (completedMatrixInclude A k)) =
      Set.range ((↑) : FiniteMatrixLimit A → CornerCompletion A) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨k, a, rfl⟩; exact ⟨finiteMatrixInclude A k a, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨k, a, rfl⟩ := DirectLimit.exists_eq_mk (matrixConnecting A) y
      exact ⟨k, a, rfl⟩
  rw [heq]
  exact denseRange_coe

end Pureness

namespace Pureness
open Filter Topology
open scoped ComplexOrder
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance cornerCompletionOrder : PartialOrder (CornerCompletion A) := CStarAlgebra.spectralOrder _

instance cornerCompletionStarOrdered : StarOrderedRing (CornerCompletion A) := CStarAlgebra.spectralOrderedRing _

lemma completedMatrixInclude_nonneg (k : ℕ) (a : MatrixStage A k) (ha : 0 ≤ a) :
    0 ≤ completedMatrixInclude A k a := by
  obtain ⟨x, rfl⟩ := positive_square_factor a ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

def completedProjection (k : ℕ) : CornerCompletion A := completedMatrixInclude A k 1

lemma completedProjection_star (k : ℕ) : star (completedProjection A k) = completedProjection A k := by
  change star (completedMatrixInclude A k 1) = completedMatrixInclude A k 1
  rw [← map_star, star_one]

lemma completedProjection_norm_le (k : ℕ) : ‖completedProjection A k‖ ≤ 1 := by
  change ‖completedMatrixInclude A k 1‖ ≤ 1
  rw [completedMatrixInclude_norm]
  cases subsingleton_or_nontrivial (MatrixStage A k)
  · rw [Subsingleton.elim (1 : MatrixStage A k) 0, norm_zero]; exact zero_le_one
  · exact le_of_eq norm_one

def completedCornerCut (k : ℕ) (a : CornerCompletion A) : CornerCompletion A :=
  completedProjection A k * a * completedProjection A k

lemma completedCornerCut_continuous (k : ℕ) : Continuous (completedCornerCut A k) := by
  unfold completedCornerCut
  fun_prop

lemma completedCornerCut_sub (k : ℕ) (a b : CornerCompletion A) :
    completedCornerCut A k (a - b) = completedCornerCut A k a - completedCornerCut A k b := by
  simp only [completedCornerCut, mul_sub, sub_mul]

lemma completedCornerCut_norm_le (k : ℕ) (a : CornerCompletion A) :
    ‖completedCornerCut A k a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖completedProjection A k‖ * ‖a‖ * ‖completedProjection A k‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (completedProjection_norm_le A k) (norm_nonneg _))
      (completedProjection_norm_le A k) (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

lemma completedCornerCut_fixes {l k : ℕ} (h : l ≤ k) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) = completedMatrixInclude A l a := by
  rw [← completedMatrixInclude_corner A h a]
  change completedMatrixInclude A k 1 * completedMatrixInclude A k (corner h a) *
    completedMatrixInclude A k 1 = _
  rw [← map_mul, ← map_mul, one_mul, mul_one]

theorem completedCornerCut_tendsto (a : CornerCompletion A) :
    Tendsto (fun k : ℕ => completedCornerCut A k a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha := completedMatrixInclude_dense A a
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp ha (ε / 2) (by positivity)
  obtain ⟨l, c, rfl⟩ := Set.mem_iUnion.mp hb
  refine ⟨l, fun k hk => ?_⟩
  have hfix := completedCornerCut_fixes A hk c
  have heq : completedCornerCut A k a - a =
      completedCornerCut A k (a - completedMatrixInclude A l c) +
        (completedMatrixInclude A l c - a) := by
    rw [completedCornerCut_sub, hfix]
    abel
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖completedCornerCut A k (a - completedMatrixInclude A l c)‖ +
        ‖completedMatrixInclude A l c - a‖ := norm_add_le _ _
    _ ≤ ‖a - completedMatrixInclude A l c‖ + ‖completedMatrixInclude A l c - a‖ :=
      add_le_add (completedCornerCut_norm_le A k _) le_rfl
    _ < ε := by
      rw [norm_sub_rev (completedMatrixInclude A l c)]
      rw [dist_eq_norm] at hab
      linarith

lemma completedCornerCut_nonneg (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    0 ≤ completedCornerCut A k a := by
  simpa only [completedCornerCut, completedProjection_star] using star_left_conjugate_nonneg ha (completedProjection A k)

end Pureness

namespace TraceCone
open scoped CStarAlgebra
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev FinMatrix (A : Type*) (n : ℕ) := CStarMatrix (Fin n) (Fin n) A


def matrixSuccessor (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A (n+1) where
  toFun M := CStarMatrix.ofMatrix (fun i j =>
    Fin.lastCases 0 (fun i => Fin.lastCases 0 (M i) j) i)
  map_zero' := by
    ext row column
    change Fin.lastCases (motive := fun _ => A) 0
      (fun _ : Fin n => Fin.lastCases 0 (fun _ => (0 : A)) column) row = 0
    refine Fin.lastCases ?_ (fun row => ?_) row
    · simp
    · refine Fin.lastCases ?_ (fun column => ?_) column <;> simp
  map_add' M N := by
    ext row column
    change Fin.lastCases (motive := fun _ => A) 0
      (fun row => Fin.lastCases 0 (fun column => M row column + N row column) column) row =
      Fin.lastCases (motive := fun _ => A) 0 (fun row => Fin.lastCases 0 (M row) column) row +
        Fin.lastCases (motive := fun _ => A) 0 (fun row => Fin.lastCases 0 (N row) column) row
    refine Fin.lastCases ?_ (fun row => ?_) row
    · simp
    · refine Fin.lastCases ?_ (fun column => ?_) column <;> simp
  map_mul' M N := by
    ext row column
    change Fin.lastCases (motive := fun _ => A) 0
      (fun row => Fin.lastCases 0 (fun column => ∑ index, M row index * N index column) column) row =
      ∑ index : Fin (n + 1),
        Fin.lastCases (motive := fun _ => A) 0 (fun row => Fin.lastCases 0 (M row) index) row *
          Fin.lastCases (motive := fun _ => A) 0 (fun index => Fin.lastCases 0 (N index) column) index
    refine Fin.lastCases ?_ (fun row => ?_) row
    · simp
    · refine Fin.lastCases ?_ (fun column => ?_) column
      · simp [Fin.sum_univ_castSucc]
      · simp [Fin.sum_univ_castSucc]
  map_smul' c M := by
    ext row column
    change Fin.lastCases (motive := fun _ => A) 0
      (fun row => Fin.lastCases 0 (fun column => c • M row column) column) row =
      c • Fin.lastCases (motive := fun _ => A) 0 (fun row => Fin.lastCases 0 (M row) column) row
    refine Fin.lastCases ?_ (fun row => ?_) row
    · simp
    · refine Fin.lastCases ?_ (fun column => ?_) column <;> simp
  map_star' M := by
    ext row column
    change Fin.lastCases (motive := fun _ => A) 0
      (fun row => Fin.lastCases 0 (fun column => star (M column row)) column) row =
      star (Fin.lastCases (motive := fun _ => A) 0
        (fun column => Fin.lastCases 0 (M column) row) column)
    refine Fin.lastCases ?_ (fun row => ?_) row
    · refine Fin.lastCases ?_ (fun column => ?_) column <;> simp
    · refine Fin.lastCases ?_ (fun column => ?_) column <;> simp

def matrixPad {n m : ℕ} (h : n ≤ m) : FinMatrix A n → FinMatrix A m :=
  Nat.leRecOn h (fun {k} => matrixSuccessor k)

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixPad_succ {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixPad (Nat.le.step h) M = matrixSuccessor m (matrixPad h M) :=
  Nat.leRecOn_succ h M

def matrixInclusion {n m : ℕ} (h : n ≤ m) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A m where
  toFun := matrixPad h
  map_zero' := by
    induction m, h using Nat.le_induction with
    | base => simp only [matrixPad, Nat.leRecOn_self]
    | succ m h ih => rw [matrixPad_succ h, ih, map_zero]
  map_add' M N := by
    induction m, h using Nat.le_induction with
    | base => simp only [matrixPad, Nat.leRecOn_self]
    | succ m h ih => simp only [matrixPad_succ h, ih, map_add]
  map_mul' M N := by
    induction m, h using Nat.le_induction with
    | base => simp only [matrixPad, Nat.leRecOn_self]
    | succ m h ih => simp only [matrixPad_succ h, ih, map_mul]
  map_smul' c M := by
    induction m, h using Nat.le_induction with
    | base => simp only [matrixPad, Nat.leRecOn_self, MonoidHom.id_apply]
    | succ m h ih => simp only [matrixPad_succ h, ih, map_smul]
  map_star' M := by
    induction m, h using Nat.le_induction with
    | base => simp only [matrixPad, Nat.leRecOn_self]
    | succ m h ih => simp only [matrixPad_succ h, ih, map_star]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixSuccessor_apply_castSucc (n : ℕ) (M : FinMatrix A n) (row column : Fin n) :
    matrixSuccessor n M row.castSucc column.castSucc = M row column := by
  change Fin.lastCases 0
    (fun row => Fin.lastCases 0 (M row) column.castSucc) row.castSucc = M row column
  simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixSuccessor_injective (n : ℕ) : Function.Injective (matrixSuccessor (A := A) n) := by
  intro first second equality
  ext row column
  simpa only [matrixSuccessor_apply_castSucc] using
    congrArg (fun matrix : FinMatrix A (n + 1) => matrix row.castSucc column.castSucc) equality

lemma matrixSuccessor_isometry (n : ℕ) : Isometry (matrixSuccessor (A := A) n) :=
  NonUnitalStarAlgHom.isometry _ (matrixSuccessor_injective n)

@[simp] lemma matrixSuccessor_norm (n : ℕ) (M : FinMatrix A n) :
    ‖matrixSuccessor n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixSuccessor_injective n) M

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixPad_self (n : ℕ) (M : FinMatrix A n) : matrixPad le_rfl M = M :=
  Nat.leRecOn_self M

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixPad_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (M : FinMatrix A n) :
    matrixPad g (matrixPad h M) = matrixPad (h.trans g) M :=
  (Nat.leRecOn_trans h g M).symm

@[simp] lemma matrixInclusion_norm {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    ‖matrixInclusion h M‖ = ‖M‖ := by
  change ‖matrixPad h M‖ = ‖M‖
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih => rw [matrixPad_succ h, matrixSuccessor_norm, ih]

lemma matrixInclusion_isometry {n m : ℕ} (h : n ≤ m) :
    Isometry (matrixInclusion (A := A) h) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixInclusion_norm h)

@[simp] lemma matrixInclusion_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k)
    (M : FinMatrix A n) :
    matrixInclusion g (matrixInclusion h M) = matrixInclusion (h.trans g) M :=
  matrixPad_trans h g M

end TraceCone

section
open scoped ENNReal Topology
open Filter
namespace TraceCone
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]

abbrev BoundedFamilies := lp A ∞

end TraceCone
end

section
open scoped ENNReal Topology
open Filter
namespace TraceCone
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]
namespace BoundedFamilies
variable {A}

lemma norm_coordinate_le (x : BoundedFamilies A) (n : ℕ) : ‖x n‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp) x n

def vanishing : Submodule ℂ (BoundedFamilies A) where
  carrier := {x | Tendsto (fun n => ‖x n‖) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' hx hy := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_add_le _ _)
    simpa using hx.add hy
  smul_mem' c x hx := by
    change Tendsto (fun n => ‖c • x n‖) atTop (𝓝 0)
    simpa only [norm_smul, mul_zero] using (tendsto_const_nhds (x := ‖c‖)).mul hx

@[simp] lemma mem_vanishing (x : BoundedFamilies A) : x ∈ vanishing (A := A) ↔
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := Iff.rfl

lemma mul_mem_vanishing_left (x : BoundedFamilies A) {y : BoundedFamilies A}
    (hy : y ∈ vanishing (A := A)) : x*y ∈ vanishing (A := A) := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x‖*‖y n‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ‖x‖)).mul hy
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_right (norm_coordinate_le x n) (norm_nonneg _))

lemma mul_mem_vanishing_right {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A))
    (y : BoundedFamilies A) : x*y ∈ vanishing (A := A) := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x n‖*‖y‖) atTop (𝓝 0) := by
    simpa using hx.mul (tendsto_const_nhds (x := ‖y‖))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_left (norm_coordinate_le y n) (norm_nonneg _))

lemma star_mem_vanishing {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A)) : star x ∈ vanishing (A := A) := by
  change Tendsto (fun n => ‖star (x n)‖) atTop (𝓝 0)
  simpa only [norm_star] using (mem_vanishing x).mp hx

instance vanishing_closed : IsClosed (vanishing (A := A) : Set (BoundedFamilies A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => ‖x n‖) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hdiff : ‖x n-y n‖ < ε/2 := by
    have h := norm_coordinate_le (x-y) n
    exact h.trans_lt (by simpa only [dist_eq_norm] using hxy)
  have htail : ‖y n‖ < ε/2 := by simpa using hN n hn
  rw [dist_zero_right, norm_norm]
  have h : ‖x n‖ ≤ ‖x n-y n‖+‖y n‖ := norm_le_norm_sub_add _ _
  linarith

def vanishingCon : RingCon (BoundedFamilies A) where
  toSetoid := (vanishing (A := A)).quotientRel
  add' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    convert (vanishing (A := A)).add_mem hxy huv using 1; abel
  mul' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    have h := (vanishing (A := A)).add_mem (mul_mem_vanishing_right hxy u)
      (mul_mem_vanishing_left y huv)
    convert h using 1; noncomm_ring

end BoundedFamilies
end TraceCone
end

section
open scoped ENNReal Topology
open Filter Metric
namespace TraceCone
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]

def FamilyQuotient := (BoundedFamilies.vanishingCon (A := A)).Quotient

end TraceCone
end

section
open scoped ENNReal Topology
open Filter Metric
namespace TraceCone
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]
namespace FamilyQuotient
open BoundedFamilies
variable {A}

instance : NonUnitalRing (FamilyQuotient A) :=
  inferInstanceAs (NonUnitalRing (vanishingCon (A := A)).Quotient)

instance : NormedAddCommGroup (FamilyQuotient A) :=
  inferInstanceAs (NormedAddCommGroup (BoundedFamilies A ⧸ vanishing (A := A)))

instance : Module ℂ (FamilyQuotient A) :=
  inferInstanceAs (Module ℂ (BoundedFamilies A ⧸ vanishing (A := A)))

instance : NormedSpace ℂ (FamilyQuotient A) :=
  inferInstanceAs (NormedSpace ℂ (BoundedFamilies A ⧸ vanishing (A := A)))

instance : CompleteSpace (FamilyQuotient A) :=
  inferInstanceAs (CompleteSpace (BoundedFamilies A ⧸ vanishing (A := A)))

def mk (x : BoundedFamilies A) : FamilyQuotient A := Submodule.Quotient.mk x

@[simp] lemma mk_mul (x y : BoundedFamilies A) : mk (x*y) = mk x*mk y := rfl

lemma mk_surjective : Function.Surjective (mk (A := A)) := Quotient.mk_surjective

lemma mk_eq_mk_iff (x y : BoundedFamilies A) : mk x = mk y ↔ x-y ∈ vanishing (A := A) :=
  Submodule.Quotient.eq _

lemma norm_mk_le (x : BoundedFamilies A) : ‖mk x‖ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le _ _

lemma exists_norm_mk_lt (x : FamilyQuotient A) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedFamilies A, mk a = x ∧ ‖a‖ < ‖x‖+ε := Submodule.Quotient.norm_mk_lt x hε

instance : NonUnitalNormedRing (FamilyQuotient A) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have h := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at h
    obtain ⟨ε₁, ε₂, ⟨h₁,h₂⟩, h⟩ := h
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x h₁
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le a]⟩
      ⟨by linarith, by linarith [norm_mk_le b]⟩
    exact ((norm_mk_le (a*b)).trans (norm_mul_le a b)).trans (sub_lt_iff_lt_add'.mp h.1).le

instance : Star (FamilyQuotient A) := ⟨Quotient.map' star (by
  intro x y h
  change (vanishing (A := A)).quotientRel x y at h
  change (vanishing (A := A)).quotientRel (star x) (star y)
  rw [Submodule.quotientRel_def] at h ⊢
  simpa only [star_sub] using star_mem_vanishing h)⟩

@[simp] lemma mk_star (x : BoundedFamilies A) : mk (star x) = star (mk x) := rfl

instance : StarRing (FamilyQuotient A) where
  star_involutive := by
    intro x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg mk (star_star x)
  star_mul := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (star_mul x y)
  star_add := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (star_add x y)

instance : StarModule ℂ (FamilyQuotient A) where
  star_smul := by
    intro c x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg mk (star_smul c x)

instance : IsScalarTower ℂ (FamilyQuotient A) (FamilyQuotient A) where
  smul_assoc := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (smul_mul_assoc c x y)

instance : SMulCommClass ℂ (FamilyQuotient A) (FamilyQuotient A) where
  smul_comm := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg mk (smul_comm c x y)

end FamilyQuotient
end TraceCone
end

section
open scoped ENNReal Topology
open Filter
namespace TraceCone
variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
namespace BoundedFamilies

lemma norm_bounded (x : BoundedFamilies A) :
    IsBoundedUnder (· ≤ ·) atTop (fun n => ‖x n‖) :=
  isBoundedUnder_of ⟨‖x‖, norm_coordinate_le x⟩

lemma norm_cobounded (x : BoundedFamilies A) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n => ‖x n‖) :=
  (isBoundedUnder_of ⟨0, fun n => norm_nonneg (x n)⟩ :
    IsBoundedUnder (· ≥ ·) atTop (fun n => ‖x n‖)).isCoboundedUnder_le

lemma limsup_norm_nonneg (x : BoundedFamilies A) :
    0 ≤ limsup (fun n => ‖x n‖) atTop :=
  le_limsup_of_frequently_le (Eventually.of_forall (fun n => norm_nonneg (x n))).frequently (norm_bounded x)

lemma limsup_norm_le_of_vanishing_sub (x y : BoundedFamilies A)
    (h : x-y ∈ vanishing (A := A)) : limsup (fun n => ‖x n‖) atTop ≤ ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (norm_cobounded x)
  have he : ∀ᶠ n in atTop, ‖x n-y n‖ < ε := by
    have h0 := h
    have h0' : Tendsto (fun n => ‖x n-y n‖) atTop (𝓝 0) := h0
    exact (tendsto_order.mp h0').2 ε hε
  filter_upwards [he] with n hn
  have ht := norm_le_norm_sub_add (x n) (y n)
  have hy := norm_coordinate_le y n
  linarith

def tail (x : BoundedFamilies A) (N : ℕ) : BoundedFamilies A :=
  ⟨fun n => if N ≤ n then x n else 0, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n,rfl⟩
    change ‖if N ≤ n then x n else 0‖ ≤ ‖x‖
    split_ifs
    · exact norm_coordinate_le x n
    · simpa only [norm_zero] using norm_nonneg x⟩⟩

lemma tail_sub_mem (x : BoundedFamilies A) (N : ℕ) : tail x N-x ∈ vanishing (A := A) := by
  change Tendsto (fun n => ‖(tail x N) n-x n‖) atTop (𝓝 0)
  apply (tendsto_congr' (show (fun n => ‖(tail x N) n-x n‖) =ᶠ[atTop] fun _ => (0 : ℝ) from ?_)).mpr
    tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [tail, hn]

lemma norm_tail_le (x : BoundedFamilies A) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, N ≤ n → ‖x n‖ ≤ C) : ‖tail x N‖ ≤ C := by
  apply lp.norm_le_of_forall_le hC
  intro n
  change ‖if N ≤ n then x n else 0‖ ≤ C
  split_ifs with hn
  · exact h n hn
  · simpa using hC

end BoundedFamilies
end TraceCone
end

section
open scoped ENNReal Topology
open Filter
namespace TraceCone
variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
namespace FamilyQuotient
open BoundedFamilies

theorem norm_mk_eq_limsup (x : BoundedFamilies A) :
    ‖mk x‖ = limsup (fun n => ‖x n‖) atTop := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt
      (lt_add_of_pos_right (limsup (fun n => ‖x n‖) atTop) hε) (norm_bounded x))
    have heq : mk (tail x N) = mk x := (mk_eq_mk_iff _ _).mpr (tail_sub_mem x N)
    rw [← heq]
    exact (norm_mk_le _).trans (norm_tail_le x N _ (by linarith [limsup_norm_nonneg x])
      (fun n hn => (hN n hn).le))
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hy,hn⟩ := exists_norm_mk_lt (mk x) hε
    have hxy : x-y ∈ vanishing (A := A) := (mk_eq_mk_iff _ _).mp hy.symm
    exact (limsup_norm_le_of_vanishing_sub x y hxy).trans hn.le

lemma norm_star_mul_self_eq (x : FamilyQuotient A) : ‖star x*x‖ = ‖x‖*‖x‖ := by
  obtain ⟨x,rfl⟩ := mk_surjective x
  rw [← mk_star, ← mk_mul, norm_mk_eq_limsup, norm_mk_eq_limsup]
  let f : ℝ → ℝ := fun t => max t 0 * max t 0
  have hf : Monotone f := by
    intro a b hab
    exact mul_self_le_mul_self (le_max_right _ _) (max_le_max hab le_rfl)
  have hc : Continuous f := (continuous_id.max continuous_const).mul (continuous_id.max continuous_const)
  have h := hf.map_limsup_of_continuousAt (fun n => ‖x n‖) hc.continuousAt
    (norm_bounded x) (norm_cobounded x)
  have he : f ∘ (fun n => ‖x n‖) = fun n => ‖star (x n)*x n‖ := by
    funext n
    simp only [Function.comp_apply, f, max_eq_left (norm_nonneg (x n)), CStarRing.norm_star_mul_self]
  rw [he] at h
  dsimp [f] at h
  rw [max_eq_left (limsup_norm_nonneg x)] at h
  exact h.symm

instance : CStarRing (FamilyQuotient A) where
  norm_mul_self_le x := (norm_star_mul_self_eq x).symm.le

instance : NonUnitalCStarAlgebra (FamilyQuotient A) where

end FamilyQuotient
end TraceCone
end

section
open scoped ENNReal Topology CStarAlgebra
open Filter
namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixFamily (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] BoundedFamilies (FinMatrix A) where
  toFun M := ⟨fun m => if h : n ≤ m then matrixInclusion h M else 0,
    memℓp_infty ⟨‖M‖, by
      rintro _ ⟨m,rfl⟩
      change ‖if h : n ≤ m then matrixInclusion h M else 0‖ ≤ ‖M‖
      split_ifs <;> simp_all [norm_nonneg]⟩⟩
  map_zero' := by apply lp.ext; funext m; change (if h : n ≤ m then matrixInclusion h 0 else 0) = 0; split_ifs <;> simp_all
  map_add' M N := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (M+N) else 0) =
      (if h : n ≤ m then matrixInclusion h M else 0) + (if h : n ≤ m then matrixInclusion h N else 0)
    split_ifs <;> simp_all
  map_mul' M N := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (M*N) else 0) =
      (if h : n ≤ m then matrixInclusion h M else 0) * (if h : n ≤ m then matrixInclusion h N else 0)
    split_ifs <;> simp_all
  map_smul' c M := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (c • M) else 0) =
      c • (if h : n ≤ m then matrixInclusion h M else 0)
    split_ifs <;> simp_all
  map_star' M := by
    apply lp.ext; funext m
    change (if h : n ≤ m then matrixInclusion h (star M) else 0) =
      star (if h : n ≤ m then matrixInclusion h M else 0)
    by_cases h : n ≤ m
    · rw [dite_eq_left h, dite_eq_left h]
      exact map_star (matrixInclusion h) M
    · rw [dite_eq_right h, dite_eq_right h]
      exact (star_zero _).symm

end TraceCone
end

section
open scoped ENNReal Topology CStarAlgebra
open Filter
namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace FamilyQuotient
variable {F : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (F n)]

def quotientHom : BoundedFamilies F →⋆ₙₐ[ℂ] FamilyQuotient F where
  toFun := mk
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma mk_eq_of_eventually_eq (x y : BoundedFamilies F) (h : ∀ᶠ n in atTop, x n = y n) : mk x = mk y := by
  apply (mk_eq_mk_iff _ _).mpr
  change Tendsto (fun n => ‖x n-y n‖) atTop (𝓝 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with n hn
  simp [hn]

end FamilyQuotient
end TraceCone
end

section
open scoped ENNReal Topology CStarAlgebra
open Filter
namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] FamilyQuotient (FinMatrix A) :=
  FamilyQuotient.quotientHom.comp (matrixFamily n)

@[simp] lemma matrixStage_norm (n : ℕ) (M : FinMatrix A n) : ‖matrixStage n M‖ = ‖M‖ := by
  change ‖FamilyQuotient.mk (matrixFamily n M)‖ = _
  rw [FamilyQuotient.norm_mk_eq_limsup]
  calc
    _ = limsup (fun _ : ℕ => ‖M‖) atTop := limsup_congr (by
      filter_upwards [eventually_ge_atTop n] with m hm
      change ‖if h : n ≤ m then matrixInclusion h M else 0‖ = ‖M‖
      simp [hm])
    _ = ‖M‖ := limsup_const (b := ‖M‖)

@[simp] lemma matrixStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixStage m (matrixInclusion h M) = matrixStage n M := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop m] with k hk
  change (if g : m ≤ k then matrixInclusion g (matrixInclusion h M) else 0) =
    (if g : n ≤ k then matrixInclusion g M else 0)
  simp [hk, h.trans hk]

end TraceCone
end

section
open scoped ENNReal Topology CStarAlgebra
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixUnion : NonUnitalStarSubalgebra ℂ (FamilyQuotient (FinMatrix A)) where
  carrier := {x | ∃ (n : ℕ) (M : FinMatrix A n), matrixStage n M = x}
  zero_mem' := ⟨0,0,map_zero _⟩
  add_mem' := by
    rintro x y ⟨n,M,rfl⟩ ⟨m,N,rfl⟩
    refine ⟨max n m, matrixInclusion (le_max_left n m) M + matrixInclusion (le_max_right n m) N, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨n,M,rfl⟩ ⟨m,N,rfl⟩
    refine ⟨max n m, matrixInclusion (le_max_left n m) M * matrixInclusion (le_max_right n m) N, ?_⟩
    simp
  smul_mem' := by
    rintro c x ⟨n,M,rfl⟩
    exact ⟨n,c • M,map_smul _ c M⟩
  star_mem' := by
    rintro x ⟨n,M,rfl⟩
    exact ⟨n,star M,map_star _ M⟩

def matrixLimitAlgebra : NonUnitalStarSubalgebra ℂ (FamilyQuotient (FinMatrix A)) :=
  (matrixUnion A).topologicalClosure

instance matrixLimitAlgebra_closed : IsClosed (matrixLimitAlgebra A : Set (FamilyQuotient (FinMatrix A))) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev MatrixLimit := matrixLimitAlgebra A

instance : NonUnitalCStarAlgebra (MatrixLimit A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (matrixLimitAlgebra A)

end TraceCone
end

section
open scoped ENNReal Topology CStarAlgebra
namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {A}

def matrixLimitStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] MatrixLimit A where
  toFun M := ⟨matrixStage n M, NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨n,M,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' M N := Subtype.ext (map_add _ M N)
  map_mul' M N := Subtype.ext (map_mul _ M N)
  map_smul' c M := Subtype.ext (map_smul _ c M)
  map_star' M := Subtype.ext (map_star _ M)

@[simp] lemma matrixLimitStage_norm (n : ℕ) (M : FinMatrix A n) : ‖matrixLimitStage n M‖ = ‖M‖ :=
  matrixStage_norm n M

lemma matrixLimitStage_isometry (n : ℕ) : Isometry (matrixLimitStage (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixLimitStage_norm n)

@[simp] lemma matrixLimitStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixLimitStage m (matrixInclusion h M) = matrixLimitStage n M :=
  Subtype.ext (matrixStage_compatible h M)

theorem matrixLimit_finite_approximation (x : MatrixLimit A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (M : FinMatrix A n), ‖x-matrixLimitStage n M‖ < ε := by
  obtain ⟨y,⟨n,M,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp x.2 ε hε
  refine ⟨n,M,?_⟩
  change ‖(x : FamilyQuotient (FinMatrix A))-matrixStage n M‖ < ε
  simpa only [dist_eq_norm] using hy

end TraceCone
end

section
open scoped Topology
namespace TraceCone
variable {D B : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra B]

def extendDenseStarHom (S : NonUnitalStarSubalgebra ℂ D) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (hd : DenseRange (fun x : S => (x : D))) : D →⋆ₙₐ[ℂ] B := by
  let l : S →ₗ[ℂ] B := { toFun := f, map_add' := f.map_add, map_smul' := f.map_smul }
  let L : S →L[ℂ] B := l.mkContinuous 1 (fun x => by simpa [l] using hf x)
  let E : D →L[ℂ] B := L.extend S.toSubmodule.subtypeL
  have heq (x : S) : E (x : D) = f x :=
    ContinuousLinearMap.extend_eq L (e := S.toSubmodule.subtypeL) hd isometry_subtype_coe.isUniformInducing x
  exact {
    toFun := E
    map_zero' := E.map_zero
    map_add' := E.map_add
    map_smul' := E.map_smul
    map_mul' := by
      refine hd.induction_on₂ ?_ ?_
      · exact isClosed_eq (E.continuous.comp continuous_mul)
          ((E.continuous.comp continuous_fst).mul (E.continuous.comp continuous_snd))
      · intro x y
        change E ((x*y : S) : D) = E (x : D)*E (y : D)
        rw [heq,heq,heq,map_mul]
    map_star' := by
      intro a
      refine hd.induction_on a ?_ ?_
      · exact isClosed_eq (E.continuous.comp continuous_star) E.continuous.star
      · intro x
        change E ((star x : S) : D) = star (E (x : D))
        rw [heq,heq,map_star] }

theorem extendDenseStarHom_eq (S : NonUnitalStarSubalgebra ℂ D) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (hd : DenseRange (fun x : S => (x : D))) (x : S) :
    extendDenseStarHom S f hf hd (x : D) = f x :=
  ContinuousLinearMap.extend_eq _ hd isometry_subtype_coe.isUniformInducing x

end TraceCone
end

section
open scoped Topology CStarAlgebra
namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B]

def finiteMatrixSubalgebra : NonUnitalStarSubalgebra ℂ (MatrixLimit A) :=
  (matrixUnion A).comap (NonUnitalStarSubalgebraClass.subtype (matrixLimitAlgebra A))

def finiteMatrixStage (n : ℕ) (M : FinMatrix A n) : finiteMatrixSubalgebra (A := A) :=
  ⟨matrixLimitStage n M,⟨n,M,rfl⟩⟩

lemma finiteMatrixStage_surjective (x : finiteMatrixSubalgebra (A := A)) :
    ∃ (n : ℕ) (M : FinMatrix A n), finiteMatrixStage n M = x := by
  obtain ⟨n,M,hM⟩ := x.2
  exact ⟨n,M,Subtype.ext (Subtype.ext hM)⟩

lemma finiteMatrixSubalgebra_dense : DenseRange (fun x : finiteMatrixSubalgebra (A := A) => (x : MatrixLimit A)) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n,M,hM⟩ := matrixLimit_finite_approximation x hε
  exact ⟨matrixLimitStage n M,⟨finiteMatrixStage n M,rfl⟩,by simpa only [dist_eq_norm] using hM⟩

def finiteMatrixRepresentative (x : finiteMatrixSubalgebra (A := A)) : Σ n, FinMatrix A n :=
  ⟨(finiteMatrixStage_surjective x).choose,(finiteMatrixStage_surjective x).choose_spec.choose⟩

lemma finiteMatrixRepresentative_spec (x : finiteMatrixSubalgebra (A := A)) :
    finiteMatrixStage (finiteMatrixRepresentative x).1 (finiteMatrixRepresentative x).2 = x :=
  (finiteMatrixStage_surjective x).choose_spec.choose_spec

end TraceCone
end

section
open scoped Topology CStarAlgebra
namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B]
variable (f : ∀ n, FinMatrix A n →⋆ₙₐ[ℂ] B)
variable (hf : ∀ {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n), f m (matrixInclusion h M) = f n M)

def finiteMatrixLiftValue (x : finiteMatrixSubalgebra (A := A)) : B :=
  f (finiteMatrixRepresentative x).1 (finiteMatrixRepresentative x).2

include hf in
lemma finiteMatrixLiftValue_eq (x : finiteMatrixSubalgebra (A := A)) (n : ℕ) (M : FinMatrix A n)
    (hx : finiteMatrixStage n M = x) : finiteMatrixLiftValue f x = f n M := by
  let r := finiteMatrixRepresentative x
  have he : matrixLimitStage r.1 r.2 = matrixLimitStage n M :=
    congrArg Subtype.val ((finiteMatrixRepresentative_spec x).trans hx.symm)
  have hm : matrixInclusion (le_max_left r.1 n) r.2 = matrixInclusion (le_max_right r.1 n) M := by
    apply (matrixLimitStage_isometry (max r.1 n)).injective
    simpa only [matrixLimitStage_compatible] using he
  change f r.1 r.2 = f n M
  rw [← hf (le_max_left r.1 n) r.2,← hf (le_max_right r.1 n) M,hm]

include hf in
@[simp] lemma finiteMatrixLiftValue_stage (n : ℕ) (M : FinMatrix A n) :
    finiteMatrixLiftValue f (finiteMatrixStage n M) = f n M :=
  finiteMatrixLiftValue_eq f hf _ n M rfl

lemma finiteMatrix_common_stage (x y : finiteMatrixSubalgebra (A := A)) :
    ∃ (n : ℕ) (M N : FinMatrix A n), finiteMatrixStage n M = x ∧ finiteMatrixStage n N = y := by
  obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
  obtain ⟨m,N,rfl⟩ := finiteMatrixStage_surjective y
  refine ⟨max n m,matrixInclusion (le_max_left n m) M,matrixInclusion (le_max_right n m) N,?_,?_⟩
  · exact Subtype.ext (matrixLimitStage_compatible _ _)
  · exact Subtype.ext (matrixLimitStage_compatible _ _)

def finiteMatrixLift : finiteMatrixSubalgebra (A := A) →⋆ₙₐ[ℂ] B where
  toFun := finiteMatrixLiftValue f
  map_zero' := by
    have hz : finiteMatrixStage (A := A) 0 0 = 0 := Subtype.ext (map_zero _)
    rw [← hz,finiteMatrixLiftValue_stage f hf,map_zero]
  map_add' x y := by
    obtain ⟨n,M,N,rfl,rfl⟩ := finiteMatrix_common_stage x y
    have he : finiteMatrixStage n (M+N) = finiteMatrixStage n M + finiteMatrixStage n N := Subtype.ext (map_add _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_add]
  map_mul' x y := by
    obtain ⟨n,M,N,rfl,rfl⟩ := finiteMatrix_common_stage x y
    have he : finiteMatrixStage n (M*N) = finiteMatrixStage n M * finiteMatrixStage n N := Subtype.ext (map_mul _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_mul]
  map_smul' c x := by
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
    have he : finiteMatrixStage n (c • M) = c • finiteMatrixStage n M := Subtype.ext (map_smul _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_smul]
    rfl
  map_star' x := by
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
    have he : finiteMatrixStage n (star M) = star (finiteMatrixStage n M) := Subtype.ext (map_star _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_star]

lemma finiteMatrixLift_norm_le (x : finiteMatrixSubalgebra (A := A)) : ‖finiteMatrixLift f hf x‖ ≤ ‖x‖ := by
  obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
  change ‖finiteMatrixLiftValue f (finiteMatrixStage n M)‖ ≤ ‖matrixLimitStage n M‖
  rw [finiteMatrixLiftValue_stage f hf,matrixLimitStage_norm]
  exact NonUnitalStarAlgHom.norm_apply_le (f n) M

def matrixLimitLift : MatrixLimit A →⋆ₙₐ[ℂ] B :=
  extendDenseStarHom finiteMatrixSubalgebra (finiteMatrixLift f hf)
    (finiteMatrixLift_norm_le f hf) finiteMatrixSubalgebra_dense

@[simp] theorem matrixLimitLift_stage (n : ℕ) (M : FinMatrix A n) :
    matrixLimitLift f hf (matrixLimitStage n M) = f n M := by
  change extendDenseStarHom _ _ _ _ ((finiteMatrixStage n M : finiteMatrixSubalgebra) : MatrixLimit A) = _
  rw [extendDenseStarHom_eq]
  exact finiteMatrixLiftValue_stage f hf n M

end TraceCone
end

section
namespace Pureness
open Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma shared_matrixSuccessor_eq_corner (k : ℕ) (a : MatrixStage A k) :
    TraceCone.matrixSuccessor k a = corner (Nat.le_succ k) a := by
  ext row column
  change Fin.lastCases 0 (fun row => Fin.lastCases 0 (a row) column) row =
    if hrow : row.val < k then
      if hcolumn : column.val < k then a ⟨row.val, hrow⟩ ⟨column.val, hcolumn⟩ else 0
    else 0
  refine Fin.lastCases ?_ (fun row => ?_) row
  · simp
  · refine Fin.lastCases ?_ (fun column => ?_) column
    · simp
    · simp [row.isLt, column.isLt]

lemma shared_matrixInclusion_eq_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    TraceCone.matrixInclusion h a = corner h a := by
  change TraceCone.matrixPad h a = _
  induction l, h using Nat.le_induction with
  | base => simp only [TraceCone.matrixPad, Nat.leRecOn_self, corner_refl]
  | succ l h ih =>
    rw [TraceCone.matrixPad_succ h, ih, shared_matrixSuccessor_eq_corner, corner_comp]

lemma completedMatrixInclude_shared_compatible {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedMatrixInclude A l (TraceCone.matrixInclusion h a) = completedMatrixInclude A k a := by
  rw [shared_matrixInclusion_eq_corner, completedMatrixInclude_corner]

def sharedMatrixToCompletion : TraceCone.MatrixLimit A →⋆ₙₐ[ℂ] CornerCompletion A :=
  TraceCone.matrixLimitLift (completedMatrixInclude A) completedMatrixInclude_shared_compatible

@[simp] lemma sharedMatrixToCompletion_stage (k : ℕ) (a : MatrixStage A k) :
    sharedMatrixToCompletion (TraceCone.matrixLimitStage k a) = completedMatrixInclude A k a :=
  TraceCone.matrixLimitLift_stage _ _ k a

lemma sharedMatrixToCompletion_continuous : Continuous (sharedMatrixToCompletion (A := A)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
    NonUnitalStarAlgHom.norm_apply_le (sharedMatrixToCompletion (A := A)) (x-y)

lemma sharedMatrixToCompletion_norm (x : TraceCone.MatrixLimit A) :
    ‖sharedMatrixToCompletion x‖ = ‖x‖ := by
  refine TraceCone.finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · exact isClosed_eq (sharedMatrixToCompletion_continuous.norm) continuous_norm
  · intro y
    obtain ⟨k,a,rfl⟩ := TraceCone.finiteMatrixStage_surjective y
    change ‖sharedMatrixToCompletion (TraceCone.matrixLimitStage k a)‖ =
      ‖TraceCone.matrixLimitStage k a‖
    rw [sharedMatrixToCompletion_stage, completedMatrixInclude_norm, TraceCone.matrixLimitStage_norm]

lemma sharedMatrixToCompletion_isometry : Isometry (sharedMatrixToCompletion (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ sharedMatrixToCompletion_norm

lemma sharedMatrixToCompletion_surjective : Function.Surjective (sharedMatrixToCompletion (A := A)) := by
  intro x
  have hc : IsClosed (Set.range (sharedMatrixToCompletion (A := A))) :=
    (sharedMatrixToCompletion_isometry (A := A)).isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range (sharedMatrixToCompletion (A := A))) := by
    apply (completedMatrixInclude_dense A).mono
    rintro y hy
    obtain ⟨k,a,rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨TraceCone.matrixLimitStage k a, sharedMatrixToCompletion_stage k a⟩
  have hx := hd x
  rw [hc.closure_eq] at hx
  exact hx

def sharedMatrixEquiv : TraceCone.MatrixLimit A ≃⋆ₐ[ℂ] CornerCompletion A :=
  StarAlgEquiv.ofBijective sharedMatrixToCompletion
    ⟨sharedMatrixToCompletion_isometry.injective, sharedMatrixToCompletion_surjective⟩

end Pureness

open scoped ENNReal NNReal CStarAlgebra
namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
namespace Positive

def map (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) : Positive B :=
  ⟨f a.1, map_nonneg f a.2⟩

end Positive
end TraceCone
end

section
open scoped ENNReal NNReal CStarAlgebra
namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
namespace ExtendedTrace

def pullback (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) : ExtendedTrace A where
  toFun a := τ (Positive.map f a)
  map_zero := by
    have h : Positive.map f Positive.zero = Positive.zero := Subtype.ext (_root_.map_zero f)
    rw [h, τ.map_zero]
  map_add a b := by
    have h : Positive.map f (Positive.add a b) =
        Positive.add (Positive.map f a) (Positive.map f b) := Subtype.ext (_root_.map_add f _ _)
    rw [h, τ.map_add]
  map_smul r a := by
    have h : Positive.map f (Positive.smul r a) = Positive.smul r (Positive.map f a) := by
      apply Subtype.ext
      change f ((r : ℝ) • a.1) = (r : ℝ) • f a.1
      simpa only [← Complex.coe_smul] using _root_.map_smul f (r : ℂ) a.1
    rw [h, τ.map_smul]
  tracial x := by
    have h₁ : Positive.map f (Positive.starMul x) = Positive.starMul (f x) := by
      apply Subtype.ext
      simp [Positive.map, Positive.starMul, map_mul, map_star]
    have h₂ : Positive.map f (Positive.mulStar x) = Positive.mulStar (f x) := by
      apply Subtype.ext
      simp [Positive.map, Positive.mulStar, map_mul, map_star]
    rw [h₁, h₂, τ.tracial]
  lowerSemicontinuous := τ.lowerSemicontinuous.comp
    (((map_continuous f).comp continuous_subtype_val).subtype_mk _)

end ExtendedTrace
end TraceCone
end

section
open scoped NNReal ENNReal Topology
namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance : PartialOrder (MatrixLimit A) := CStarAlgebra.spectralOrder _

instance : StarOrderedRing (MatrixLimit A) := CStarAlgebra.spectralOrderedRing _

end TraceCone
end

namespace Pureness
open Filter Topology
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCornerCut_finite_range (k l : ℕ) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) ∈ Set.range (completedMatrixInclude A k) := by
  let m := max k l
  have hk : k ≤ m := le_max_left _ _
  have hl : l ≤ m := le_max_right _ _
  refine ⟨compress hk (corner hl a), ?_⟩
  rw [completedCornerCut, completedProjection, ← completedMatrixInclude_corner A hk 1,
    ← completedMatrixInclude_corner A hl a, ← map_mul, ← map_mul,
    ← cornerProjection_eq hk, ← corner_compress, completedMatrixInclude_corner]

theorem completedCornerCut_mem_range (k : ℕ) (a : CornerCompletion A) :
    completedCornerCut A k a ∈ Set.range (completedMatrixInclude A k) := by
  have hc : IsClosed {a : CornerCompletion A |
      completedCornerCut A k a ∈ Set.range (completedMatrixInclude A k)} :=
    (completedMatrixInclude_isometry A k).isClosedEmbedding.isClosed_range.preimage
      (completedCornerCut_continuous A k)
  apply hc.closure_subset_iff.mpr ?_ (completedMatrixInclude_dense A a)
  intro b hb
  obtain ⟨l, c, rfl⟩ := Set.mem_iUnion.mp hb
  exact completedCornerCut_finite_range A k l c

def completedCompress (k : ℕ) (a : CornerCompletion A) : MatrixStage A k :=
  Classical.choose (completedCornerCut_mem_range A k a)

@[simp] lemma include_completedCompress (k : ℕ) (a : CornerCompletion A) :
    completedMatrixInclude A k (completedCompress A k a) = completedCornerCut A k a :=
  Classical.choose_spec (completedCornerCut_mem_range A k a)

lemma completedCompress_continuous (k : ℕ) : Continuous (completedCompress A k) := by
  apply (completedMatrixInclude_isometry A k).isEmbedding.isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, include_completedCompress] using completedCornerCut_continuous A k

@[simp] lemma completedCompress_include (k : ℕ) (a : MatrixStage A k) :
    completedCompress A k (completedMatrixInclude A k a) = a := by
  apply (completedMatrixInclude_isometry A k).injective
  rw [include_completedCompress, completedCornerCut_fixes A le_rfl]

end Pureness

namespace Pureness
open scoped ComplexOrder
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem nonUnitalStarAlgHom_nonneg_iff (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) (a : A) :
    0 ≤ φ a ↔ 0 ≤ a := by
  constructor
  · intro ha
    let s : NonUnitalStarSubalgebra ℂ B := NonUnitalStarAlgHom.range φ
    have hs : IsClosed (s : Set B) := (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
    let : IsClosed (s : Set B) := hs
    have hm : CFC.sqrt (φ a) ∈ s := by
      rw [CFC.sqrt_eq_nnrpow, CFC.nnrpow_eq_cfcₙ_real _ _ ha]
      exact cfcₙ_mem (𝕜' := ℂ) _ (NonUnitalStarAlgHom.mem_range_self φ a)
    obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range φ).mp hm
    have he : star x * x = a := hφ (by
      rw [map_mul, map_star, hx, (CFC.sqrt_nonneg (φ a)).star_eq, CFC.sqrt_mul_sqrt_self (φ a) ha])
    rw [← he]
    exact star_mul_self_nonneg _
  · intro ha
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he, map_mul, map_star]
    exact star_mul_self_nonneg _

end Pureness

namespace Pureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

lemma matrixTrace_compress_le (τ : TracialState A) (h : k ≤ l) (a : MatrixStage A l) (ha : 0 ≤ a) :
    matrixTrace τ (compress h a) ≤ matrixTrace τ a := by
  rw [← matrixTrace_corner τ h, matrixTrace_apply, matrixTrace_apply]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k
  · simp [corner, compress, hi]
  · simp only [corner_row_zero h _ i i hi, map_zero]
    exact τ.functional.map_nonneg (matrix_entry_nonneg a ha i)

lemma completedCompress_nonneg (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    0 ≤ completedCompress A k a := by
  apply (nonUnitalStarAlgHom_nonneg_iff (completedMatrixInclude A k)
    (completedMatrixInclude_isometry A k).injective _).mp
  rw [include_completedCompress]
  exact completedCornerCut_nonneg A k a ha

lemma completedProjection_mul_le (h : k ≤ l) :
    completedProjection A k * completedProjection A l = completedProjection A k := by
  change completedMatrixInclude A k 1 * completedMatrixInclude A l 1 = _
  rw [← completedMatrixInclude_corner A h 1, ← map_mul, mul_one, completedMatrixInclude_corner]
  rfl

lemma completedProjection_mul_ge (h : k ≤ l) :
    completedProjection A l * completedProjection A k = completedProjection A k := by
  change completedMatrixInclude A l 1 * completedMatrixInclude A k 1 = _
  rw [← completedMatrixInclude_corner A h 1, ← map_mul, one_mul, completedMatrixInclude_corner]
  rfl

lemma completedCornerCut_nested (h : k ≤ l) (a : CornerCompletion A) :
    completedCornerCut A k (completedCornerCut A l a) = completedCornerCut A k a := by
  dsimp [completedCornerCut]
  calc
    _ = (completedProjection A k * completedProjection A l) * a *
        (completedProjection A l * completedProjection A k) := by simp only [mul_assoc]
    _ = _ := by rw [completedProjection_mul_le h, completedProjection_mul_ge h]

lemma completedCornerCut_include (h : k ≤ l) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) = completedMatrixInclude A k (compress h a) := by
  rw [completedCornerCut, completedProjection, ← completedMatrixInclude_corner A h 1,
    ← map_mul, ← map_mul, ← cornerProjection_eq h, ← corner_compress, completedMatrixInclude_corner]

theorem completedCompress_compat (h : k ≤ l) (a : CornerCompletion A) :
    compress h (completedCompress A l a) = completedCompress A k a := by
  apply (completedMatrixInclude_isometry A k).injective
  rw [← completedCornerCut_include, include_completedCompress, completedCornerCut_nested h,
    include_completedCompress]

lemma completedCompression_trace_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k : ℕ => matrixTrace τ (completedCompress A k a)) := by
  intro k l h
  dsimp only
  rw [← completedCompress_compat h a]
  exact matrixTrace_compress_le τ h _ (completedCompress_nonneg l a ha)

end Pureness

namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCornerCut_add (k : ℕ) (a b : CornerCompletion A) :
    completedCornerCut A k (a + b) = completedCornerCut A k a + completedCornerCut A k b := by
  simp only [completedCornerCut, mul_add, add_mul]

lemma completedCornerCut_smul (k : ℕ) (z : ℂ) (a : CornerCompletion A) :
    completedCornerCut A k (z • a) = z • completedCornerCut A k a := by
  simp only [completedCornerCut, mul_smul_comm, smul_mul_assoc]

def completedCompressLinear (k : ℕ) : CornerCompletion A →ₗ[ℂ] MatrixStage A k where
  toFun := completedCompress A k
  map_add' a b := by
    apply (completedMatrixInclude_isometry A k).injective
    rw [include_completedCompress, map_add, include_completedCompress, include_completedCompress,
      completedCornerCut_add]
  map_smul' z a := by
    apply (completedMatrixInclude_isometry A k).injective
    simp only [map_smul, include_completedCompress, completedCornerCut_smul]
    rfl

lemma completedCompress_mono (k : ℕ) : Monotone (completedCompress A k) := by
  intro a b hab
  apply sub_nonneg.mp
  change 0 ≤ completedCompressLinear k b - completedCompressLinear k a
  rw [← map_sub]
  exact completedCompress_nonneg k (b - a) (sub_nonneg.mpr hab)

lemma completedCompress_include_of_le {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedCompress A l (completedMatrixInclude A k a) = corner h a := by
  apply (completedMatrixInclude_isometry A l).injective
  rw [include_completedCompress, completedCornerCut_fixes A h, completedMatrixInclude_corner]

def completedTraceValue (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixTrace τ (completedCompress A k a)).re

def completedDiagonalWeight (τ : TracialState A) (a : CornerCompletion A) : ℝ≥0∞ :=
  ⨆ k : ℕ, completedTraceValue τ k a

lemma completedTraceValue_continuous (τ : TracialState A) (k : ℕ) :
    Continuous (completedTraceValue τ k) :=
  ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    ((map_continuous (matrixTrace τ)).comp (completedCompress_continuous A k)))

lemma completedTraceValue_mono (τ : TracialState A) (k : ℕ) : Monotone (completedTraceValue τ k) := by
  intro a b hab
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp ((matrixTrace τ).monotone (completedCompress_mono k hab))).1

lemma completedTraceValue_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k => completedTraceValue τ k a) := by
  intro k l h
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp (completedCompression_trace_monotone τ a ha h)).1

lemma completedDiagonalWeight_tendsto (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => completedTraceValue τ k a) atTop (𝓝 (completedDiagonalWeight τ a)) :=
  tendsto_atTop_iSup (completedTraceValue_monotone τ a ha)

lemma completedDiagonalWeight_mono (τ : TracialState A) : Monotone (completedDiagonalWeight τ) := by
  intro a b hab
  exact iSup_mono fun k => completedTraceValue_mono τ k hab

lemma completedTraceValue_add (τ : TracialState A) (k : ℕ) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    completedTraceValue τ k (a + b) = completedTraceValue τ k a + completedTraceValue τ k b := by
  have hca : 0 ≤ (matrixTrace τ (completedCompress A k a)).re :=
    (Complex.nonneg_iff.mp ((matrixTrace τ).map_nonneg (completedCompress_nonneg k a ha))).1
  have hcb : 0 ≤ (matrixTrace τ (completedCompress A k b)).re :=
    (Complex.nonneg_iff.mp ((matrixTrace τ).map_nonneg (completedCompress_nonneg k b hb))).1
  change ENNReal.ofReal (matrixTrace τ (completedCompressLinear k (a + b))).re = _
  rw [map_add, map_add, Complex.add_re]
  exact ENNReal.ofReal_add hca hcb

theorem completedDiagonalWeight_add (τ : TracialState A) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    completedDiagonalWeight τ (a + b) = completedDiagonalWeight τ a + completedDiagonalWeight τ b := by
  apply tendsto_nhds_unique (completedDiagonalWeight_tendsto τ (a + b) (add_nonneg ha hb))
  convert (completedDiagonalWeight_tendsto τ a ha).add (completedDiagonalWeight_tendsto τ b hb) using 1
  funext k
  exact completedTraceValue_add τ k a b ha hb

theorem completedDiagonalWeight_include (τ : TracialState A) (l : ℕ) (a : MatrixStage A l) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedMatrixInclude A l a) = ENNReal.ofReal (matrixTrace τ a).re := by
  apply le_antisymm
  · apply iSup_le
    intro k
    have hmono := completedTraceValue_monotone τ (completedMatrixInclude A l a)
      (completedMatrixInclude_nonneg A l a ha) (le_max_left k l)
    refine hmono.trans_eq ?_
    unfold completedTraceValue
    dsimp only
    rw [completedCompress_include_of_le (le_max_right k l), matrixTrace_corner]
  · have ht := le_iSup (fun k => completedTraceValue τ k (completedMatrixInclude A l a)) l
    simpa only [completedDiagonalWeight, completedTraceValue, completedCompress_include] using ht

theorem completedDiagonalWeight_le_of_tendsto (τ : TracialState A) {a : ℕ → CornerCompletion A}
    {b : CornerCompletion A} {r : ℝ≥0∞} (ht : Tendsto a atTop (𝓝 b))
    (hr : ∀ n, completedDiagonalWeight τ (a n) ≤ r) : completedDiagonalWeight τ b ≤ r := by
  apply iSup_le
  intro k
  apply le_of_tendsto ((completedTraceValue_continuous τ k).continuousAt.tendsto.comp ht)
  exact Eventually.of_forall fun n => (le_iSup (fun k => completedTraceValue τ k (a n)) k).trans (hr n)

lemma completedDiagonalWeight_cut (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedCornerCut A k a) = completedTraceValue τ k a := by
  rw [← include_completedCompress, completedDiagonalWeight_include τ k _ (completedCompress_nonneg k a ha)]
  rfl

lemma completedDiagonalWeight_cut_le (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedCornerCut A k a) ≤ completedDiagonalWeight τ a := by
  rw [completedDiagonalWeight_cut τ k a ha]
  exact le_iSup (fun k => completedTraceValue τ k a) k

lemma completedProjection_conjugate_le (k : ℕ) (x : CornerCompletion A) :
    x * completedProjection A k * star x ≤ x * star x := by
  have hq := completedProjection_mul_le (A := A) (k := k) le_rfl
  have he : (x - x * completedProjection A k) * star (x - x * completedProjection A k) =
      x * star x - x * completedProjection A k * star x := by
    simp only [star_sub, star_mul, completedProjection_star, sub_mul, mul_sub, mul_assoc]
    rw [← mul_assoc (completedProjection A k) (completedProjection A k), hq]
    noncomm_ring
  exact sub_nonneg.mp (he ▸ mul_star_self_nonneg (x - x * completedProjection A k))

lemma completedCornerCut_mono (k : ℕ) : Monotone (completedCornerCut A k) := by
  intro a b hab
  simpa only [completedCornerCut, completedProjection_star] using
    star_left_conjugate_le_conjugate hab (completedProjection A k)

lemma completedCornerCut_mul_star_le (k : ℕ) (x : CornerCompletion A) :
    completedCornerCut A k x * star (completedCornerCut A k x) ≤
      completedCornerCut A k (x * star x) := by
  have he : completedCornerCut A k x * star (completedCornerCut A k x) =
      completedCornerCut A k (x * completedProjection A k * star x) := by
    simp only [completedCornerCut, star_mul, completedProjection_star, mul_assoc]
    rw [← mul_assoc (completedProjection A k) (completedProjection A k), completedProjection_mul_le le_rfl]
  rw [he]
  exact completedCornerCut_mono k (completedProjection_conjugate_le k x)

lemma completedDiagonalWeight_finite_polar (τ : TracialState A) (k : ℕ) (x : MatrixStage A k) :
    completedDiagonalWeight τ (star (completedMatrixInclude A k x) * completedMatrixInclude A k x) =
      completedDiagonalWeight τ (completedMatrixInclude A k x * star (completedMatrixInclude A k x)) := by
  rw [← map_star, ← map_mul, ← map_mul,
    completedDiagonalWeight_include τ k _ (star_mul_self_nonneg _),
    completedDiagonalWeight_include τ k _ (mul_star_self_nonneg _), matrixTrace_tracial]

lemma completedDiagonalWeight_star_mul_le (τ : TracialState A) (x : CornerCompletion A) :
    completedDiagonalWeight τ (star x * x) ≤ completedDiagonalWeight τ (x * star x) := by
  have ht := completedCornerCut_tendsto A x
  apply completedDiagonalWeight_le_of_tendsto τ (ht.star.mul ht)
  intro k
  rw [← include_completedCompress, completedDiagonalWeight_finite_polar, include_completedCompress]
  exact (completedDiagonalWeight_mono τ (completedCornerCut_mul_star_le k x)).trans
    (completedDiagonalWeight_cut_le τ k (x * star x) (mul_star_self_nonneg x))

theorem completedDiagonalWeight_tracial (τ : TracialState A) (x : CornerCompletion A) :
    completedDiagonalWeight τ (star x * x) = completedDiagonalWeight τ (x * star x) := by
  apply le_antisymm (completedDiagonalWeight_star_mul_le τ x)
  simpa only [star_star] using completedDiagonalWeight_star_mul_le τ (star x)

end Pureness

namespace Pureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedTraceValue_smul (τ : TracialState A) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) (a : CornerCompletion A) :
    completedTraceValue τ k (s • a) = ENNReal.ofReal s * completedTraceValue τ k a := by
  change ENNReal.ofReal (matrixTrace τ (completedCompressLinear k (s • a))).re = _
  rw [(completedCompressLinear (A := A) k).map_smul_of_tower, (matrixTrace τ).map_smul_of_tower,
    Complex.smul_re, smul_eq_mul, ENNReal.ofReal_mul hs]
  rfl

lemma completedDiagonalWeight_smul (τ : TracialState A) (s : ℝ) (hs : 0 ≤ s) (a : CornerCompletion A) :
    completedDiagonalWeight τ (s • a) = ENNReal.ofReal s * completedDiagonalWeight τ a := by
  simp only [completedDiagonalWeight, completedTraceValue_smul τ _ s hs, ENNReal.mul_iSup]

@[simp] lemma completedDiagonalWeight_zero (τ : TracialState A) : completedDiagonalWeight τ 0 = 0 := by
  have h := completedDiagonalWeight_smul τ 0 le_rfl (0 : CornerCompletion A)
  simpa only [zero_smul, ENNReal.ofReal_zero, zero_mul] using h

end Pureness

namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

noncomputable def nonUnitalNormalize (a : A) : A := ‖a‖⁻¹ • a

noncomputable def nonUnitalRoot (a : A) (j : ℕ) : A :=
  CFC.nnrpow (nonUnitalNormalize a) (((j : ℝ≥0) + 1)⁻¹)

end Pureness

namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedRootRank (τ : TracialState A) (a : CornerCompletion A) : ℝ≥0∞ :=
  ⨆ n : ℕ, completedDiagonalWeight τ (nonUnitalRoot a n)

end Pureness

namespace Pureness
namespace CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

abbrev normedRing (p : CStarAlgebraNorm R) : NormedRing R :=
  p.toAlgebraNorm.toRingNorm.toNormedRing

@[instance_reducible] def normedAlgebra (p : CStarAlgebraNorm R) :
    letI := p.normedRing
    NormedAlgebra ℂ R := by
  letI := p.normedRing
  exact ⟨fun c x => (p.toAlgebraNorm.smul' c x).le⟩

theorem cstarRing (p : CStarAlgebraNorm R) :
    letI := p.normedRing
    CStarRing R := by
  let := p.normedRing
  exact ⟨fun x => (p.cstar x).ge⟩

end CStarAlgebraNorm
end Pureness

namespace DirectComparison
open Pureness CurrentMain Filter
open scoped Topology ComplexOrder

def StrictComparison (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ (a b : CornerCompletion A), 0 ≤ a → 0 ≤ b → b ≠ 0 →
    (∀ τ : TracialState A, completedRootRank τ a < completedRootRank τ b) → CuntzSubequiv a b

def UniformGamma (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ p : Fin m → FamilyUltrapower (fun t : TracialState A => t) U,
    (∀ i, IsStarProjection (p i)) ∧ (∑ i, p i)=1 ∧
    (∀ i (a : A), Commute (p i) (familyUltrapowerMap (fun t : TracialState A => t) U a)) ∧
    ∀ i (a : A) (s : ℕ → TracialState A),
      (familyLimitTrace (fun t : TracialState A => t) U s).functional
          (familyUltrapowerMap (fun t : TracialState A => t) U a*p i) =
        (1/(m:ℂ))*(familyLimitTrace (fun t : TracialState A => t) U s).functional
          (familyUltrapowerMap (fun t : TracialState A => t) U a)

end DirectComparison

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

class TraceFamily (D : Type*) [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] where
  carrier : Set (TracialState D)

abbrev RestrictedTracialState (D : Type*) [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] [TraceFamily D] := {τ : TracialState D // τ ∈ TraceFamily.carrier (D := D)}

end DirectPacking

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder
namespace RestrictedTracialState
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

abbrev functional (τ : RestrictedTracialState D) := τ.val.functional

lemma normalized (τ : RestrictedTracialState D) : τ.functional 1=1 := τ.val.normalized

lemma tracial (τ : RestrictedTracialState D) (a b : D) : τ.functional (a*b)=τ.functional (b*a) :=
  τ.val.tracial a b

end RestrictedTracialState
end DirectPacking

namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveFunctionalCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ :=
  ⟨f.toLinearMap,map_continuous f⟩

structure NormalizedTrace (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  functional : A →ₚ[ℂ] ℂ
  norm_one : ‖positiveFunctionalCLM functional‖ = 1
  tracial : ∀ a b : A, functional (a*b)=functional (b*a)

lemma positiveFunctional_cauchy_schwarz (f : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖f (star a*b)‖ ≤ Real.sqrt (f (star a*a)).re * Real.sqrt (f (star b*b)).re := by
  simpa only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS] using
    norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS a) (f.toPreGNS b)

lemma positiveFunctional_norm_le_sqrt (f : A →ₚ[ℂ] ℂ)
    (hf : ‖positiveFunctionalCLM f‖ ≤ 1) (a : A) :
    ‖f a‖ ≤ Real.sqrt (f (star a*a)).re := by
  have hu := CStarAlgebra.increasingApproximateUnit A
  have ht : Tendsto (fun e : A => ‖f (e*a)‖) (CStarAlgebra.approximateUnit A) (𝓝 ‖f a‖) :=
    (map_continuous f).norm.tendsto a |>.comp (hu.tendsto_mul_right a)
  apply le_of_tendsto ht
  filter_upwards [hu.eventually_nonneg,hu.eventually_norm] with e he hen
  have hfe : (f (star e*e)).re ≤ 1 := by
    have h := (positiveFunctionalCLM f).le_opNorm (star e*e)
    have hn : ‖star e*e‖ ≤ 1 := (norm_mul_le _ _).trans (by simpa using mul_le_mul hen hen (norm_nonneg _) zero_le_one)
    exact (Complex.re_le_norm _).trans (h.trans (by nlinarith [norm_nonneg (positiveFunctionalCLM f),norm_nonneg (star e*e)]))
  have hs : Real.sqrt (f (star e*e)).re ≤ 1 := by
    exact (Real.sqrt_le_iff).mpr ⟨zero_le_one,by simpa using hfe⟩
  calc
    ‖f (e*a)‖ = ‖f (star e*a)‖ := by rw [he.isSelfAdjoint.star_eq]
    _ ≤ Real.sqrt (f (star e*e)).re * Real.sqrt (f (star a*a)).re := positiveFunctional_cauchy_schwarz f e a
    _ ≤ Real.sqrt (f (star a*a)).re := by nlinarith [Real.sqrt_nonneg (f (star a*a)).re]

lemma positiveFunctional_norm_sq_le (f : A →ₚ[ℂ] ℂ)
    (hf : ‖positiveFunctionalCLM f‖ ≤ 1) (a : A) :
    ‖f a‖^2 ≤ (f (star a*a)).re := by
  have h := positiveFunctional_norm_le_sqrt f hf a
  have hpos : 0 ≤ (f (star a*a)).re := (f.map_nonneg (star_mul_self_nonneg a)).1
  nlinarith [Real.sq_sqrt hpos, norm_nonneg (f a), Real.sqrt_nonneg (f (star a*a)).re]

def unitizedFunctionalLinear (f : A →ₚ[ℂ] ℂ) : Unitization ℂ A →ₗ[ℂ] ℂ where
  toFun x := x.fst + f x.snd
  map_add' x y := by simp only [Unitization.fst_add,Unitization.snd_add,map_add]; ring
  map_smul' z x := by simp only [Unitization.fst_smul,Unitization.snd_smul,map_smul,smul_eq_mul,RingHom.id_apply]; ring

lemma unitizedFunctional_star_square (f : A →ₚ[ℂ] ℂ)
    (hf : ‖positiveFunctionalCLM f‖ ≤ 1) (x : Unitization ℂ A) :
    0 ≤ unitizedFunctionalLinear f (star x*x) := by
  have ha := positiveFunctional_norm_sq_le f hf x.snd
  have hp := f.map_nonneg (star_mul_self_nonneg x.snd)
  have hi : (f (star x.snd*x.snd)).im=0 := (Complex.nonneg_iff.mp hp).2.symm
  change 0 ≤ (star x*x).fst + f (star x*x).snd
  simp only [Unitization.fst_mul, Unitization.fst_star,Unitization.snd_mul,
    Unitization.snd_star,map_add,map_smul,map_star,smul_eq_mul]
  apply Complex.nonneg_iff.mpr
  constructor
  · have hn := Complex.normSq_nonneg (x.fst+f x.snd)
    rw [Complex.normSq_eq_norm_sq] at hn
    have hn' : 0 ≤ Complex.normSq (x.fst+f x.snd) := Complex.normSq_nonneg _
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im] at hn'
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at ha
    simp only [Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
    nlinarith
  · simp only [Complex.add_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,hi]
    ring

def unitizedFunctional (f : A →ₚ[ℂ] ℂ) (hf : ‖positiveFunctionalCLM f‖ ≤ 1) :
    Unitization ℂ A →ₚ[ℂ] ℂ where
  toLinearMap := unitizedFunctionalLinear f
  monotone' := by
    intro x y hxy
    have h := (CStarAlgebra.nonneg_iff_eq_star_mul_self).mp (sub_nonneg.mpr hxy)
    obtain ⟨z,hz⟩ := h
    have hp := unitizedFunctional_star_square f hf z
    rw [←hz,map_sub,sub_nonneg] at hp
    exact hp

@[simp] lemma unitizedFunctional_one (f : A →ₚ[ℂ] ℂ)
    (hf : ‖positiveFunctionalCLM f‖ ≤ 1) : unitizedFunctional f hf 1=1 := by
  change 1+f 0=1
  simp only [map_zero,add_zero]

lemma unitizedFunctional_tracial (τ : NormalizedTrace A) (x y : Unitization ℂ A) :
    unitizedFunctional τ.functional τ.norm_one.le (x*y)=
      unitizedFunctional τ.functional τ.norm_one.le (y*x) := by
  change (x*y).fst+τ.functional (x*y).snd=(y*x).fst+τ.functional (y*x).snd
  simp only [Unitization.fst_mul,Unitization.snd_mul,map_add,map_smul,smul_eq_mul]
  rw [τ.tracial x.snd y.snd]
  ring

end NonunitalGamma

namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def NormalizedTrace.toWeakDual (τ : NormalizedTrace A) : WeakDual ℂ A :=
  StrongDual.toWeakDual (positiveFunctionalCLM τ.functional)

instance : TopologicalSpace (NormalizedTrace A) :=
  TopologicalSpace.induced NormalizedTrace.toWeakDual inferInstance

end NonunitalGamma

namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def NormalizedTrace.unitized (τ : NormalizedTrace A) : TracialState (Unitization ℂ A) where
  functional := unitizedFunctional τ.functional τ.norm_one.le
  normalized := unitizedFunctional_one _ _
  tracial := unitizedFunctional_tracial τ

end NonunitalGamma

namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder ComplexStarModule
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def WeightBounded (τ : ExtendedTrace A) : Prop :=
  ∃ C : ℝ≥0, ∀ a : Positive A, ‖a.1‖ ≤ 1 → τ a ≤ (C : ℝ≥0∞)

def WeightDenselyFinite (τ : ExtendedTrace A) : Prop :=
  Dense {a : Positive A | τ a < ∞}

lemma weightBounded_finite {τ : ExtendedTrace A} (hτ : WeightBounded τ) (a : Positive A) :
    τ a ≠ ∞ := by
  obtain ⟨C,hC⟩ := hτ
  let r : ℝ≥0 := ‖a.1‖₊+1
  have hr : r ≠ 0 := ne_of_gt (by dsimp [r]; positivity)
  have he : Positive.smul r (Positive.smul r⁻¹ a)=a := by
    apply Subtype.ext
    change (r:ℝ) • ((r⁻¹:ℝ≥0):ℝ) • a.1=a.1
    rw [NNReal.coe_inv,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hr),one_smul]
  have hn : ‖(Positive.smul r⁻¹ a).1‖ ≤ 1 := by
    change ‖((r⁻¹:ℝ≥0):ℝ) • a.1‖ ≤ 1
    rw [norm_smul,NNReal.coe_inv,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply (inv_mul_le_iff₀ (by exact_mod_cast (pos_iff_ne_zero.mpr hr))).mpr
    dsimp [r]
    linarith
  have hf : τ (Positive.smul r⁻¹ a) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hC _ hn)
  rw [←he,τ.map_smul]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hf

end NonunitalGamma

namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder ComplexStarModule
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace ExtendedTraceExtension
variable (τ : ExtendedTrace A) (hfinite : ∀ a, τ a ≠ ∞)

def value (a : Positive A) : ℝ := (τ a).toReal

lemma value_nonneg (a : Positive A) : 0 ≤ value τ a := ENNReal.toReal_nonneg

lemma value_zero : value τ Positive.zero=0 := by simp [value,τ.map_zero]

include hfinite in
lemma value_add (a b : Positive A) : value τ (Positive.add a b)=value τ a+value τ b := by
  exact (congrArg ENNReal.toReal (τ.map_add a b)).trans (ENNReal.toReal_add (hfinite a) (hfinite b))

lemma value_smul (r : ℝ≥0) (a : Positive A) :
    value τ (Positive.smul r a)=(r:ℝ)*value τ a := by
  simp only [value,τ.map_smul,ENNReal.toReal_mul,ENNReal.coe_toReal]

def selfAdjointValue (a : selfAdjoint A) : ℝ :=
  value τ ⟨a.1⁺,CFC.posPart_nonneg _⟩-value τ ⟨a.1⁻,CFC.negPart_nonneg _⟩

include hfinite in
lemma selfAdjointValue_sub (a : selfAdjoint A) (p q : Positive A)
    (hpq : a.1=p.1-q.1) : selfAdjointValue τ a=value τ p-value τ q := by
  have hb : Positive.add ⟨a.1⁺,CFC.posPart_nonneg _⟩ q=
      Positive.add p ⟨a.1⁻,CFC.negPart_nonneg _⟩ := by
    apply Subtype.ext
    exact sub_eq_sub_iff_add_eq_add.mp ((CFC.posPart_sub_negPart a.1 a.2).trans hpq)
  have hv := congrArg (value τ) hb
  rw [value_add τ hfinite,value_add τ hfinite] at hv
  unfold selfAdjointValue
  linarith

include hfinite in
lemma selfAdjointValue_add (a b : selfAdjoint A) :
    selfAdjointValue τ (a+b)=selfAdjointValue τ a+selfAdjointValue τ b := by
  let p := Positive.add (⟨a.1⁺,CFC.posPart_nonneg _⟩ : Positive A) ⟨b.1⁺,CFC.posPart_nonneg _⟩
  let q := Positive.add (⟨a.1⁻,CFC.negPart_nonneg _⟩ : Positive A) ⟨b.1⁻,CFC.negPart_nonneg _⟩
  have hrep : (a+b).1=p.1-q.1 := by
    change a.1+b.1=(a.1⁺+b.1⁺)-(a.1⁻+b.1⁻)
    rw [add_sub_add_comm,CFC.posPart_sub_negPart _ a.2,CFC.posPart_sub_negPart _ b.2]
  rw [selfAdjointValue_sub τ hfinite (a+b) p q hrep]
  dsimp [p,q]
  rw [value_add τ hfinite,value_add τ hfinite]
  unfold selfAdjointValue
  ring

include hfinite in
lemma selfAdjointValue_smul_nonneg (r : ℝ≥0) (a : selfAdjoint A) :
    selfAdjointValue τ ((r:ℝ) • a)=(r:ℝ)*selfAdjointValue τ a := by
  rw [selfAdjointValue_sub τ hfinite ((r:ℝ) • a)
    (Positive.smul r ⟨a.1⁺,CFC.posPart_nonneg _⟩)
    (Positive.smul r ⟨a.1⁻,CFC.negPart_nonneg _⟩) (by
      change (r:ℝ) • a.1=(r:ℝ) • a.1⁺-(r:ℝ) • a.1⁻
      rw [←smul_sub,CFC.posPart_sub_negPart _ a.2])]
  rw [value_smul,value_smul]
  unfold selfAdjointValue
  ring

lemma selfAdjointValue_neg (a : selfAdjoint A) : selfAdjointValue τ (-a) = -selfAdjointValue τ a := by
  unfold selfAdjointValue
  change value τ ⟨(-a.1)⁺,_⟩-value τ ⟨(-a.1)⁻,_⟩ = -(value τ ⟨a.1⁺,_⟩-value τ ⟨a.1⁻,_⟩)
  simp only [CFC.posPart_neg,CFC.negPart_neg]
  ring

include hfinite in
lemma selfAdjointValue_smul (r : ℝ) (a : selfAdjoint A) :
    selfAdjointValue τ (r • a)=r*selfAdjointValue τ a := by
  by_cases hr : 0 ≤ r
  · exact selfAdjointValue_smul_nonneg τ hfinite ⟨r,hr⟩ a
  · have he := selfAdjointValue_smul_nonneg τ hfinite ⟨-r,by linarith⟩ a
    change selfAdjointValue τ ((-r) • a)=(-r)*selfAdjointValue τ a at he
    rw [neg_smul,selfAdjointValue_neg] at he
    linarith

include hfinite in
lemma selfAdjointValue_positive (a : Positive A) :
    selfAdjointValue τ ⟨a.1,a.2.isSelfAdjoint⟩=value τ a := by
  have he := selfAdjointValue_sub τ hfinite ⟨a.1,a.2.isSelfAdjoint⟩ a Positive.zero
    (by simp [Positive.zero])
  simpa only [value_zero,sub_zero] using he

def realLinear : selfAdjoint A →ₗ[ℝ] ℝ where
  toFun := selfAdjointValue τ
  map_add' := selfAdjointValue_add τ hfinite
  map_smul' r a := selfAdjointValue_smul τ hfinite r a

def complexLinear : A →ₗ[ℂ] ℂ where
  toFun x := (realLinear τ hfinite (ℜ x):ℂ)+Complex.I*(realLinear τ hfinite (ℑ x):ℂ)
  map_add' x y := by simp only [map_add,Complex.ofReal_add];ring
  map_smul' z x := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,_root_.map_smul,
      RingHom.id_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
    apply Complex.ext <;> simp

lemma complexLinear_positive (a : Positive A) : complexLinear τ hfinite a.1=(value τ a:ℂ) := by
  change (realLinear τ hfinite (ℜ a.1):ℂ)+Complex.I*(realLinear τ hfinite (ℑ a.1):ℂ)=_
  rw [a.2.isSelfAdjoint.imaginaryPart,map_zero,Complex.ofReal_zero,mul_zero,add_zero]
  congr 1
  change selfAdjointValue τ (ℜ a.1)=value τ a
  rw [show ℜ a.1=⟨a.1,a.2.isSelfAdjoint⟩ from Subtype.ext a.2.isSelfAdjoint.coe_realPart]
  exact selfAdjointValue_positive τ hfinite a

def functional : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (complexLinear τ hfinite) (by
  intro a ha
  rw [complexLinear_positive τ hfinite ⟨a,ha⟩]
  exact_mod_cast value_nonneg τ ⟨a,ha⟩)

@[simp] lemma functional_positive (a : Positive A) :
    functional τ hfinite a.1=(τ a).toReal := complexLinear_positive τ hfinite a

omit [PartialOrder A] [StarOrderedRing A] in
lemma linearMap_tracial_of_star_mul (f : A →ₗ[ℂ] ℂ)
    (h : ∀ a : A, f (star a*a)=f (a*star a)) : ∀ a b : A, f (a*b)=f (b*a) := by
  intro a b
  have h₁ := h (star a+b)
  have h₂ := h (star a+Complex.I • b)
  simp only [star_add,star_star,add_mul,mul_add,map_add] at h₁
  simp only [star_add,star_star,star_smul,Complex.star_def,Complex.conj_I,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,map_add,map_smul] at h₂
  simp only [smul_eq_mul] at h₂
  have ha := h (star a)
  have hb := h b
  simp only [star_star] at ha
  linear_combination (norm := ring_nf) (h₁-ha-hb-Complex.I*(h₂-ha-hb))/2
  simp [Complex.I_sq]

lemma functional_tracial (a b : A) : functional τ hfinite (a*b)=functional τ hfinite (b*a) := by
  apply linearMap_tracial_of_star_mul (complexLinear τ hfinite) _ a b
  intro x
  exact (complexLinear_positive τ hfinite (Positive.starMul x)).trans
    ((congrArg (fun r : ℝ≥0∞ => (r.toReal:ℂ)) (τ.tracial x)).trans
      (complexLinear_positive τ hfinite (Positive.mulStar x)).symm)

end ExtendedTraceExtension
end NonunitalGamma

namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder ComplexStarModule
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def boundedWeightFunctional (τ : ExtendedTrace A) (hτ : WeightBounded τ) : A →ₚ[ℂ] ℂ :=
  ExtendedTraceExtension.functional τ (weightBounded_finite hτ)

lemma boundedWeightFunctional_tracial (τ : ExtendedTrace A) (hτ : WeightBounded τ) (a b : A) :
    boundedWeightFunctional τ hτ (a*b)=boundedWeightFunctional τ hτ (b*a) :=
  ExtendedTraceExtension.functional_tracial τ (weightBounded_finite hτ) a b

end NonunitalGamma

namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def scaleFunctional (r : ℝ≥0) (f : A →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ ((r:ℂ) • f.toLinearMap) (by
    intro a ha
    change 0 ≤ (r:ℂ)*f a
    exact mul_nonneg (by exact_mod_cast r.2) (f.map_nonneg ha))

@[simp] lemma scaleFunctional_apply (r : ℝ≥0) (f : A →ₚ[ℂ] ℂ) (a : A) :
    scaleFunctional r f a=(r:ℂ)*f a := rfl

lemma positiveFunctionalCLM_scale (r : ℝ≥0) (f : A →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (scaleFunctional r f)=(r:ℂ) • positiveFunctionalCLM f := by
  ext a
  rfl

lemma scaleFunctional_norm (r : ℝ≥0) (f : A →ₚ[ℂ] ℂ) :
    ‖positiveFunctionalCLM (scaleFunctional r f)‖=(r:ℝ)*‖positiveFunctionalCLM f‖ := by
  rw [positiveFunctionalCLM_scale,norm_smul]
  congr 1
  exact_mod_cast (show ‖(r:ℝ)‖=(r:ℝ) from Real.norm_of_nonneg r.2)

lemma boundedWeightFunctional_nonzero {τ : ExtendedTrace A} (hτ : WeightBounded τ) (hne : τ ≠ 0) :
    positiveFunctionalCLM (boundedWeightFunctional τ hτ) ≠ 0 := by
  intro hz
  apply hne
  apply ExtendedTrace.ext
  intro a
  have he := congrArg (fun f : A →L[ℂ] ℂ => f a.1) hz
  change boundedWeightFunctional τ hτ a.1=0 at he
  rw [show boundedWeightFunctional τ hτ a.1=((τ a).toReal:ℂ) from
    ExtendedTraceExtension.functional_positive τ (weightBounded_finite hτ) a] at he
  have hr : (τ a).toReal=0 := by exact_mod_cast he
  exact (ENNReal.toReal_eq_zero_iff (τ a)).mp hr |>.resolve_right (weightBounded_finite hτ a)

def normalizedWeight (τ : ExtendedTrace A) (hτ : WeightBounded τ) (hne : τ ≠ 0) : NormalizedTrace A where
  functional := scaleFunctional (‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖₊⁻¹) (boundedWeightFunctional τ hτ)
  norm_one := by
    rw [scaleFunctional_norm,NNReal.coe_inv,coe_nnnorm,inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (boundedWeightFunctional_nonzero hτ hne)
  tracial a b := by
    simp only [scaleFunctional_apply,boundedWeightFunctional_tracial τ hτ a b]

end NonunitalGamma

namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def TopologicallySimple (A : Type*) [NonUnitalNormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I=⊥ ∨ I=⊤

end NonunitalGamma

namespace NonunitalGamma
open Filter Topology
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open ComplexStarModule
open scoped ComplexOrder CStarAlgebra

def Projectionless (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ p : A, IsStarProjection p → p=0

end NonunitalGamma

section
open scoped CStarAlgebra
namespace Pureness
open Filter Topology TraceCone
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedExtendedTrace (τ : TracialState A) : ExtendedTrace (CornerCompletion A) where
  toFun a := completedDiagonalWeight τ a.1
  map_zero := completedDiagonalWeight_zero τ
  map_add a b := completedDiagonalWeight_add τ a.1 b.1 a.2 b.2
  map_smul r a := by
    simpa only [Positive.smul, ENNReal.ofReal_coe_nnreal] using completedDiagonalWeight_smul τ (r : ℝ) r.2 a.1
  tracial := completedDiagonalWeight_tracial τ
  lowerSemicontinuous := by
    change LowerSemicontinuous (fun a : Positive (CornerCompletion A) =>
      ⨆ k, completedTraceValue τ k a.1)
    exact lowerSemicontinuous_iSup fun k =>
      ((completedTraceValue_continuous τ k).comp continuous_subtype_val).lowerSemicontinuous

def sharedExtendedTrace (τ : TracialState A) : ExtendedTrace (TraceCone.MatrixLimit A) :=
  (completedExtendedTrace τ).pullback sharedMatrixEquiv.toNonUnitalStarAlgHom

end Pureness
end

namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ComplexOrder ENNReal NNReal CStarAlgebra
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def finiteMatrixMap (f : A →⋆ₙₐ[ℂ] B) (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix B n :=
  CStarMatrix.mapₙₐ f

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma finiteMatrixMap_successor (f : A →⋆ₙₐ[ℂ] B) (n : ℕ) (M : FinMatrix A n) :
    finiteMatrixMap f (n+1) (matrixSuccessor n M)=matrixSuccessor n (finiteMatrixMap f n M) := by
  ext i j
  change f (Fin.lastCases 0 (fun row => Fin.lastCases 0 (M row) j) i) =
    Fin.lastCases 0 (fun row => Fin.lastCases 0 (fun column => f (M row column)) j) i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma finiteMatrixMap_inclusion (f : A →⋆ₙₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    finiteMatrixMap f m (matrixInclusion h M)=matrixInclusion h (finiteMatrixMap f n M) := by
  change finiteMatrixMap f m (matrixPad h M)=matrixPad h (finiteMatrixMap f n M)
  induction m,h using Nat.le_induction with
  | base => simp only [matrixPad, Nat.leRecOn_self]
  | succ m h ih => rw [matrixPad_succ h,matrixPad_succ h,finiteMatrixMap_successor,ih]

lemma stabilizationCompatible (f : A →⋆ₙₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    ((matrixLimitStage m).comp (finiteMatrixMap f m)) (matrixInclusion h M)=
      ((matrixLimitStage n).comp (finiteMatrixMap f n)) M := by
  change matrixLimitStage m (finiteMatrixMap f m (matrixInclusion h M))=_
  rw [finiteMatrixMap_inclusion,matrixLimitStage_compatible]
  rfl

def stabilizationMap (f : A →⋆ₙₐ[ℂ] B) : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit B :=
  matrixLimitLift (fun n => (matrixLimitStage n).comp (finiteMatrixMap f n)) (stabilizationCompatible f)

def stabilizationInr : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit (Unitization ℂ A) :=
  stabilizationMap (Unitization.inrNonUnitalStarAlgHom ℂ A)

def NormalizedTrace.stabilized (τ : NormalizedTrace A) : ExtendedTrace (MatrixLimit A) :=
  (Pureness.sharedExtendedTrace τ.unitized).pullback stabilizationInr

end NonunitalGamma

namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ENNReal NNReal ComplexOrder CStarAlgebra
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def scaledTrace (r : ℝ≥0) (τ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := (r:ℝ≥0∞)*τ a
  map_zero := by rw [τ.map_zero,mul_zero]
  map_add a b := by rw [τ.map_add,mul_add]
  map_smul s a := by rw [τ.map_smul];ac_rfl
  tracial x := by rw [τ.tracial]
  lowerSemicontinuous := (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous
    τ.lowerSemicontinuous (fun _ _ h => mul_le_mul_right h _)

def boundedStabilized (τ : ExtendedTrace A) (hτ : WeightBounded τ) :
    ExtendedTrace (MatrixLimit A) :=
  by
  classical
  exact if h : τ=0 then 0 else scaledTrace
    ‖positiveFunctionalCLM (boundedWeightFunctional τ hτ)‖₊ (normalizedWeight τ hτ h).stabilized

def AllDenselyFiniteTracesBounded (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ τ : ExtendedTrace A, WeightDenselyFinite τ → WeightBounded τ

def StrictComparison (hcone : AllDenselyFiniteTracesBounded A) : Prop :=
  ∀ a b : Positive (MatrixLimit A), b.1 ≠ 0 →
    (∀ (τ : ExtendedTrace A) (hτ : WeightDenselyFinite τ),
      (boundedStabilized τ (hcone τ hτ)).rank b=1 →
      (boundedStabilized τ (hcone τ hτ)).rank a<1) → CuntzBelow a b

end NonunitalGamma

namespace NonunitalGamma
open Pureness CurrentMain Filter DirectComparison
open scoped Topology ComplexOrder
variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "τ" => (fun t : NormalizedTrace A => NormalizedTrace.unitized t)

def UniformGamma (A : Type) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [Nonempty (NormalizedTrace A)] (U : Ultrafilter ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ p : Fin m → FamilyUltrapower (fun t : NormalizedTrace A => t.unitized) U,
    (∀ i, IsStarProjection (p i)) ∧ (∑ i, p i)=1 ∧
    (∀ i (a : A), Commute (p i) (familyUltrapowerMap (fun t : NormalizedTrace A => t.unitized) U (Unitization.inr a))) ∧
    ∀ i (a : A) (s : ℕ → NormalizedTrace A),
      (familyLimitTrace (fun t : NormalizedTrace A => t.unitized) U s).functional
          (familyUltrapowerMap (fun t : NormalizedTrace A => t.unitized) U (Unitization.inr a)*p i) =
        (1/(m:ℂ))*(familyLimitTrace (fun t : NormalizedTrace A => t.unitized) U s).functional
          (familyUltrapowerMap (fun t : NormalizedTrace A => t.unitized) U (Unitization.inr a))

end NonunitalGamma

namespace NonunitalGamma
open TraceCone Pureness CurrentMain Filter
open scoped ComplexOrder
variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def StablyProjectionless (A : Type) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Prop :=
  Projectionless (MatrixLimit A)

end NonunitalGamma

namespace NuclearUnitization
open scoped TensorProduct
universe u v

structure NonUnitalCStarNorm (R : Type*) [NonUnitalRing R] [StarRing R] [Module ℂ R]
    extends RingNorm R where
  smul : ∀ (c : ℂ) x, toRingNorm (c • x)=‖c‖*toRingNorm x
  cstar : ∀ x, toRingNorm (star x*x)=toRingNorm x*toRingNorm x

def IsNuclear (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (NonUnitalCStarNorm (A ⊗[ℂ] B))

end NuclearUnitization

namespace Pureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

abbrev Completion (p : CStarAlgebraNorm R) :=
  letI := p.normedRing
  UniformSpace.Completion R

instance completionCStarAlgebra (p : CStarAlgebraNorm R) : NonUnitalCStarAlgebra p.Completion := by
  letI := p.normedRing
  letI := p.normedAlgebra
  letI := p.cstarRing
  exact Pureness.nonUnitalCompletionCStarAlgebra R

end Pureness.CStarAlgebraNorm

namespace ConcreteMatrixUnits
open scoped ComplexOrder
variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [CStarAlgebra D]

structure System (ι D : Type*) [Fintype ι] [DecidableEq ι] [CStarAlgebra D] where
  entry : ι → ι → D
  mul_entry : ∀ i j k l,entry i j*entry k l=if j=k then entry i l else 0
  star_entry : ∀ i j,star (entry i j)=entry j i
  sum_diag : ∑ i,entry i i=1

end ConcreteMatrixUnits

namespace JiangSuConstruction
open scoped Kronecker ComplexOrder

abbrev Mat (n : ℕ) := CStarMatrix (Fin n) (Fin n) ℂ

abbrev TensorMat (p q : ℕ) := CStarMatrix (Fin p × Fin q) (Fin p × Fin q) ℂ

abbrev Interval := Set.Icc (0 : ℝ) 1

end JiangSuConstruction

namespace JiangSuConstruction
open scoped Kronecker ComplexOrder
local instance (priority := 2000) continuousMatrixSemiring (p q : ℕ) :
    Semiring C(Interval, TensorMat p q) := (inferInstance : Ring C(Interval, TensorMat p q)).toSemiring

def leftAmplification (p q : ℕ) : Mat p →⋆ₐ[ℂ] TensorMat p q where
  toFun x := CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.zero_kronecker _
  map_add' x y := Matrix.add_kronecker _ _ _
  map_mul' x y := by
    change (CStarMatrix.ofMatrix.symm x * CStarMatrix.ofMatrix.symm y) ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ) =
      (CStarMatrix.ofMatrix.symm x ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)) *
      (CStarMatrix.ofMatrix.symm y ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul (CStarMatrix.ofMatrix.symm x)
      (CStarMatrix.ofMatrix.symm y) (1 : Matrix (Fin q) (Fin q) ℂ) 1
  commutes' z := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [CStarMatrix.algebraMap_apply, Matrix.kroneckerMap_apply,
        hik, hjl]
  map_star' x := by
    change (CStarMatrix.ofMatrix.symm x).conjTranspose ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ) =
      ((CStarMatrix.ofMatrix.symm x) ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ)).conjTranspose
    simpa only [Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker (CStarMatrix.ofMatrix.symm x) (1 : Matrix (Fin q) (Fin q) ℂ)).symm

def rightAmplification (p q : ℕ) : Mat q →⋆ₐ[ℂ] TensorMat p q where
  toFun x := CStarMatrix.ofMatrix ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x)
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.kronecker_zero _
  map_add' x y := Matrix.kronecker_add _ _ _
  map_mul' x y := by
    change (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm x * CStarMatrix.ofMatrix.symm y) =
      ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x) *
      ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm y)
    simpa only [Matrix.one_mul] using Matrix.mul_kronecker_mul (1 : Matrix (Fin p) (Fin p) ℂ) 1
      (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)
  commutes' z := by
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [CStarMatrix.algebraMap_apply, Matrix.kroneckerMap_apply,
        hik, hjl]
  map_star' x := by
    change (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm x).conjTranspose =
      ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm x).conjTranspose
    simpa only [Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker (1 : Matrix (Fin p) (Fin p) ℂ) (CStarMatrix.ofMatrix.symm x)).symm

def evalHom (p q : ℕ) (t : Interval) : C(Interval, TensorMat p q) →⋆ₐ[ℂ] TensorMat p q where
  toFun f := f t
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def leftEndpoint : Interval := ⟨0,by norm_num⟩

def rightEndpoint : Interval := ⟨1,by norm_num⟩

def dimensionDrop (p q : ℕ) : StarSubalgebra ℂ C(Interval, TensorMat p q) :=
  (leftAmplification p q).range.comap (evalHom p q leftEndpoint) ⊓
  (rightAmplification p q).range.comap (evalHom p q rightEndpoint)

instance tensorMat_finiteDimensional (p q : ℕ) : FiniteDimensional ℂ (TensorMat p q) :=
  FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
    (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective

lemma leftAmplification_closed (p q : ℕ) :
    IsClosed ((leftAmplification p q).range : Set (TensorMat p q)) := by
  exact (leftAmplification p q).range.toSubalgebra.toSubmodule.closed_of_finiteDimensional

lemma rightAmplification_closed (p q : ℕ) :
    IsClosed ((rightAmplification p q).range : Set (TensorMat p q)) := by
  exact (rightAmplification p q).range.toSubalgebra.toSubmodule.closed_of_finiteDimensional

instance dimensionDrop_closed (p q : ℕ) : IsClosed (dimensionDrop p q : Set C(Interval, TensorMat p q)) := by
  change IsClosed ((fun f : C(Interval, TensorMat p q) => f leftEndpoint) ⁻¹'
    ((leftAmplification p q).range : Set (TensorMat p q)) ∩
    (fun f : C(Interval, TensorMat p q) => f rightEndpoint) ⁻¹'
    ((rightAmplification p q).range : Set (TensorMat p q)))
  apply IsClosed.inter
  · exact (leftAmplification_closed p q).preimage
      (show Continuous (fun f : C(Interval, TensorMat p q) => f leftEndpoint) from
        continuous_eval_const leftEndpoint)
  · exact (rightAmplification_closed p q).preimage
      (show Continuous (fun f : C(Interval, TensorMat p q) => f rightEndpoint) from
        continuous_eval_const rightEndpoint)

abbrev DimensionDrop (p q : ℕ) := dimensionDrop p q

instance (p q : ℕ) : CStarAlgebra (DimensionDrop p q) := by
  letI : SubringClass (StarSubalgebra ℂ C(Interval, TensorMat p q)) C(Interval, TensorMat p q) :=
    @StarSubalgebra.subringClass ℂ C(Interval, TensorMat p q) _ _ _ _ _ _
  exact StarSubalgebra.cstarAlgebra (dimensionDrop p q)

end JiangSuConstruction

section
open Filter
open scoped ENNReal Topology CStarAlgebra
namespace SequentialCStar
variable (C : ℕ → Type*) [∀ n, CStarAlgebra (C n)] [∀ n, Nontrivial (C n)]
open TraceCone

def boundedOne : BoundedFamilies C := ⟨fun _ => 1,memℓp_infty ⟨1,by
  rintro _ ⟨n,rfl⟩
  simp⟩⟩

instance : One (FamilyQuotient C) := ⟨FamilyQuotient.mk (boundedOne C)⟩

lemma quotient_one_mul (x : FamilyQuotient C) : 1*x=x := by
  obtain ⟨x,rfl⟩ := FamilyQuotient.mk_surjective x
  change FamilyQuotient.mk (boundedOne C*x)=FamilyQuotient.mk x
  congr 1
  apply lp.ext
  funext n
  exact one_mul (x n)

lemma quotient_mul_one (x : FamilyQuotient C) : x*1=x := by
  obtain ⟨x,rfl⟩ := FamilyQuotient.mk_surjective x
  change FamilyQuotient.mk (x*boundedOne C)=FamilyQuotient.mk x
  congr 1
  apply lp.ext
  funext n
  exact mul_one (x n)

instance : Monoid (FamilyQuotient C) where
  one_mul := quotient_one_mul C
  mul_one := quotient_mul_one C

instance : Ring (FamilyQuotient C) where
  natCast n := n • (1 : FamilyQuotient C)
  natCast_zero := zero_smul _ _
  natCast_succ n := by simp only [add_smul,one_smul]
  intCast z := z • (1 : FamilyQuotient C)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc := negSucc_zsmul _

instance : Algebra ℂ (FamilyQuotient C) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedRing (FamilyQuotient C) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

instance : NormedAlgebra ℂ (FamilyQuotient C) where
  norm_smul_le := norm_smul_le

instance : CStarAlgebra (FamilyQuotient C) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

structure System where
  map : ∀ {n m}, n≤ m → C n →⋆ₐ[ℂ] C m
  identity : ∀ n (a : C n), map (le_refl n) a=a
  composition : ∀ {n m k} (h : n≤ m) (g : m≤k) (a : C n), map g (map h a)=map (h.trans g) a
  injective : ∀ {n m} (h : n≤ m), Function.Injective (map h)

end SequentialCStar
end

section
open Filter
open scoped ENNReal Topology CStarAlgebra
namespace SequentialCStar
variable (C : ℕ → Type*) [∀ n, CStarAlgebra (C n)] [∀ n, Nontrivial (C n)]
open TraceCone
namespace System
variable {C} (S : System C)

omit [∀ n, Nontrivial (C n)] in
lemma map_norm {n m} (h : n≤ m) (a : C n) : ‖S.map h a‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map (S.map h).toNonUnitalStarAlgHom (S.injective h) a

def family (n : ℕ) : C n →⋆ₙₐ[ℂ] BoundedFamilies C where
  toFun a := ⟨fun m => if h : n≤ m then S.map h a else 0,
    memℓp_infty ⟨‖a‖,by
      rintro _ ⟨m,rfl⟩
      change ‖if h : n≤ m then S.map h a else 0‖≤‖a‖
      split_ifs <;> simp [map_norm,norm_nonneg]⟩⟩
  map_zero' := by apply lp.ext; funext m; change (if h : n≤ m then S.map h 0 else 0)=0; split_ifs <;> simp
  map_add' a b := by
    apply lp.ext; funext m
    change (if h : n≤ m then S.map h (a+b) else 0)=(if h : n≤ m then S.map h a else 0)+(if h : n≤ m then S.map h b else 0)
    split_ifs <;> simp
  map_mul' a b := by
    apply lp.ext; funext m
    change (if h : n≤ m then S.map h (a*b) else 0)=(if h : n≤ m then S.map h a else 0)*(if h : n≤ m then S.map h b else 0)
    split_ifs <;> simp
  map_smul' c a := by
    apply lp.ext; funext m
    change (if h : n≤ m then S.map h (c • a) else 0)=c • (if h : n≤ m then S.map h a else 0)
    split_ifs <;> simp
  map_star' a := by
    apply lp.ext; funext m
    change (if h : n≤ m then S.map h (star a) else 0)=star (if h : n≤ m then S.map h a else 0)
    by_cases h : n≤ m
    · rw [dite_eq_left h,dite_eq_left h]
      exact map_star (S.map h) a
    · rw [dite_eq_right h,dite_eq_right h]
      exact (star_zero _).symm

def stageNonUnital (n : ℕ) : C n →⋆ₙₐ[ℂ] FamilyQuotient C :=
  FamilyQuotient.quotientHom.comp (S.family n)

@[simp] lemma stageNonUnital_norm (n : ℕ) (a : C n) : ‖S.stageNonUnital n a‖=‖a‖ := by
  change ‖FamilyQuotient.mk (S.family n a)‖=‖a‖
  rw [FamilyQuotient.norm_mk_eq_limsup]
  calc
    _ = limsup (fun _ : ℕ => ‖a‖) atTop := limsup_congr (by
      filter_upwards [eventually_ge_atTop n] with m hm
      change ‖if h : n≤ m then S.map h a else 0‖=‖a‖
      simp [hm,map_norm])
    _ = ‖a‖ := limsup_const (b := ‖a‖)

lemma stageNonUnital_one (n : ℕ) : S.stageNonUnital n 1=1 := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop n] with m hm
  change (if h : n≤ m then S.map h 1 else 0)=1
  simp [hm]

def stage (n : ℕ) : C n →⋆ₐ[ℂ] FamilyQuotient C where
  toFun := S.stageNonUnital n
  map_one' := S.stageNonUnital_one n
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,S.stageNonUnital_one,←Algebra.algebraMap_eq_smul_one]
  map_star' := map_star _

@[simp] lemma stage_norm (n : ℕ) (a : C n) : ‖S.stage n a‖=‖a‖ := S.stageNonUnital_norm n a

@[simp] lemma stage_compatible {n m} (h : n ≤ m) (a : C n) :
    S.stage m (S.map h a) = S.stage n a := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop m] with index index_ge
  change (if bound : m ≤ index then S.map bound (S.map h a) else 0) =
    (if bound : n ≤ index then S.map bound a else 0)
  rw [dite_eq_left index_ge, dite_eq_left (h.trans index_ge)]
  exact S.composition h index_ge a

def unionAlgebra : StarSubalgebra ℂ (FamilyQuotient C) where
  carrier := {element | ∃ (index : ℕ) (value : C index), S.stage index value = element}
  one_mem' := ⟨0, 1, map_one _⟩
  zero_mem' := ⟨0, 0, map_zero _⟩
  add_mem' := by
    rintro first second ⟨left, first, rfl⟩ ⟨right, second, rfl⟩
    exact ⟨max left right,
      S.map (le_max_left left right) first + S.map (le_max_right left right) second,
      by simp⟩
  mul_mem' := by
    rintro first second ⟨left, first, rfl⟩ ⟨right, second, rfl⟩
    exact ⟨max left right,
      S.map (le_max_left left right) first * S.map (le_max_right left right) second,
      by simp⟩
  algebraMap_mem' scalar := ⟨0, algebraMap ℂ (C 0) scalar, (S.stage 0).commutes scalar⟩
  star_mem' := by
    rintro element ⟨index, value, rfl⟩
    exact ⟨index, star value, map_star _ value⟩

def limitAlgebra : StarSubalgebra ℂ (FamilyQuotient C) := S.unionAlgebra.topologicalClosure

instance limitAlgebra_closed : IsClosed (S.limitAlgebra : Set (FamilyQuotient C)) :=
  StarSubalgebra.isClosed_topologicalClosure _

abbrev Limit := S.limitAlgebra

instance : CStarAlgebra S.Limit := StarSubalgebra.cstarAlgebra _

def inclusion (n : ℕ) : C n →⋆ₐ[ℂ] S.Limit where
  toFun a := ⟨S.stage n a,StarSubalgebra.le_topologicalClosure _ ⟨n,a,rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  commutes' z := Subtype.ext ((S.stage n).commutes z)
  map_star' a := Subtype.ext (map_star _ a)

@[simp] lemma inclusion_norm (n : ℕ) (a : C n) : ‖S.inclusion n a‖=‖a‖ := S.stage_norm n a

lemma inclusion_isometry (n : ℕ) : Isometry (S.inclusion n) := AddMonoidHomClass.isometry_of_norm _ (S.inclusion_norm n)

theorem finite_stage_approximation (x : S.Limit) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (a : C n), ‖x-S.inclusion n a‖<ε := by
  obtain ⟨y,⟨n,a,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp x.2 ε hε
  refine ⟨n,a,?_⟩
  change ‖(x : FamilyQuotient C)-S.stage n a‖<ε
  simpa only [dist_eq_norm] using hy

end System
end SequentialCStar
end

namespace SequentialCStar
variable {C : ℕ → Type*} [∀ n, CStarAlgebra (C n)]
variable (step : ∀ n, C n →⋆ₐ[ℂ] C (n+1))

def sequenceHom {n m : ℕ} (h : n≤ m) : C n →⋆ₐ[ℂ] C m :=
  Nat.leRecOn (C := fun k => C n →⋆ₐ[ℂ] C k) h
    (fun {k} f => (step k).comp f) (StarAlgHom.id ℂ (C n))

@[simp] lemma sequenceHom_self (n : ℕ) (a : C n) : sequenceHom step (le_refl n) a=a := by
  rw [sequenceHom,Nat.leRecOn_self]
  rfl

lemma sequenceHom_succ {n m : ℕ} (h : n≤ m) (a : C n) :
    sequenceHom step (h.trans (Nat.le_succ m)) a=step m (sequenceHom step h a) := by
  rw [sequenceHom,Nat.leRecOn_succ h]
  rfl

lemma sequenceHom_comp {n m k : ℕ} (h : n≤ m) (g : m≤k) (a : C n) :
    sequenceHom step g (sequenceHom step h a)=sequenceHom step (h.trans g) a := by
  induction g with
  | refl => simp
  | @step k g ih =>
    rw [sequenceHom_succ step g,sequenceHom_succ step (h.trans g),ih]

lemma sequenceHom_injective (hs : ∀ n,Function.Injective (step n)) {n m : ℕ} (h : n≤ m) :
    Function.Injective (sequenceHom step h) := by
  induction h with
  | refl => intro x y h; simpa using h
  | @step m h ih =>
    intro x y hxy
    rw [sequenceHom_succ step h,sequenceHom_succ step h] at hxy
    exact ih (hs m hxy)

def System.ofSequence (hs : ∀ n,Function.Injective (step n)) : System C where
  map h := sequenceHom step h
  identity := sequenceHom_self step
  composition := sequenceHom_comp step
  injective := sequenceHom_injective step hs

end SequentialCStar

namespace JiangSuConstruction

structure Multiplicities (p q : ℕ) where
  k : ℕ
  l : ℕ
  lower : ℕ
  upper : ℕ
  residual : ℕ
  gamma : ℕ
  delta : ℕ
  k_pos : 0<k
  l_pos : 0<l
  gamma_pos : 0<gamma
  delta_pos : 0<delta
  residual_pos : 0<residual
  lower_eq : lower=(p*k)*gamma
  upper_eq : upper=(q*l)*delta
  total : lower+upper+residual=k*l
  zero_count : lower+residual=l*(k-q*delta)
  one_count : upper+residual=k*(l-p*gamma)
  zero_reduced : p*(k-q*delta)+(p*q)*delta=p*k
  one_reduced : q*(l-p*gamma)+(p*q)*gamma=q*l
  lower_mass : k*l≤8*lower
  upper_mass : k*l≤8*upper



def lowerEigenvalue : C(Interval,Interval) :=
  ⟨fun t => ⟨t.1/((2 : ℕ) : ℝ),by constructor <;> linarith [t.2.1,t.2.2]⟩,
    by fun_prop⟩

def upperEigenvalue : C(Interval,Interval) :=
  ⟨fun t => ⟨(t.1+1)/((2 : ℕ) : ℝ),by constructor <;> linarith [t.2.1,t.2.2]⟩,
    by fun_prop⟩

theorem midpoint_value_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_of_lt one_half_pos, le_of_lt one_half_lt_one⟩

def midpoint : Interval := ⟨(1 / ((2 : ℕ) : ℝ) : ℝ), midpoint_value_mem⟩


open Complex NormedSpace selfAdjoint Unitary
open scoped CStarAlgebra ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrix_finite_spectrum (a : CStarMatrix n n ℂ) : (spectrum ℂ a).Finite := by
  have h := Matrix.finite_spectrum (CStarMatrix.ofMatrix.symm a)
  rwa [← AlgEquiv.spectrum_eq (CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ)).toAlgEquiv] at h

lemma finite_spectrum_unitary_exp {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hf : (spectrum ℂ (u : A)).Finite) :
    expUnitary (argSelfAdjoint u)=u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) := hf.continuousOn arg
  rw [expUnitary_coe,argSelfAdjoint_coe,← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul ..,← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy => ?_
  have hy₁ : ‖y‖=1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I*y.arg=log y :=
    Complex.ext (by simp [log_re,hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ,this] using exp_log (by aesop)

lemma finite_matrix_unitary_joined_one (u : unitary (CStarMatrix n n ℂ)) : Joined 1 u := by
  have hf : (spectrum ℂ (u : CStarMatrix n n ℂ)).Finite := matrix_finite_spectrum _
  have he : expUnitary (argSelfAdjoint u)=u := finite_spectrum_unitary_exp u hf
  exact he ▸ selfAdjoint.joined_one_expUnitary (argSelfAdjoint u)

def finiteMatrixUnitaryPath (u v : unitary (CStarMatrix n n ℂ)) : Path u v :=
  ((finite_matrix_unitary_joined_one u).symm.trans (finite_matrix_unitary_joined_one v)).somePath

end JiangSuConstruction

namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def blockDiagonalHom : (κ → CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] CStarMatrix (ι × κ) (ι × κ) ℂ where
  toFun x := CStarMatrix.ofMatrix (Matrix.blockDiagonal (fun i => CStarMatrix.ofMatrix.symm (x i)))
  map_one' := Matrix.blockDiagonal_one
  map_zero' := Matrix.blockDiagonal_zero
  map_add' x y := Matrix.blockDiagonal_add _ _
  map_mul' x y := Matrix.blockDiagonal_mul _ _
  commutes' z := by
    ext ⟨i,k⟩ ⟨j,l⟩
    by_cases h : k=l <;> by_cases g : i=j <;>
      simp [Matrix.blockDiagonal_apply, CStarMatrix.algebraMap_apply,h,g]
  map_star' x := (Matrix.blockDiagonal_conjTranspose _).symm

@[simp] lemma blockDiagonalHom_apply (x : κ → CStarMatrix ι ι ℂ) (i j : ι) (k : κ) :
    blockDiagonalHom x (i,k) (j,k)=x k i j := by
  exact Matrix.blockDiagonal_apply_eq _ i j k

lemma blockDiagonalHom_injective : Function.Injective (blockDiagonalHom (ι := ι) (κ := κ)) := by
  intro x y h
  funext k
  ext i j
  simpa only [blockDiagonalHom_apply] using congrArg (fun a : CStarMatrix (ι×κ) (ι×κ) ℂ => a (i,k) (j,k)) h

lemma blockDiagonalHom_continuous : Continuous (blockDiagonalHom (ι := ι) (κ := κ)) :=
  map_continuous (blockDiagonalHom (ι := ι) (κ := κ))

def diagonalContinuousHom (ξ : κ → C(Interval,Interval)) :
    C(Interval,CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] C(Interval,CStarMatrix (ι×κ) (ι×κ) ℂ) where
  toFun f := ⟨fun t => blockDiagonalHom (fun k => f (ξ k t)),
    blockDiagonalHom_continuous.comp (continuous_pi fun k => f.continuous.comp (ξ k).continuous)⟩
  map_one' := by apply ContinuousMap.ext; intro t; exact map_one blockDiagonalHom
  map_zero' := by apply ContinuousMap.ext; intro t; exact map_zero blockDiagonalHom
  map_add' f g := by apply ContinuousMap.ext; intro t; exact map_add blockDiagonalHom _ _
  map_mul' f g := by apply ContinuousMap.ext; intro t; exact map_mul blockDiagonalHom _ _
  commutes' z := by apply ContinuousMap.ext; intro t; exact blockDiagonalHom.commutes z
  map_star' f := by apply ContinuousMap.ext; intro t; exact map_star blockDiagonalHom _

def unitaryConjugation {A : Type*} [CStarAlgebra A] (u : unitary A) : A →⋆ₐ[ℂ] A where
  toFun a := (u:A)*a*star (u:A)
  map_one' := by simp only [mul_one]; exact u.2.2
  map_zero' := by simp
  map_add' a b := by simp [mul_add,add_mul]
  map_mul' a b := by
    simp only [mul_assoc]
    rw [←mul_assoc (star (u:A)),u.2.1,one_mul]
  commutes' z := by
    rw [← (Algebra.commutes z (u:A)), mul_assoc,u.2.2,mul_one]
  map_star' a := by simp [star_mul,mul_assoc]

lemma unitaryConjugation_injective {A : Type*} [CStarAlgebra A] (u : unitary A) :
    Function.Injective (unitaryConjugation u) := by
  intro a b h
  have h' := congrArg (fun x : A => star (u:A)*x*(u:A)) h
  simpa [unitaryConjugation,mul_assoc,←mul_assoc (star (u:A)) (u:A),u.2.1] using h'

def continuousUnitaryConjugation (u : C(Interval,unitary (CStarMatrix ι ι ℂ))) :
    C(Interval,CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] C(Interval,CStarMatrix ι ι ℂ) where
  toFun f := ⟨fun t => unitaryConjugation (u t) (f t),
    (((continuous_subtype_val.comp u.continuous).mul f.continuous).mul
      (continuous_star.comp (continuous_subtype_val.comp u.continuous)))⟩
  map_one' := by apply ContinuousMap.ext; intro t; exact map_one (unitaryConjugation (u t))
  map_zero' := by apply ContinuousMap.ext; intro t; exact map_zero (unitaryConjugation (u t))
  map_add' f g := by apply ContinuousMap.ext; intro t; exact map_add (unitaryConjugation (u t)) _ _
  map_mul' f g := by apply ContinuousMap.ext; intro t; exact map_mul (unitaryConjugation (u t)) _ _
  commutes' z := by apply ContinuousMap.ext; intro t; exact (unitaryConjugation (u t)).commutes z
  map_star' f := by apply ContinuousMap.ext; intro t; exact map_star (unitaryConjugation (u t)) _

lemma continuousUnitaryConjugation_injective (u : C(Interval,unitary (CStarMatrix ι ι ℂ))) :
    Function.Injective (continuousUnitaryConjugation u) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  exact unitaryConjugation_injective (u t) (congrArg (fun x : C(Interval,CStarMatrix ι ι ℂ) => x t) h)

end JiangSuConstruction

namespace JiangSuConstruction
open scoped Kronecker ComplexOrder CStarAlgebra
variable {ι κ α β ν : Type*}

def endpointLeftEquiv : ((ι×κ)×((α×ν)⊕(β×(κ×ν)))) ≃
    (((ι×α)⊕((ι×κ)×β))×(κ×ν)) where
  toFun x := match x with
    | ((i,k),Sum.inl (a,l)) => (Sum.inl (i,a),(k,l))
    | ((i,k),Sum.inr (b,kl)) => (Sum.inr ((i,k),b),kl)
  invFun x := match x with
    | (Sum.inl (i,a),(k,l)) => ((i,k),Sum.inl (a,l))
    | (Sum.inr ((i,k),b),kl) => ((i,k),Sum.inr (b,kl))
  left_inv := by rintro ⟨⟨i,k⟩,⟨a,l⟩|⟨b,kl⟩⟩ <;> rfl
  right_inv := by rintro ⟨⟨i,a⟩|⟨⟨i,k⟩,b⟩,⟨k',l⟩⟩ <;> rfl

def endpointRightEquiv : ((ι×κ)×((α×ν)⊕(β×(ι×ν)))) ≃
    ((ι×ν)×((κ×α)⊕((ι×κ)×β))) where
  toFun x := match x with
    | ((i,k),Sum.inl (a,l)) => ((i,l),Sum.inl (k,a))
    | ((i,k),Sum.inr (b,il)) => (il,Sum.inr ((i,k),b))
  invFun x := match x with
    | ((i,l),Sum.inl (k,a)) => ((i,k),Sum.inl (a,l))
    | (il,Sum.inr ((i,k),b)) => ((i,k),Sum.inr (b,il))
  left_inv := by rintro ⟨⟨i,k⟩,⟨a,l⟩|⟨b,il⟩⟩ <;> rfl
  right_inv := by rintro ⟨⟨i,l⟩,⟨k,a⟩|⟨⟨i',k⟩,b⟩⟩ <;> rfl

end JiangSuConstruction

namespace JiangSuConstruction
open scoped Kronecker ComplexOrder CStarAlgebra
variable {ι κ α β ν : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ν] [DecidableEq ν]

def endpointReduced (a : CStarMatrix ι ι ℂ) (b : CStarMatrix (ι×κ) (ι×κ) ℂ) :
    CStarMatrix ((ι×α)⊕((ι×κ)×β)) ((ι×α)⊕((ι×κ)×β)) ℂ :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks
    (Matrix.blockDiagonal fun _ : α => CStarMatrix.ofMatrix.symm a) 0 0
    (Matrix.blockDiagonal fun _ : β => CStarMatrix.ofMatrix.symm b))

lemma endpoint_left_regroup (a : CStarMatrix ι ι ℂ) (b : CStarMatrix (ι×κ) (ι×κ) ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (endpointLeftEquiv (ι:=ι) (κ:=κ) (α:=α) (β:=β) (ν:=ν))
      (blockDiagonalHom (fun x : (α×ν)⊕(β×(κ×ν)) => match x with
        | Sum.inl _ => CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix κ κ ℂ))
        | Sum.inr _ => b)) =
    CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm (endpointReduced (α:=α) (β:=β) a b) ⊗ₖ
      (1 : Matrix (κ×ν) (κ×ν) ℂ)) := by
  let x : (α×ν)⊕(β×(κ×ν)) → Matrix (ι×κ) (ι×κ) ℂ := fun z => match z with
    | Sum.inl _ => CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix κ κ ℂ)
    | Sum.inr _ => CStarMatrix.ofMatrix.symm b
  ext ⟨s,⟨k,l⟩⟩ ⟨t,⟨k',l'⟩⟩
  cases s with
  | inl ia =>
    rcases ia with ⟨i,a'⟩
    cases t with
    | inl ja =>
      rcases ja with ⟨j,a''⟩
      change Matrix.blockDiagonal x (((i,k),Sum.inl (a',l))) (((j,k'),Sum.inl (a'',l'))) = _
      by_cases ha : a'=a'' <;> by_cases hk : k=k' <;> by_cases hl : l=l' <;>
        simp [x,Matrix.blockDiagonal_apply,endpointReduced,Matrix.kroneckerMap_apply,ha,hk,hl]
    | inr jb =>
      rcases jb with ⟨⟨j,h⟩,b'⟩
      change Matrix.blockDiagonal x (((i,k),Sum.inl (a',l))) (((j,h),Sum.inr (b',(k',l')))) = _
      simp [x,Matrix.blockDiagonal_apply,endpointReduced,Matrix.kroneckerMap_apply]
  | inr ib =>
    rcases ib with ⟨⟨i,h⟩,b'⟩
    cases t with
    | inl ja =>
      rcases ja with ⟨j,a'⟩
      change Matrix.blockDiagonal x (((i,h),Sum.inr (b',(k,l)))) (((j,k'),Sum.inl (a',l'))) = _
      simp [x,Matrix.blockDiagonal_apply,endpointReduced,Matrix.kroneckerMap_apply]
    | inr jb =>
      rcases jb with ⟨⟨j,h'⟩,b''⟩
      change Matrix.blockDiagonal x (((i,h),Sum.inr (b',(k,l)))) (((j,h'),Sum.inr (b'',(k',l')))) = _
      by_cases hb : b'=b'' <;> by_cases hk : k=k' <;> by_cases hl : l=l' <;>
        simp [x,Matrix.blockDiagonal_apply,endpointReduced,Matrix.kroneckerMap_apply,hb,hk,hl]

def endpointRightReduced (a : CStarMatrix κ κ ℂ) (b : CStarMatrix (ι×κ) (ι×κ) ℂ) :
    CStarMatrix ((κ×α)⊕((ι×κ)×β)) ((κ×α)⊕((ι×κ)×β)) ℂ :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks
    (Matrix.blockDiagonal fun _ : α => CStarMatrix.ofMatrix.symm a) 0 0
    (Matrix.blockDiagonal fun _ : β => CStarMatrix.ofMatrix.symm b))

lemma endpoint_right_regroup (a : CStarMatrix κ κ ℂ) (b : CStarMatrix (ι×κ) (ι×κ) ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (endpointRightEquiv (ι:=ι) (κ:=κ) (α:=α) (β:=β) (ν:=ν))
      (blockDiagonalHom (fun x : (α×ν)⊕(β×(ι×ν)) => match x with
        | Sum.inl _ => CStarMatrix.ofMatrix ((1 : Matrix ι ι ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a)
        | Sum.inr _ => b)) =
    CStarMatrix.ofMatrix ((1 : Matrix (ι×ν) (ι×ν) ℂ) ⊗ₖ
      CStarMatrix.ofMatrix.symm (endpointRightReduced (α:=α) (β:=β) a b)) := by
  let x : (α×ν)⊕(β×(ι×ν)) → Matrix (ι×κ) (ι×κ) ℂ := fun z => match z with
    | Sum.inl _ => (1 : Matrix ι ι ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a
    | Sum.inr _ => CStarMatrix.ofMatrix.symm b
  ext ⟨⟨i,l⟩,s⟩ ⟨⟨i',l'⟩,t⟩
  cases s with
  | inl ka =>
    rcases ka with ⟨k,a'⟩
    cases t with
    | inl ja =>
      rcases ja with ⟨j,a''⟩
      change Matrix.blockDiagonal x (((i,k),Sum.inl (a',l))) (((i',j),Sum.inl (a'',l'))) = _
      by_cases ha : a'=a'' <;> by_cases hi : i=i' <;> by_cases hl : l=l' <;>
        simp [x,Matrix.blockDiagonal_apply,endpointRightReduced,Matrix.kroneckerMap_apply,ha,hi,hl]
    | inr jb =>
      rcases jb with ⟨⟨j,h⟩,b'⟩
      change Matrix.blockDiagonal x (((i,k),Sum.inl (a',l))) (((j,h),Sum.inr (b',(i',l')))) = _
      simp [x,Matrix.blockDiagonal_apply,endpointRightReduced,Matrix.kroneckerMap_apply]
  | inr ib =>
    rcases ib with ⟨⟨j,h⟩,b'⟩
    cases t with
    | inl ka =>
      rcases ka with ⟨k,a'⟩
      change Matrix.blockDiagonal x (((j,h),Sum.inr (b',(i,l)))) (((i',k),Sum.inl (a',l'))) = _
      simp [x,Matrix.blockDiagonal_apply,endpointRightReduced,Matrix.kroneckerMap_apply]
    | inr jb =>
      rcases jb with ⟨⟨j',h'⟩,b''⟩
      change Matrix.blockDiagonal x (((j,h),Sum.inr (b',(i,l)))) (((j',h'),Sum.inr (b'',(i',l')))) = _
      by_cases hb : b'=b'' <;> by_cases hi : i=i' <;> by_cases hl : l=l' <;>
        simp [x,Matrix.blockDiagonal_apply,endpointRightReduced,Matrix.kroneckerMap_apply,hb,hi,hl]

end JiangSuConstruction

namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def continuousReindex (e : ι ≃ κ) :
    C(Interval,CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] C(Interval,CStarMatrix κ κ ℂ) :=
  ContinuousMap.compStarAlgHom Interval (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom
    (map_continuous (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom)

lemma continuousReindex_injective (e : ι≃κ) : Function.Injective (continuousReindex e) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  apply (CStarMatrix.reindexₐ ℂ ℂ e).injective
  exact congrArg (fun x : C(Interval,CStarMatrix κ κ ℂ) => x t) h

end JiangSuConstruction

namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {p q P Q : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

def connectingAmbient (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q))
    (u₀ u₁ : unitary (TensorMat P Q)) :
    C(Interval,TensorMat p q) →⋆ₐ[ℂ] C(Interval,TensorMat P Q) :=
  (continuousUnitaryConjugation (finiteMatrixUnitaryPath u₀ u₁).toContinuousMap).comp
    ((continuousReindex e).comp (diagonalContinuousHom ξ))

lemma connectingAmbient_zero (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q))
    (u₀ u₁ : unitary (TensorMat P Q)) (f : C(Interval,TensorMat p q)) :
    connectingAmbient ξ e u₀ u₁ f leftEndpoint=
      unitaryConjugation u₀ ((CStarMatrix.reindexₐ ℂ ℂ e)
        (blockDiagonalHom (fun k => f (ξ k leftEndpoint)))) := by
  change unitaryConjugation ((finiteMatrixUnitaryPath u₀ u₁) 0) _=_
  rw [Path.source]
  rfl

lemma connectingAmbient_one (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q))
    (u₀ u₁ : unitary (TensorMat P Q)) (f : C(Interval,TensorMat p q)) :
    connectingAmbient ξ e u₀ u₁ f rightEndpoint=
      unitaryConjugation u₁ ((CStarMatrix.reindexₐ ℂ ℂ e)
        (blockDiagonalHom (fun k => f (ξ k rightEndpoint)))) := by
  change unitaryConjugation ((finiteMatrixUnitaryPath u₀ u₁) 1) _=_
  rw [Path.target]
  rfl

def connectingMap (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q)) (u₀ u₁ : unitary (TensorMat P Q))
    (h₀ : ∀ f : DimensionDrop p q, unitaryConjugation u₀ ((CStarMatrix.reindexₐ ℂ ℂ e)
      (blockDiagonalHom (fun k => (f : C(Interval,TensorMat p q)) (ξ k leftEndpoint)))) ∈
        (leftAmplification P Q).range)
    (h₁ : ∀ f : DimensionDrop p q, unitaryConjugation u₁ ((CStarMatrix.reindexₐ ℂ ℂ e)
      (blockDiagonalHom (fun k => (f : C(Interval,TensorMat p q)) (ξ k rightEndpoint)))) ∈
        (rightAmplification P Q).range) :
    DimensionDrop p q →⋆ₐ[ℂ] DimensionDrop P Q :=
  ((connectingAmbient ξ e u₀ u₁).comp (dimensionDrop p q).subtype).codRestrict
    (dimensionDrop P Q) (fun f => by
      constructor
      · change connectingAmbient ξ e u₀ u₁ (f : C(Interval,TensorMat p q)) leftEndpoint ∈ (leftAmplification P Q).range
        rw [connectingAmbient_zero]
        exact h₀ f
      · change connectingAmbient ξ e u₀ u₁ (f : C(Interval,TensorMat p q)) rightEndpoint ∈ (rightAmplification P Q).range
        rw [connectingAmbient_one]
        exact h₁ f)

end JiangSuConstruction

namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance (priority := 2000) permutationMatrixSemiring : Semiring (CStarMatrix ι ι ℂ) :=
  (inferInstance : CStarAlgebra (CStarMatrix ι ι ℂ)).toSemiring

def permutationUnitary (e : Equiv.Perm ι) : unitary (CStarMatrix ι ι ℂ) :=
  ⟨CStarMatrix.ofMatrix ((e⁻¹).permMatrix ℂ),by
    constructor
    · change ((e⁻¹).permMatrix ℂ).conjTranspose * (e⁻¹).permMatrix ℂ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp
    · change (e⁻¹).permMatrix ℂ * ((e⁻¹).permMatrix ℂ).conjTranspose = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp⟩

lemma permutationUnitary_conjugation (e : Equiv.Perm ι) (a : CStarMatrix ι ι ℂ) :
    unitaryConjugation (permutationUnitary e) a = CStarMatrix.reindexₐ ℂ ℂ e a := by
  change (e⁻¹).permMatrix ℂ * CStarMatrix.ofMatrix.symm a *
    ((e⁻¹).permMatrix ℂ).conjTranspose = Matrix.reindex e e a
  rw [Matrix.conjTranspose_permMatrix]
  change (e⁻¹).toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * e.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

end JiangSuConstruction

namespace JiangSuConstruction
open scoped Kronecker ComplexOrder CStarAlgebra
variable {ι κ ρ σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

local instance (priority := 2000) reindexMatrixSemiring {index : Type*}
    [Fintype index] [DecidableEq index] : Semiring (CStarMatrix index index ℂ) :=
  (inferInstance : CStarAlgebra (CStarMatrix index index ℂ)).toSemiring

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
lemma reindex_trans (e : ι≃κ) (f : κ≃ρ) (a : CStarMatrix ι ι ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
      CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl

lemma reindex_blockDiagonal (e : κ≃ρ) (x : κ→CStarMatrix ι ι ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl ι) e) (blockDiagonalHom x) =
      blockDiagonalHom (fun k => x (e.symm k)) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change Matrix.blockDiagonal (fun z => CStarMatrix.ofMatrix.symm (x z))
    (i,e.symm k) (j,e.symm l) = Matrix.blockDiagonal (fun z => CStarMatrix.ofMatrix.symm (x (e.symm z))) (i,k) (j,l)
  simp only [Matrix.blockDiagonal_apply,Equiv.symm_apply_eq]
  by_cases h : k=l
  · subst l; simp
  · simp [h]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] [DecidableEq σ] in
lemma reindex_kronecker (e : ι≃κ) (f : ρ≃σ) (a : CStarMatrix ι ι ℂ) (b : CStarMatrix ρ ρ ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f)
      (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ CStarMatrix.ofMatrix.symm b)) =
    CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm (CStarMatrix.reindexₐ ℂ ℂ e a) ⊗ₖ
      CStarMatrix.ofMatrix.symm (CStarMatrix.reindexₐ ℂ ℂ f b)) := rfl

omit [DecidableEq ι] in
lemma reindex_left_amplification {P Q : ℕ} (e : ι≃Fin P) (f : κ≃Fin Q)
    (a : CStarMatrix ι ι ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f)
      (CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix κ κ ℂ))) =
      leftAmplification P Q (CStarMatrix.reindexₐ ℂ ℂ e a) := by
  rw [show (1 : Matrix κ κ ℂ)=CStarMatrix.ofMatrix.symm (1 : CStarMatrix κ κ ℂ) from rfl,reindex_kronecker,map_one]
  rfl

omit [DecidableEq κ] in
lemma reindex_right_amplification {P Q : ℕ} (e : ι≃Fin P) (f : κ≃Fin Q)
    (a : CStarMatrix κ κ ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f)
      (CStarMatrix.ofMatrix ((1 : Matrix ι ι ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a)) =
      rightAmplification P Q (CStarMatrix.reindexₐ ℂ ℂ f a) := by
  rw [show (1 : Matrix ι ι ℂ)=CStarMatrix.ofMatrix.symm (1 : CStarMatrix ι ι ℂ) from rfl,reindex_kronecker,map_one]
  rfl

omit [DecidableEq ι] in
lemma permutation_after_reindex (e f : ι≃κ) (a : CStarMatrix ι ι ℂ) :
    unitaryConjugation (permutationUnitary (e.symm.trans f)) (CStarMatrix.reindexₐ ℂ ℂ e a) =
      CStarMatrix.reindexₐ ℂ ℂ f a := by
  rw [permutationUnitary_conjugation]
  ext i j
  change a (e.symm (e (f.symm i))) (e.symm (e (f.symm j))) = a (f.symm i) (f.symm j)
  simp

end JiangSuConstruction

namespace OriginalJiangSu
open JiangSuConstruction

structure Pair where
  p : ℕ
  q : ℕ
  p_gt : 1 < p
  q_gt : 1 < q
  coprime : p.Coprime q

structure Multiplicities (p q : ℕ) where
  k : ℕ
  l : ℕ
  r : ℕ
  s : ℕ
  gamma : ℕ
  delta : ℕ
  lower : ℕ
  upper : ℕ
  middle : ℕ
  k_pos : 0 < k
  l_pos : 0 < l
  r_pos : 0 < r
  s_pos : 0 < s
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  middle_pos : 0 < middle
  lower_eq : lower = l*r
  upper_eq : upper = k*s
  total : lower+upper+middle=k*l
  zero_count : upper+middle=(q*l)*delta
  one_count : lower+middle=(p*k)*gamma
  zero_reduced : p*r+(p*q)*delta=p*k
  one_reduced : q*s+(p*q)*gamma=q*l
  target_coprime : (p*k).Coprime (q*l)
  r_lt : r < q
  s_lt : s < p
  k_prime : Nat.Prime k
  l_prime : Nat.Prime l
  k_large : 4*q ≤ k
  l_large : 4*p ≤ l

lemma mod_pos_of_coprime {k q : ℕ} (hq : 1<q) (h : k.Coprime q) : 0<k%q := by
  by_contra hz
  have hd : q∣k := Nat.dvd_of_mod_eq_zero (by omega)
  have := h.symm.eq_one_of_dvd hd
  omega

lemma arithmetic_multiplicities (x : Pair) (k l : ℕ)
    (hk : 4*x.q≤k) (hl : 4*x.p≤l)
    (hkp : Nat.Prime k) (hlprime : Nat.Prime l)
    (hkq : k.Coprime x.q) (hlp : l.Coprime x.p) (hkl : k.Coprime l) :
    Nonempty (Multiplicities x.p x.q) := by
  have hpgt := x.p_gt
  have hqgt := x.q_gt
  let r := k%x.q
  let s := l%x.p
  let L := l*r
  let U := k*s
  let C := k*l-L-U
  have hrp : 0<r := mod_pos_of_coprime x.q_gt hkq
  have hsp : 0<s := mod_pos_of_coprime x.p_gt hlp
  have hkpos : 0<k := by omega
  have hlpos : 0<l := by omega
  have hr : r<x.q := Nat.mod_lt _ (by omega)
  have hs : s<x.p := Nat.mod_lt _ (by omega)
  have hL : 4*L<k*l := by
    calc 4*L=l*(4*r) := by dsimp [L]; ring
         _<l*k := Nat.mul_lt_mul_of_pos_left (by omega) hlpos
         _=k*l := Nat.mul_comm _ _
  have hU : 4*U<k*l := by
    calc 4*U=k*(4*s) := by dsimp [U]; ring
         _<k*l := Nat.mul_lt_mul_of_pos_left (by omega) hkpos
  have hsum : L+U<k*l := by omega
  have htotal : L+U+C=k*l := by dsimp [C]; omega
  have hkr : r+x.q*(k/x.q)=k := Nat.mod_add_div k x.q
  have hls : s+x.p*(l/x.p)=l := Nat.mod_add_div l x.p
  refine ⟨⟨k,l,r,s,l/x.p,k/x.q,L,U,C,hkpos,hlpos,hrp,hsp,
    Nat.mul_pos hlpos hrp,Nat.mul_pos hkpos hsp,by dsimp [C]; omega,
    rfl,rfl,htotal,?_,?_,?_,?_,?_,hr,hs,hkp,hlprime,hk,hl⟩⟩
  · have he : L+(x.q*l)*(k/x.q)=k*l := by
      calc L+(x.q*l)*(k/x.q)=(r+x.q*(k/x.q))*l := by dsimp [L]; ring
           _=k*l := by rw [hkr]
    omega
  · have he : U+(x.p*k)*(l/x.p)=k*l := by
      calc U+(x.p*k)*(l/x.p)=k*(s+x.p*(l/x.p)) := by dsimp [U]; ring
           _=k*l := by rw [hls]
    omega
  · calc x.p*r+(x.p*x.q)*(k/x.q)=x.p*(r+x.q*(k/x.q)) := by ring
         _=x.p*k := by rw [hkr]
  · calc x.q*s+(x.p*x.q)*(l/x.p)=x.q*(s+x.p*(l/x.p)) := by ring
         _=x.q*l := by rw [hls]
  · exact (x.coprime.mul_right hlp.symm).mul_left (hkq.mul_right hkl)

lemma multiplicities_exists (x : Pair) : Nonempty (Multiplicities x.p x.q) := by
  obtain ⟨k,hk,hkp⟩ := Nat.exists_infinite_primes (4*x.p+4*x.q+2)
  obtain ⟨l,hl,hlp⟩ := Nat.exists_infinite_primes (4*x.p+4*x.q+k+2)
  have hpgt := x.p_gt
  have hqgt := x.q_gt
  have hp : 0<x.p := by omega
  have hq : 0<x.q := by omega
  have hkpos : 0<k := hkp.pos
  have hkq : x.q<k := by nlinarith
  have hlp' : x.p<l := by nlinarith
  have hkl : k<l := by nlinarith
  apply arithmetic_multiplicities x k l (by omega) (by omega) hkp hlp
  · exact hkp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq hkq)
  · exact hlp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hp hlp')
  · exact (hlp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hkpos hkl)).symm

def multiplicities (x : Pair) : Multiplicities x.p x.q :=
  Classical.choice (multiplicities_exists x)

def Pair.next (x : Pair) : Pair :=
  let m := multiplicities x
  ⟨x.p*m.k,x.q*m.l,by nlinarith [x.p_gt,m.k_pos],
    by nlinarith [x.q_gt,m.l_pos],m.target_coprime⟩

def pair : ℕ → Pair
  | 0 => ⟨2,3,by decide,by decide,by decide⟩
  | n+1 => (pair n).next

end OriginalJiangSu

namespace OriginalJiangSu
open JiangSuConstruction
variable {p q : ℕ}

abbrev Index (m : Multiplicities p q) := Fin m.lower ⊕ (Fin m.upper ⊕ Fin m.middle)

def family (m : Multiplicities p q) : Index m → C(Interval,Interval)
  | .inl _ => lowerEigenvalue
  | .inr (.inl _) => upperEigenvalue
  | .inr (.inr _) => ContinuousMap.const _ JiangSuConstruction.midpoint

def sumSwapFirst (α β γ : Type*) : (α ⊕ (β ⊕ γ)) ≃ (β ⊕ (α ⊕ γ)) where
  toFun | .inl a => .inr (.inl a) | .inr (.inl b) => .inl b | .inr (.inr c) => .inr (.inr c)
  invFun | .inl b => .inr (.inl b) | .inr (.inl a) => .inl a | .inr (.inr c) => .inr (.inr c)
  left_inv := by rintro (a|b|c) <;> rfl
  right_inv := by rintro (b|a|c) <;> rfl

def zeroCountEquiv (m : Multiplicities p q) : Fin m.lower ≃ (Fin m.r × Fin m.l) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.lower_eq)

def zeroMidEquiv (m : Multiplicities p q) : (Fin m.upper ⊕ Fin m.middle) ≃
    (Fin m.delta × (Fin q × Fin m.l)) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.zero_count)

def oneCountEquiv (m : Multiplicities p q) : Fin m.upper ≃ (Fin m.s × Fin m.k) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.upper_eq)

def oneMidEquiv (m : Multiplicities p q) : (Fin m.lower ⊕ Fin m.middle) ≃
    (Fin m.gamma × (Fin p × Fin m.k)) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using m.one_count)

def zeroBlockEquiv (m : Multiplicities p q) : Index m ≃
    ((Fin m.r × Fin m.l) ⊕ (Fin m.delta × (Fin q × Fin m.l))) :=
  Equiv.sumCongr (zeroCountEquiv m) (zeroMidEquiv m)

def oneBlockEquiv (m : Multiplicities p q) : Index m ≃
    ((Fin m.s × Fin m.k) ⊕ (Fin m.gamma × (Fin p × Fin m.k))) :=
  (sumSwapFirst _ _ _).trans (Equiv.sumCongr (oneCountEquiv m) (oneMidEquiv m))

lemma family_zero (m : Multiplicities p q) (z) :
    family m ((zeroBlockEquiv m).symm z) leftEndpoint =
      (match z with | Sum.inl _ => leftEndpoint | Sum.inr _ => JiangSuConstruction.midpoint) := by
  cases z with
  | inl z => apply Subtype.ext; norm_num [zeroBlockEquiv,family,lowerEigenvalue,leftEndpoint]
  | inr z =>
    change family m (Sum.inr ((zeroMidEquiv m).symm z)) leftEndpoint=JiangSuConstruction.midpoint
    cases (zeroMidEquiv m).symm z <;> apply Subtype.ext <;>
      norm_num [family,upperEigenvalue,leftEndpoint,JiangSuConstruction.midpoint]

lemma family_one (m : Multiplicities p q) (z) :
    family m ((oneBlockEquiv m).symm z) rightEndpoint =
      (match z with | Sum.inl _ => rightEndpoint | Sum.inr _ => JiangSuConstruction.midpoint) := by
  cases z with
  | inl z => apply Subtype.ext; norm_num [oneBlockEquiv,sumSwapFirst,family,upperEigenvalue,rightEndpoint]
  | inr z =>
    change family m ((sumSwapFirst _ _ _).symm (Sum.inr ((oneMidEquiv m).symm z))) rightEndpoint=JiangSuConstruction.midpoint
    cases (oneMidEquiv m).symm z <;> apply Subtype.ext <;>
      norm_num [sumSwapFirst,family,lowerEigenvalue,rightEndpoint,JiangSuConstruction.midpoint]

lemma family_cover (m : Multiplicities p q) (t : Interval) :
    ∃ j : Index m,∃ s : Interval,family m j s=t := by
  by_cases ht : t.1≤1/2
  · refine ⟨Sum.inl ⟨0,m.lower_pos⟩,⟨2*t.1,by constructor <;> linarith [t.2.1]⟩,?_⟩
    apply Subtype.ext
    change 2*t.1/2=t.1
    ring
  · refine ⟨Sum.inr (Sum.inl ⟨0,m.upper_pos⟩),⟨2*t.1-1,by constructor <;> linarith [t.2.2]⟩,?_⟩
    apply Subtype.ext
    change (2*t.1-1+1)/2=t.1
    ring

end OriginalJiangSu

namespace OriginalJiangSu
open JiangSuConstruction
open scoped Kronecker ComplexOrder CStarAlgebra
variable {p q : ℕ}

def zeroReducedEquiv (m : Multiplicities p q) :
    ((Fin p×Fin m.r) ⊕ ((Fin p×Fin q)×Fin m.delta)) ≃ Fin (p*m.k) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using m.zero_reduced)

def zeroTensorEquiv (m : Multiplicities p q) : (Fin q×Fin m.l) ≃ Fin (q*m.l) :=
  Fintype.equivOfCardEq (by simp)

def oneReducedEquiv (m : Multiplicities p q) :
    ((Fin q×Fin m.s) ⊕ ((Fin p×Fin q)×Fin m.gamma)) ≃ Fin (q*m.l) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using m.one_reduced)

def oneTensorEquiv (m : Multiplicities p q) : (Fin p×Fin m.k) ≃ Fin (p*m.k) :=
  Fintype.equivOfCardEq (by simp)

def zeroIndexEquiv (m : Multiplicities p q) :
    ((Fin p×Fin q)×Index m) ≃ (Fin (p*m.k)×Fin (q*m.l)) :=
  (Equiv.prodCongr (Equiv.refl _) (zeroBlockEquiv m)).trans
    (endpointLeftEquiv.trans (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m)))

def oneIndexEquiv (m : Multiplicities p q) :
    ((Fin p×Fin q)×Index m) ≃ (Fin (p*m.k)×Fin (q*m.l)) :=
  (Equiv.prodCongr (Equiv.refl _) (oneBlockEquiv m)).trans
    (endpointRightEquiv.trans (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m)))

lemma zeroIndex_endpoint (m : Multiplicities p q) (f : DimensionDrop p q) :
    CStarMatrix.reindexₐ ℂ ℂ (zeroIndexEquiv m)
      (blockDiagonalHom (fun z => (f : C(Interval,TensorMat p q)) (family m z leftEndpoint))) ∈
        (leftAmplification (p*m.k) (q*m.l)).range := by
  obtain ⟨a,ha⟩ := f.2.1
  have hfamily : (fun z => (f : C(Interval,TensorMat p q))
      (family m ((zeroBlockEquiv m).symm z) leftEndpoint)) =
      (fun z => match z with
        | Sum.inl _ => leftAmplification p q a
        | Sum.inr _ => (f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint) := by
    funext z
    rw [family_zero]
    cases z
    · exact ha.symm
    · rfl
  unfold zeroIndexEquiv
  rw [reindex_trans,reindex_blockDiagonal,hfamily,reindex_trans]
  change CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m))
    (CStarMatrix.reindexₐ ℂ ℂ endpointLeftEquiv (blockDiagonalHom (fun z => match z with
      | Sum.inl _ => CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))
      | Sum.inr _ => (f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint))) ∈ _
  have he := congrArg (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m)))
    (endpoint_left_regroup (α := Fin m.r) (β := Fin m.delta)
      (ν := Fin m.l) a ((f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint))
  rw [reindex_left_amplification] at he
  refine ⟨CStarMatrix.reindexₐ ℂ ℂ (zeroReducedEquiv m) (endpointReduced a ((f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint)), ?_⟩
  convert he.symm using 1
  · congr 2
    apply congrArg blockDiagonalHom
    funext index
    cases index <;> rfl

lemma oneIndex_endpoint (m : Multiplicities p q) (f : DimensionDrop p q) :
    CStarMatrix.reindexₐ ℂ ℂ (oneIndexEquiv m)
      (blockDiagonalHom (fun z => (f : C(Interval,TensorMat p q)) (family m z rightEndpoint))) ∈
        (rightAmplification (p*m.k) (q*m.l)).range := by
  obtain ⟨a,ha⟩ := f.2.2
  have hfamily : (fun z => (f : C(Interval,TensorMat p q))
      (family m ((oneBlockEquiv m).symm z) rightEndpoint)) =
      (fun z => match z with
        | Sum.inl _ => rightAmplification p q a
        | Sum.inr _ => (f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint) := by
    funext z
    rw [family_one]
    cases z
    · exact ha.symm
    · rfl
  unfold oneIndexEquiv
  rw [reindex_trans,reindex_blockDiagonal,hfamily,reindex_trans]
  change CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m))
    (CStarMatrix.reindexₐ ℂ ℂ endpointRightEquiv (blockDiagonalHom (fun z => match z with
      | Sum.inl _ => CStarMatrix.ofMatrix ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a)
      | Sum.inr _ => (f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint))) ∈ _
  have he := congrArg (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m)))
    (endpoint_right_regroup (α := Fin m.s) (β := Fin m.gamma)
      (ν := Fin m.k) a ((f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint))
  rw [reindex_right_amplification] at he
  refine ⟨CStarMatrix.reindexₐ ℂ ℂ (oneReducedEquiv m) (endpointRightReduced a ((f : C(Interval,TensorMat p q)) JiangSuConstruction.midpoint)), ?_⟩
  convert he.symm using 1
  · congr 2
    apply congrArg blockDiagonalHom
    funext index
    cases index <;> rfl

def step (m : Multiplicities p q) :
    DimensionDrop p q →⋆ₐ[ℂ] DimensionDrop (p*m.k) (q*m.l) :=
  connectingMap (family m) (zeroIndexEquiv m)
    (permutationUnitary ((zeroIndexEquiv m).symm.trans (zeroIndexEquiv m)))
    (permutationUnitary ((zeroIndexEquiv m).symm.trans (oneIndexEquiv m)))
    (fun f => by rw [permutation_after_reindex]; exact zeroIndex_endpoint m f)
    (fun f => by rw [permutation_after_reindex]; exact oneIndex_endpoint m f)

lemma diagonalContinuousHom_injective_cover {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ξ : κ → C(Interval,Interval)) (hc : ∀ t,∃ j,∃ s,ξ j s=t) :
    Function.Injective (diagonalContinuousHom (ι:=ι) ξ) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  obtain ⟨j,s,rfl⟩ := hc t
  exact congrFun (blockDiagonalHom_injective (congrArg
    (fun x : C(Interval,CStarMatrix (ι×κ) (ι×κ) ℂ) => x s) h)) j

lemma connectingAmbient_injective_cover {P Q : ℕ} {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q)) (u₀ u₁ : unitary (TensorMat P Q))
    (hc : ∀ t,∃ j,∃ s,ξ j s=t) : Function.Injective (connectingAmbient ξ e u₀ u₁) :=
  (continuousUnitaryConjugation_injective _).comp
    ((continuousReindex_injective e).comp (diagonalContinuousHom_injective_cover ξ hc))

theorem step_injective (m : Multiplicities p q) : Function.Injective (step m) := by
  intro f g h
  apply Subtype.ext
  apply connectingAmbient_injective_cover _ _ _ _ (family_cover m)
  exact congrArg (fun x : DimensionDrop (p*m.k) (q*m.l) => (x : C(Interval,TensorMat (p*m.k) (q*m.l)))) h

end OriginalJiangSu

namespace OriginalJiangSu
open JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

abbrev Stage (n : ℕ) : Type := ↥(DimensionDrop (pair n).p (pair n).q)

end OriginalJiangSu

namespace OriginalJiangSu
open JiangSuConstruction
open scoped CStarAlgebra ComplexOrder
local instance (priority := 2000) stageSemiring (n : ℕ) : Semiring (Stage n) :=
  (inferInstance : CStarAlgebra (Stage n)).toSemiring

instance stageNontrivial (n : ℕ) : Nontrivial (Stage n) := by
  let : NeZero (pair n).p := ⟨by have := (pair n).p_gt; omega⟩
  let : NeZero (pair n).q := ⟨by have := (pair n).q_gt; omega⟩
  infer_instance

def stageStep (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n+1) := step (multiplicities (pair n))

lemma stageStep_injective (n : ℕ) : Function.Injective (stageStep n) := step_injective _

def system : SequentialCStar.System Stage :=
  SequentialCStar.System.ofSequence stageStep stageStep_injective

abbrev Algebra := system.Limit

instance limitNontrivial : Nontrivial Algebra :=
  (system.inclusion_isometry 0).injective.nontrivial

instance algebraOrder : PartialOrder Algebra := CStarAlgebra.spectralOrder _

instance algebraStarOrder : StarOrderedRing Algebra := CStarAlgebra.spectralOrderedRing _

end OriginalJiangSu

namespace SequentialCStar.System
open Filter Topology
variable {C : ℕ→Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable [∀ n,TopologicalSpace.SeparableSpace (C n)] (S : System C)

 theorem exists_dense_stage_sequence : ∃ d : ℕ→S.Limit,DenseRange d ∧
    d 0=algebraMap ℂ S.Limit Complex.I ∧
    ∀ j,∃ (n : ℕ) (a : C n),S.inclusion n a=d j := by
  classical
  choose c hc using (fun n=>TopologicalSpace.exists_dense_seq (C n))
  let e : ℕ×ℕ→S.Limit := fun z=>S.inclusion z.1 (c z.1 z.2)
  have he : DenseRange e := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n,b,hb⟩ := S.finite_stage_approximation x (half_pos hε)
    obtain ⟨z,⟨k,rfl⟩,hz⟩ := Metric.mem_closure_iff.mp (hc n b) (ε/2) (half_pos hε)
    refine ⟨e (n,k),⟨(n,k),rfl⟩,?_⟩
    have hin := (S.inclusion_isometry n).dist_eq b (c n k)
    change dist x (S.inclusion n (c n k))<ε
    have htri := dist_triangle x (S.inclusion n b) (S.inclusion n (c n k))
    rw [hin] at htri
    simp only [dist_eq_norm] at htri hz ⊢
    linarith
  let d : ℕ→S.Limit
    | 0=>algebraMap ℂ S.Limit Complex.I
    | j+1=>e (Nat.unpair j)
  refine ⟨d,he.mono ?_,rfl,?_⟩
  · rintro x ⟨⟨n,k⟩,rfl⟩
    exact ⟨Nat.pair n k+1,by simp [d,Nat.unpair_pair]⟩
  · intro j
    cases j with
    | zero => exact ⟨0,algebraMap ℂ (C 0) Complex.I,(S.inclusion 0).commutes _⟩
    | succ j => exact ⟨(Nat.unpair j).1,c (Nat.unpair j).1 (Nat.unpair j).2,rfl⟩

end SequentialCStar.System

namespace OriginalJiangSu
open Pureness JiangSuConstruction
open scoped CStarAlgebra ComplexOrder
local instance stageSeparable (n : ℕ) : TopologicalSpace.SeparableSpace (Stage n) := by
  infer_instance

instance algebraSeparable : TopologicalSpace.SeparableSpace Algebra := by
  obtain ⟨d,hd,-,-⟩ := system.exists_dense_stage_sequence
  exact hd.separableSpace (continuous_of_discreteTopology)

end OriginalJiangSu

namespace FourEdgeSurgery
variable {G : Type*} [Group G]

structure Flow (G : Type*) [Group G] where
  toFun : ℝ → G
  zero : toFun 0=1
  add : ∀ r s,toFun (r+s)=toFun r*toFun s

instance : CoeFun (Flow G) (fun _ => ℝ → G) := ⟨Flow.toFun⟩

lemma Flow.map_add (p : Flow G) (r s : ℝ) : p (r+s)=p r*p s := p.add r s

end FourEdgeSurgery

namespace Pureness
open scoped TensorProduct
variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]
variable (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

def commutingTensorClosure : StarSubalgebra ℂ N :=
  (commutingStarTensorHom φ ψ hc).range.topologicalClosure

instance commutingTensorClosure_closed : IsClosed (commutingTensorClosure φ ψ hc : Set N) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance commutingTensorClosureCStarAlgebra : CStarAlgebra (commutingTensorClosure φ ψ hc) :=
  StarSubalgebra.cstarAlgebra _

end Pureness

namespace NonunitalTensor
open scoped CStarAlgebra TensorProduct
variable {A D E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)

def elementarySet : Set E := {x | ∃ a : A,∃ d : D,x=j a*κ d}

def coefficientSpan : Submodule ℂ E := Submodule.span ℂ (elementarySet j κ)

lemma coefficientSpan_mem (a : A) (d : D) : j a*κ d∈coefficientSpan j κ :=
  Submodule.subset_span ⟨a,d,rfl⟩

end NonunitalTensor

namespace NonunitalTensor
open scoped CStarAlgebra TensorProduct
variable {A D E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (j a) (κ d))

include hc

lemma span_mul_mem {x y : E} (hx : x∈coefficientSpan j κ) (hy : y∈coefficientSpan j κ) :
    x*y∈coefficientSpan j κ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,d,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b,e,rfl⟩ := hy
      have he : (j a*κ d)*(j b*κ e)=j (a*b)*κ (d*e) := by
        rw [map_mul,map_mul]
        calc
          _=j a*(κ d*j b)*κ e := by simp only [mul_assoc]
          _=j a*(j b*κ d)*κ e := by rw [(hc b d).symm.eq]
          _=_ := by simp only [mul_assoc]
      rw [he]
      exact coefficientSpan_mem j κ _ _
    | zero => simp
    | add y z hy hz ihy ihz => simpa only [mul_add] using (coefficientSpan j κ).add_mem ihy ihz
    | smul c y hy ih => simpa only [mul_smul_comm] using (coefficientSpan j κ).smul_mem c ih
  | zero => simp
  | add x z hx hz ihx ihz => simpa only [add_mul] using (coefficientSpan j κ).add_mem ihx ihz
  | smul c x hx ih => simpa only [smul_mul_assoc] using (coefficientSpan j κ).smul_mem c ih

lemma span_star_mem {x : E} (hx : x∈coefficientSpan j κ) : star x∈coefficientSpan j κ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,d,rfl⟩ := hx
    rw [star_mul,←map_star,←map_star,←(hc (star a) (star d)).eq]
    exact coefficientSpan_mem j κ _ _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [star_add] using (coefficientSpan j κ).add_mem ihx ihy
  | smul c x hx ih => simpa only [star_smul] using (coefficientSpan j κ).smul_mem (star c) ih

def coefficientAlgebra : NonUnitalStarSubalgebra ℂ E where
  carrier := coefficientSpan j κ
  zero_mem' := (coefficientSpan j κ).zero_mem
  add_mem' := (coefficientSpan j κ).add_mem
  smul_mem' := fun c _ hx => (coefficientSpan j κ).smul_mem c hx
  mul_mem' := span_mul_mem j κ hc
  star_mem' := span_star_mem j κ hc

def tensorIdeal : NonUnitalStarSubalgebra ℂ E := (coefficientAlgebra j κ hc).topologicalClosure

instance tensorIdeal_closed : IsClosed (tensorIdeal j κ hc : Set E) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance : NonUnitalCStarAlgebra (tensorIdeal j κ hc) := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _

end NonunitalTensor

namespace NonunitalTensor
open scoped CStarAlgebra TensorProduct
variable {A D E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
variable (γ : Unitization ℂ A →⋆ₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (γ a) (κ d))

def originalHom : A →⋆ₙₐ[ℂ] E := γ.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)

include hc in
lemma original_commute (a : A) (d : D) : Commute (originalHom γ a) (κ d) := hc (Unitization.inr a) d

end NonunitalTensor

namespace ActualHilbertTensor
open scoped TensorProduct InnerProductSpace
variable (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def TensorSpace := UniformSpace.Completion (H ⊗[ℂ] K)

instance normedAddCommGroup : NormedAddCommGroup (TensorSpace H K) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (H ⊗[ℂ] K)))

instance innerProductSpace : InnerProductSpace ℂ (TensorSpace H K) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion (H ⊗[ℂ] K)))

instance completeSpace : CompleteSpace (TensorSpace H K) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (H ⊗[ℂ] K)))

end ActualHilbertTensor

namespace ActualSpatial
open Pureness UnitalTomsWinter
open scoped CStarAlgebra TensorProduct InnerProductSpace
variable (A D : Type*) [CStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

def Hilbert := ActualHilbertTensor.TensorSpace (StateHilbertSpace A) (StateHilbertSpace D)

instance hilbertNormedAddCommGroup : NormedAddCommGroup (Hilbert A D) :=
  inferInstanceAs (NormedAddCommGroup
    (ActualHilbertTensor.TensorSpace (StateHilbertSpace A) (StateHilbertSpace D)))

instance hilbertInnerProductSpace : InnerProductSpace ℂ (Hilbert A D) :=
  inferInstanceAs (InnerProductSpace ℂ
    (ActualHilbertTensor.TensorSpace (StateHilbertSpace A) (StateHilbertSpace D)))

instance hilbertCompleteSpace : CompleteSpace (Hilbert A D) :=
  inferInstanceAs (CompleteSpace
    (ActualHilbertTensor.TensorSpace (StateHilbertSpace A) (StateHilbertSpace D)))

abbrev Op := Hilbert A D →L[ℂ] Hilbert A D

abbrev repA := stateHilbertRepresentation A

def leftAction : A →⋆ₐ[ℂ] Op A D := spatialLeftHom (K := StateHilbertSpace D) (repA A)

def rightAction : D →⋆ₐ[ℂ] Op A D := spatialRightHom (H := StateHilbertSpace A) (repA D)

lemma commute (a : A) (d : D) : Commute (leftAction A D a) (rightAction A D d) :=
  spatialLeftRight_commute (repA A) (repA D) a d

abbrev Tensor := commutingTensorClosure (N := Op A D) (leftAction A D) (rightAction A D) (commute A D)

instance : PartialOrder (Tensor A D) := CStarAlgebra.spectralOrder _

instance : StarOrderedRing (Tensor A D) := CStarAlgebra.spectralOrderedRing _

def leftHom : A →⋆ₐ[ℂ] Tensor A D := (leftAction A D).codRestrict _ (fun a => by
  apply StarSubalgebra.le_topologicalClosure
  exact ⟨a ⊗ₜ[ℂ] (1 : D),by simp [commutingStarTensorHom_tmul]⟩)

def rightHom : D →⋆ₐ[ℂ] Tensor A D := (rightAction A D).codRestrict _ (fun d => by
  apply StarSubalgebra.le_topologicalClosure
  exact ⟨(1 : A) ⊗ₜ[ℂ] d,by simp [commutingStarTensorHom_tmul]⟩)

lemma homs_commute (a : A) (d : D) : Commute (leftHom A D a) (rightHom A D d) := by
  apply Subtype.ext
  exact commute A D a d

end ActualSpatial

namespace ActualSpatial
open Pureness Filter
open scoped CStarAlgebra TensorProduct
universe u v
variable (A : Type u) (D : Type v) [CStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

lemma commuting_range_eq_span :
    Set.range (commutingStarTensorHom (leftAction A D) (rightAction A D) (commute A D)) =
    (Submodule.span ℂ (Set.range (fun z : A×D => leftAction A D z.1*rightAction A D z.2)) : Set (Op A D)) := by
  let f := commutingStarTensorHom (leftAction A D) (rightAction A D) (commute A D)
  let M := Submodule.span ℂ (Set.range (fun z : A×D => leftAction A D z.1*rightAction A D z.2))
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    change _ ∈ M
    induction z using TensorProduct.inductionOn with
    | tmul a d => exact Submodule.subset_span ⟨(a,d),rfl⟩
    | add x y hx hy => simpa only [map_add] using M.add_mem hx hy
  · change (M : Set (Op A D)) ⊆ f.toLinearMap.range
    apply SetLike.coe_subset_coe.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,d⟩,rfl⟩
    exact ⟨a ⊗ₜ[ℂ] d,rfl⟩

instance tensorSeparable [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace D] : TopologicalSpace.SeparableSpace (Tensor A D) := by
  have hs : TopologicalSpace.IsSeparable
      (Set.range (fun z : A×D => leftAction A D z.1*rightAction A D z.2)) :=
    TopologicalSpace.isSeparable_range (by fun_prop)
  have he : (Tensor A D : Set (Op A D)) =
      closure (Submodule.span ℂ (Set.range (fun z : A×D => leftAction A D z.1*rightAction A D z.2)) : Set (Op A D)) := by
    change closure (Set.range (commutingStarTensorHom (leftAction A D) (rightAction A D) (commute A D))) = _
    rw [commuting_range_eq_span]
  apply TopologicalSpace.IsSeparable.separableSpace
  rw [he]
  exact (hs.span (R := ℂ)).closure

end ActualSpatial

namespace ActualSpatial
open Pureness NonunitalTensor NonunitalGamma Filter
open scoped CStarAlgebra TensorProduct
universe u
variable (A : Type*) (D : Type u) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

abbrev nonunitalIdeal : NonUnitalStarSubalgebra ℂ (Tensor (Unitization ℂ A) D) :=
  tensorIdeal (originalHom (leftHom (Unitization ℂ A) D))
  (rightHom (Unitization ℂ A) D)
  (original_commute (leftHom (Unitization ℂ A) D) (rightHom (Unitization ℂ A) D)
    (homs_commute (Unitization ℂ A) D))

def NonunitalTensor : Type _ := ↥(nonunitalIdeal A D)

instance : NonUnitalCStarAlgebra (NonunitalTensor A D) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra
    (A := Tensor (Unitization ℂ A) D) (nonunitalIdeal A D)

end ActualSpatial

end

end OAI
