import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixMask (n : ℕ) {m : ℕ} (M : FinMatrix A m) : FinMatrix A m :=
  CStarMatrix.ofMatrix (fun i j => if i.val < n ∧ j.val < n then M i j else 0)

@[simp] lemma matrixMask_apply [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M : FinMatrix A m) (i j : Fin m) :
    matrixMask n M i j = if i.val < n ∧ j.val < n then M i j else 0 := rfl

lemma matrixMask_eq_self [PartialOrder A] [StarOrderedRing A]
    {n m : ℕ} (h : m ≤ n) (M : FinMatrix A m) : matrixMask n M = M := by
  apply CStarMatrix.ext; intro i j
  simp [i.isLt.trans_le h, j.isLt.trans_le h]

@[simp] lemma matrixMask_zero [PartialOrder A] [StarOrderedRing A]
    (n m : ℕ) : matrixMask (A := A) n (0 : FinMatrix A m) = 0 := by
  apply CStarMatrix.ext; intro i j; simp
@[simp] lemma matrixMask_add [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M N : FinMatrix A m) :
    matrixMask n (M+N) = matrixMask n M + matrixMask n N := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.add_apply]; split_ifs <;> simp
@[simp] lemma matrixMask_smul [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (c : ℂ) (M : FinMatrix A m) :
    matrixMask n (c • M) = c • matrixMask n M := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.smul_apply]; split_ifs <;> simp
@[simp] lemma matrixMask_sub [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M N : FinMatrix A m) :
    matrixMask n (M-N) = matrixMask n M - matrixMask n N := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.sub_apply]; split_ifs <;> simp

def matrixUnitize (m : ℕ) : FinMatrix A m →⋆ₙₐ[ℂ] FinMatrix (Unitization ℂ A) m :=
  CStarMatrix.mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ A)

lemma matrixUnitize_injective [PartialOrder A] [StarOrderedRing A]
    (m : ℕ) : Function.Injective (matrixUnitize (A := A) m) := by
  intro M N h
  apply CStarMatrix.ext; intro i j
  exact Unitization.inr_injective (congrArg (fun P : FinMatrix (Unitization ℂ A) m => P i j) h)

@[simp] lemma matrixUnitize_norm [PartialOrder A] [StarOrderedRing A]
    (m : ℕ) (M : FinMatrix A m) : ‖matrixUnitize m M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixUnitize_injective m) M

def matrixMaskProjection (n m : ℕ) : FinMatrix (Unitization ℂ A) m :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun i => if i.val < n then 1 else 0))

lemma matrixMaskProjection_star [PartialOrder A] [StarOrderedRing A]
    (n m : ℕ) : star (matrixMaskProjection (A := A) n m) = matrixMaskProjection n m := by
  apply CStarMatrix.ext; intro i j
  simp [matrixMaskProjection, Matrix.diagonal, CStarMatrix.star_apply]
  split_ifs <;> simp_all
  omega

lemma matrixMaskProjection_mul [PartialOrder A] [StarOrderedRing A]
    (n m : ℕ) : matrixMaskProjection (A := A) n m * matrixMaskProjection n m = matrixMaskProjection n m := by
  change (Matrix.diagonal (fun i : Fin m => if i.val < n then (1 : Unitization ℂ A) else 0)) *
      Matrix.diagonal (fun i : Fin m => if i.val < n then (1 : Unitization ℂ A) else 0) =
    Matrix.diagonal (fun i : Fin m => if i.val < n then (1 : Unitization ℂ A) else 0)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

lemma matrixMaskProjection_norm_le [PartialOrder A] [StarOrderedRing A]
    (n m : ℕ) : ‖matrixMaskProjection (A := A) n m‖ ≤ 1 := by
  exact IsStarProjection.norm_le _
    ⟨matrixMaskProjection_mul n m, matrixMaskProjection_star n m⟩

lemma matrixMask_unitize [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M : FinMatrix A m) :
    matrixUnitize m (matrixMask n M) = matrixMaskProjection n m * matrixUnitize m M * matrixMaskProjection n m := by
  apply CStarMatrix.ext; intro i j
  let d : Fin m → Unitization ℂ A := fun i => if i.val < n then 1 else 0
  let N : Matrix (Fin m) (Fin m) (Unitization ℂ A) := fun i j => (M i j : Unitization ℂ A)
  change ((matrixMask n M) i j : Unitization ℂ A) = (Matrix.diagonal d * N * Matrix.diagonal d) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [matrixMask_apply, d, N]
  split_ifs <;> simp_all

theorem matrixMask_norm_le [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M : FinMatrix A m) : ‖matrixMask n M‖ ≤ ‖M‖ := by
  rw [← matrixUnitize_norm m (matrixMask n M), matrixMask_unitize]
  have hp := matrixMaskProjection_norm_le (A := A) n m
  calc
    _ ≤ ‖matrixMaskProjection (A := A) n m‖ * ‖matrixUnitize m M‖ * ‖matrixMaskProjection (A := A) n m‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖M‖ := by
      rw [matrixUnitize_norm]
      nlinarith [norm_nonneg (matrixMaskProjection (A := A) n m), norm_nonneg M,
        mul_le_mul_of_nonneg_right hp (norm_nonneg M)]

lemma matrixMask_successor [PartialOrder A] [StarOrderedRing A]
    (n m : ℕ) (M : FinMatrix A m) :
    matrixMask n (matrixSuccessor m M) = matrixSuccessor m (matrixMask n M) := by
  apply CStarMatrix.ext; intro i j
  change (if i.val < n ∧ j.val < n then
      Fin.lastCases (0 : A) (fun i => Fin.lastCases (0 : A) (M i) j) i else (0 : A)) =
    Fin.lastCases (0 : A) (fun i => Fin.lastCases (0 : A) (matrixMask n M i) j) i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma matrixMask_inclusion [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m k : ℕ} (h : m ≤ k) (M : FinMatrix A m) :
    matrixMask n (matrixInclusion h M) = matrixInclusion h (matrixMask n M) := by
  change matrixMask n (matrixPad h M) = matrixPad h (matrixMask n M)
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k h ih => rw [matrixPad_succ h, matrixPad_succ h, matrixMask_successor, ih]
end TraceCone
end


noncomputable section
open scoped ENNReal Topology CStarAlgebra
open Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixFamilyMask (n : ℕ) : BoundedFamilies (FinMatrix A) →ₗ[ℂ] BoundedFamilies (FinMatrix A) where
  toFun x := ⟨fun m => matrixMask n (x m), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨m,rfl⟩
    exact (matrixMask_norm_le n (x m)).trans (BoundedFamilies.norm_coordinate_le x m)⟩⟩
  map_add' x y := by apply lp.ext; funext m; exact matrixMask_add n (x m) (y m)
  map_smul' c x := by apply lp.ext; funext m; exact matrixMask_smul n c (x m)

lemma matrixFamilyMask_vanishing (n : ℕ) {x : BoundedFamilies (FinMatrix A)}
    (hx : x ∈ BoundedFamilies.vanishing) : matrixFamilyMask n x ∈ BoundedFamilies.vanishing := by
  change Tendsto (fun m => ‖matrixMask n (x m)‖) atTop (𝓝 0)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => matrixMask_norm_le n (x m)) hx

def matrixQuotientMask (n : ℕ) : FamilyQuotient (FinMatrix A) →ₗ[ℂ] FamilyQuotient (FinMatrix A) :=
  (BoundedFamilies.vanishing (A := FinMatrix A)).mapQ BoundedFamilies.vanishing
    (matrixFamilyMask n) (fun _ hx => matrixFamilyMask_vanishing n hx)

@[simp] lemma matrixQuotientMask_mk (n : ℕ) (x : BoundedFamilies (FinMatrix A)) :
    matrixQuotientMask n (FamilyQuotient.mk x) = FamilyQuotient.mk (matrixFamilyMask n x) := rfl

lemma matrixQuotientMask_norm_le (n : ℕ) (x : FamilyQuotient (FinMatrix A)) :
    ‖matrixQuotientMask n x‖ ≤ ‖x‖ := by
  obtain ⟨x,rfl⟩ := FamilyQuotient.mk_surjective x
  rw [matrixQuotientMask_mk, FamilyQuotient.norm_mk_eq_limsup, FamilyQuotient.norm_mk_eq_limsup]
  exact limsup_le_limsup (Eventually.of_forall (fun m => matrixMask_norm_le n (x m)))
    (BoundedFamilies.norm_cobounded _) (BoundedFamilies.norm_bounded x)

def matrixQuotientMaskCLM (n : ℕ) : FamilyQuotient (FinMatrix A) →L[ℂ] FamilyQuotient (FinMatrix A) :=
  (matrixQuotientMask n).mkContinuous 1 (fun x => by simpa using matrixQuotientMask_norm_le n x)

lemma matrixQuotientMask_stage (n m : ℕ) (M : FinMatrix A m) :
    matrixQuotientMask n (matrixStage m M) = matrixStage m (matrixMask n M) := by
  apply FamilyQuotient.mk_eq_of_eventually_eq
  filter_upwards [eventually_ge_atTop m] with k hk
  change matrixMask n (if h : m ≤ k then matrixInclusion h M else 0) =
    (if h : m ≤ k then matrixInclusion h (matrixMask n M) else 0)
  simp [hk, matrixMask_inclusion]

lemma matrixQuotientMask_mem_limit (n : ℕ) (x : MatrixLimit A) :
    matrixQuotientMask n x.1 ∈ matrixLimitAlgebra A := by
  have hc : Continuous (matrixQuotientMask (A := A) n) := (matrixQuotientMaskCLM n).continuous
  apply map_mem_closure hc x.2
  rintro y ⟨m,M,rfl⟩
  exact ⟨m,matrixMask n M,(matrixQuotientMask_stage n m M).symm⟩

def matrixCompression (n : ℕ) : MatrixLimit A →ₗ[ℂ] MatrixLimit A where
  toFun x := ⟨matrixQuotientMask n x.1, matrixQuotientMask_mem_limit n x⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul _ c x.1)

lemma matrixCompression_norm_le (n : ℕ) (x : MatrixLimit A) : ‖matrixCompression n x‖ ≤ ‖x‖ :=
  matrixQuotientMask_norm_le n x.1

lemma matrixCompression_stage (n m : ℕ) (M : FinMatrix A m) :
    matrixCompression n (matrixLimitStage m M) = matrixLimitStage m (matrixMask n M) :=
  Subtype.ext (matrixQuotientMask_stage n m M)

private theorem contractions_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : ℕ → E →ₗ[ℂ] E) (hC : ∀ n x, ‖C n x‖ ≤ ‖x‖) (x : E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : E, ‖x-y‖ < ε ∧ ∃ m, ∀ n, m ≤ n → C n y = y) :
    Tendsto (fun n => C n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,m,hm⟩ := happrox (ε/2) (by linarith)
  refine ⟨m,fun n hn => ?_⟩
  have hid : C n x - x = C n (x-y) + (y-x) := by
    rw [map_sub,hm n hn]
    abel
  rw [dist_eq_norm,hid]
  calc
    _ ≤ ‖C n (x-y)‖ + ‖y-x‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + ‖y-x‖ := add_le_add (hC n _) le_rfl
    _ < ε := by rw [norm_sub_rev y x]; linarith

theorem matrixCompression_tendsto (x : MatrixLimit A) :
    Tendsto (fun n => matrixCompression n x) atTop (𝓝 x) := by
  apply contractions_tendsto matrixCompression matrixCompression_norm_le x
  intro ε hε
  obtain ⟨m,M,hM⟩ := matrixLimit_finite_approximation x hε
  refine ⟨matrixLimitStage m M,hM,m,fun n hn => ?_⟩
  rw [matrixCompression_stage, matrixMask_eq_self hn]
end TraceCone
end

end OAI
