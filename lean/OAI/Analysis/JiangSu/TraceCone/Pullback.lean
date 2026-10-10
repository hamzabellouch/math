import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.ProductCuts

namespace OAI


noncomputable section
open scoped ENNReal NNReal CStarAlgebra

namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace ExtendedTrace

@[simp] theorem pullback_apply (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    pullback τ f a = τ (Positive.map f a) := rfl

def kernelWeight (f : A →⋆ₙₐ[ℂ] B) : ExtendedTrace A := (zeroIdealWeight B).pullback f

theorem kernelWeight_eq_zero (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    kernelWeight f a = 0 ↔ f a.1 = 0 := zeroIdealWeight_eq_zero B _

theorem kernelWeight_lt_top (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    kernelWeight f a < ∞ ↔ f a.1 = 0 := zeroIdealWeight_lt_top B _

theorem injective_of_surjective_pullback (f : A →⋆ₙₐ[ℂ] B)
    (h : Function.Surjective (fun τ : ExtendedTrace B => τ.pullback f)) :
    Function.Injective f := by
  obtain ⟨τ, hτ⟩ := h (zeroIdealWeight A)
  have hker (x : A) (hx : f x = 0) : x = 0 := by
    have hp : Positive.map f (Positive.starMul x) = Positive.zero := by
      apply Subtype.ext
      simp [Positive.map, Positive.starMul, Positive.zero, _root_.map_mul,
        map_star, hx]
    have hz : zeroIdealWeight A (Positive.starMul x) = 0 := by
      rw [← hτ, pullback_apply, hp]
      exact τ.map_zero
    exact (CStarRing.star_mul_self_eq_zero_iff x).mp
      ((zeroIdealWeight_eq_zero A _).mp hz)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  simp [_root_.map_sub, hxy]

end ExtendedTrace
end TraceCone

end


noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra
open Filter

namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
namespace Positive

lemma map_power (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) (r : ℝ≥0) (hr : 0 < r) :
    map f (power r a) = power r (map f a) := by
  apply Subtype.ext
  change f (a.1 ^ r) = (f a.1) ^ r
  rw [CFC.nnrpow_eq_cfcₙ_real _ _ a.2,
    CFC.nnrpow_eq_cfcₙ_real _ _ (map_nonneg f a.2)]
  exact f.map_cfcₙ (fun t : ℝ => t ^ (r : ℝ)) a.1
    (hf₀ := Real.zero_rpow (by exact_mod_cast hr.ne'))
    (hφ := map_continuous f) (ha := IsSelfAdjoint.of_nonneg a.2)
    (hφa := IsSelfAdjoint.of_nonneg (map_nonneg f a.2))

end Positive
namespace ExtendedTrace

@[simp] theorem rank_zero_trace (a : Positive A) : (0 : ExtendedTrace A).rank a = 0 := by
  simp [rank]

theorem rank_add (τ σ : ExtendedTrace A) (a : Positive A) :
    (τ + σ).rank a = τ.rank a + σ.rank a := by
  exact tendsto_nhds_unique ((τ + σ).tendsto_roots_rank_all a)
    ((τ.tendsto_roots_rank_all a).add (σ.tendsto_roots_rank_all a))

theorem rank_pullback (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    (τ.pullback f).rank a = τ.rank (Positive.map f a) := by
  unfold rank
  congr 1
  funext n
  rw [pullback_apply, Positive.map_power f a _ (Positive.rootExponent_pos n)]

theorem rank_le_liminf_of_canonicalConverges {J : Type*} (L : Filter J) [L.NeBot]
    (u : J → ExtendedTrace A) (τ : ExtendedTrace A) (h : CanonicalConverges L u τ)
    (a : Positive A) : τ.rank a ≤ liminf (fun i => (u i).rank a) L := by
  rw [← τ.rank_normalize a, τ.rank_eq_iSup _ (Positive.normalize_norm_le_one a)]
  apply iSup_le
  intro k
  have hb : ∀ᶠ i in L,
      (u i) (Positive.power (Positive.rootExponent k) (Positive.normalize a)) ≤ (u i).rank a := by
    apply Eventually.of_forall
    intro i
    rw [← (u i).rank_normalize a, (u i).rank_eq_iSup _ (Positive.normalize_norm_le_one a)]
    exact le_iSup
      (fun exponent : ℕ =>
        (u i) (Positive.power (Positive.rootExponent exponent) (Positive.normalize a))) k
  have hcutoff :=
    (h (Positive.power (Positive.rootExponent k) (Positive.normalize a)) 1 (by norm_num)).2
  exact hcutoff.trans (liminf_le_liminf hb)

end ExtendedTrace
end TraceCone

end


noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι]
namespace Positive

lemma exists_starMul_factor (a : Positive A) : ∃ b : A, star b * b = a.1 := by
  refine ⟨CFC.sqrt a.1, ?_⟩
  rw [(CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2]

lemma matrix_diagonal_nonneg (a : Positive (CStarMatrix ι ι A)) (i : ι) : 0 ≤ a.1 i i := by
  obtain ⟨b, hb⟩ := exists_starMul_factor a
  rw [← hb, CStarMatrix.mul_apply]
  apply Finset.sum_nonneg
  intro index _
  rw [CStarMatrix.star_apply]
  exact star_mul_self_nonneg _

def matrixDiagonal (a : Positive (CStarMatrix ι ι A)) (i : ι) : Positive A :=
  ⟨a.1 i i, matrix_diagonal_nonneg a i⟩

lemma matrixDiagonal_continuous (i : ι) :
    Continuous (fun a : Positive (CStarMatrix ι ι A) => matrixDiagonal a i) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Positive (CStarMatrix ι ι A) => a.1 i i)
  exact ((continuous_apply i).comp (continuous_apply i)).comp
    ((CStarMatrix.ofMatrixL (m := ι) (n := ι) (A := A)).symm.continuous.comp continuous_subtype_val)

lemma matrixDiagonal_zero (i : ι) :
    matrixDiagonal (Positive.zero : Positive (CStarMatrix ι ι A)) i = Positive.zero :=
  Subtype.ext rfl

lemma matrixDiagonal_add (a b : Positive (CStarMatrix ι ι A)) (i : ι) :
    matrixDiagonal (add a b) i = add (matrixDiagonal a i) (matrixDiagonal b i) :=
  Subtype.ext rfl

lemma matrixDiagonal_smul (s : ℝ≥0) (a : Positive (CStarMatrix ι ι A)) (i : ι) :
    matrixDiagonal (smul s a) i = smul s (matrixDiagonal a i) := Subtype.ext rfl

lemma matrixDiagonal_starMul (x : CStarMatrix ι ι A) (i : ι) :
    matrixDiagonal (starMul x) i = sum Finset.univ (fun j => starMul (x j i)) := by
  apply Subtype.ext
  simp [matrixDiagonal, starMul, sum, CStarMatrix.mul_apply, CStarMatrix.star_apply]

lemma matrixDiagonal_mulStar (x : CStarMatrix ι ι A) (i : ι) :
    matrixDiagonal (mulStar x) i = sum Finset.univ (fun j => mulStar (x i j)) := by
  apply Subtype.ext
  simp [matrixDiagonal, mulStar, sum, CStarMatrix.mul_apply, CStarMatrix.star_apply]

end Positive
namespace ExtendedTrace

def matrixTrace (τ : ExtendedTrace A) (ι : Type*) [Fintype ι] :
    ExtendedTrace (CStarMatrix ι ι A) where
  toFun a := ∑ i, τ (Positive.matrixDiagonal a i)
  map_zero := by simp [Positive.matrixDiagonal_zero, τ.map_zero]
  map_add a b := by simp only [Positive.matrixDiagonal_add, τ.map_add, Finset.sum_add_distrib]
  map_smul s a := by simp only [Positive.matrixDiagonal_smul, τ.map_smul, Finset.mul_sum]
  tracial x := by
    simp only [Positive.matrixDiagonal_starMul, Positive.matrixDiagonal_mulStar,
      τ.map_sum, τ.tracial]
    exact Finset.sum_comm
  lowerSemicontinuous := lowerSemicontinuous_sum (fun i _ =>
    τ.lowerSemicontinuous.comp (Positive.matrixDiagonal_continuous i))

@[simp] theorem matrixTrace_apply (τ : ExtendedTrace A) (a : Positive (CStarMatrix ι ι A)) :
    τ.matrixTrace ι a = ∑ i, τ (Positive.matrixDiagonal a i) := rfl

end ExtendedTrace
variable [DecidableEq ι]

def matrixCorner (i : ι) : A →⋆ₙₐ[ℂ] CStarMatrix ι ι A where
  toFun a := CStarMatrix.ofMatrix (Matrix.single i i a)
  map_zero' := by
    ext j k
    simp [Matrix.single]
  map_add' a b := by
    change Matrix.single i i (a + b) = Matrix.single i i a + Matrix.single i i b
    exact Matrix.single_add i i a b
  map_smul' s a := by
    ext j k
    by_cases hji : i = j <;> by_cases hki : i = k <;>
      simp [Matrix.single, hji, hki, CStarMatrix.smul_apply]
  map_mul' a b := by
    change Matrix.single i i (a * b) = Matrix.single i i a * Matrix.single i i b
    simp
  map_star' a := by
    change Matrix.single i i (star a) = (Matrix.single i i a).conjTranspose
    exact (Matrix.conjTranspose_single i i a).symm

namespace Positive

lemma matrixDiagonal_corner (i j : ι) (a : Positive A) :
    matrixDiagonal (map (matrixCorner i) a) j = if j = i then a else Positive.zero := by
  split_ifs with hj
  · subst j
    apply Subtype.ext
    simp [matrixDiagonal, map, matrixCorner]
  · apply Subtype.ext
    simp [matrixDiagonal, map, matrixCorner, Matrix.single, Ne.symm hj, Positive.zero]

end Positive
namespace ExtendedTrace

theorem matrixTrace_corner (τ : ExtendedTrace A) (i : ι) (a : Positive A) :
    τ.matrixTrace ι (Positive.map (matrixCorner i) a) = τ a := by
  rw [matrixTrace_apply]
  simp only [Positive.matrixDiagonal_corner]
  simp [apply_ite, τ.map_zero]

lemma matrixTrace_pullback_corner (τ : ExtendedTrace A) (i : ι) :
    (τ.matrixTrace ι).pullback (matrixCorner i) = τ := by
  ext a
  exact τ.matrixTrace_corner i a

theorem matrixRank_corner (τ : ExtendedTrace A) (i : ι) (a : Positive A) :
    (τ.matrixTrace ι).rank (Positive.map (matrixCorner i) a) = τ.rank a := by
  rw [← rank_pullback, matrixTrace_pullback_corner]

end ExtendedTrace

end TraceCone

end

end OAI
