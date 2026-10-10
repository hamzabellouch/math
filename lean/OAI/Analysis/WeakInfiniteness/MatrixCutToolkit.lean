import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzComparison
import OAI.Analysis.WeakInfiniteness.RectangularPolar
import OAI.Analysis.WeakInfiniteness.SpectralCut

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

local instance matrixRealModuleToolkit {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def diagonalHom (n : ℕ) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := diagonalCopies n
  map_add' a b := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.add_apply]
    split_ifs <;> simp
  map_zero' := by ext i j; simp [diagonalCopies]
  map_mul' a b := by
    change Matrix.diagonal (fun _ : Fin n => a*b) =
      Matrix.diagonal (fun _ : Fin n => a)*Matrix.diagonal (fun _ : Fin n => b)
    rw [Matrix.diagonal_mul_diagonal]
  map_smul' c a := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.smul_apply]
    split_ifs <;> simp
  map_star' a := by
    ext i j
    simp only [diagonalCopies, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply,
      CStarMatrix.star_eq_conjTranspose, CStarMatrix.conjTranspose_apply]
    split_ifs <;> simp_all

lemma diagonalCopies_nonneg (n : ℕ) {a : A} (ha : 0 ≤ a) : 0 ≤ diagonalCopies n a :=
by
  have he : diagonalCopies n a = star ((diagonalHom n) (CFC.sqrt a))*
      (diagonalHom n) (CFC.sqrt a) := by
    rw [← map_star, ← map_mul, (CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rfl
  rw [he]
  exact star_mul_self_nonneg _

lemma diagonalCopies_cfc (n : ℕ) (a : A) (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    diagonalCopies n (cfcₙ f a) = cfcₙ f (diagonalCopies n a) :=
  (diagonalHom n).map_cfcₙ f a hf.continuousOn hf0 (by fun_prop) ha (ha.map (diagonalHom n))

omit [PartialOrder A] [StarOrderedRing A] in
lemma left_identity_on_hereditary (e h : A) (hh : IsSelfAdjoint h) (he : e*h=h)
    {x : A} (hx : x ∈ hereditarySubalgebra h hh) : e*x=x := by
  have hclosed : IsClosed {x : A | e*x=x} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal ?_ hclosed hx
  rintro _ ⟨b,rfl⟩
  change e*(h*b*h)=h*b*h
  rw [← mul_assoc, ← mul_assoc, he]

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_sub_mul {m n k : Type*} [Fintype n]
    (u v : CStarMatrix m n A) (w : CStarMatrix n k A) : (u-v)*w=u*w-v*w :=
  Matrix.sub_mul _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_mul_sub {m n k : Type*} [Fintype n]
    (u : CStarMatrix m n A) (v w : CStarMatrix n k A) : u*(v-w)=u*v-u*w :=
  Matrix.mul_sub _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_star_sub {m n : Type*} (u v : CStarMatrix m n A) :
    (u-v).conjTranspose=u.conjTranspose-v.conjTranspose := Matrix.conjTranspose_sub _ _

lemma rectangular_left_identity_of_range {m n : Type*} [Fintype m] [Fintype n]
    (e : CStarMatrix m m A) (u : CStarMatrix m n A)
    (he : e*(u*u.conjTranspose)=u*u.conjTranspose) : e*u=u := by
  let v := e*u-u
  have hvu : v*u.conjTranspose=0 := by
    change (e*u-u)*u.conjTranspose=0
    rw [rectangular_sub_mul, rectangular_mul_assoc, he, sub_self]
  have hv : v*v.conjTranspose=0 := by
    change v*(e*u-u).conjTranspose=0
    rw [rectangular_star_sub, rectangular_star_mul, rectangular_mul_sub,
      ← rectangular_mul_assoc, hvu]
    simp only [sub_zero]
    exact Matrix.zero_mul _
  have hn := rectangular_norm_range v
  rw [hv, norm_zero] at hn
  have hh : ‖v‖=0 := by nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

lemma rectangular_left_identity_of_hereditary_range {m n : Type*} [Fintype m] [Fintype n]
    (e h : CStarMatrix m m A) (u : CStarMatrix m n A) (hh : IsSelfAdjoint h)
    (he : e*h=h) (hu : u*u.conjTranspose ∈ hereditarySubalgebra h hh) : e*u=u :=
  rectangular_left_identity_of_range e u (left_identity_on_hereditary e h hh he hu)

def positiveCut (δ : ℝ) (a : A) : A := cfcₙ (fun s : ℝ => max (s-δ) 0) a

lemma positiveCut_nonneg (δ : ℝ) (a : A) : 0 ≤ positiveCut δ a :=
  cfcₙ_nonneg (fun _ _ => le_max_right _ _)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_mul_positiveCut (a : A) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 2*θ ≤ δ) :
    cfcₙ (spectralRamp θ) a*positiveCut δ a = positiveCut δ a := by
  have hf0 : max (0-δ) 0 = 0 := by rw [max_eq_right]; linarith
  rw [positiveCut, ← cfcₙ_mul (spectralRamp θ) (fun s : ℝ => max (s-δ) 0) a
    (continuous_spectralRamp θ).continuousOn (spectralRamp_eq_zero hθ hθ.le)
    (by fun_prop) hf0]
  congr 1
  funext s
  by_cases hs : s ≤ δ
  · rw [max_eq_right (by linarith : s-δ ≤ 0), mul_zero]
  · rw [spectralRamp_eq_one hθ (by linarith), one_mul]

end

end WeakPureInfiniteness
end

end OAI
