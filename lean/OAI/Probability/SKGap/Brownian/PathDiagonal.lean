import Mathlib
import OAI.Probability.SKGap.Localization.TruncationGoodSet
import OAI.Probability.SKGap.Stability.StabilityMatrix
import OAI.Probability.SKGap.Localization.RealQuadratic
import OAI.Probability.SKGap.Matrix.OpNormDiagonal

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathDiagonal (a : ι → ℝ) (z : ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => sqrt z*sqrt (a i))
def pathShift (z q : ℝ) : Matrix ι ι ℝ := diagonal (fun _ => z*q)

lemma stabilityMatrix_path_rep (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {z : ℝ}
    (hz : 0 ≤ z) (q : ℝ) (M : Matrix ι ι ℝ) :
    stabilityMatrix a z q M = 1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z := by
  ext i k
  simp only [stabilityMatrix,Matrix.sub_apply,pathDiagonal,pathShift,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply]
  by_cases hik : i=k
  · subst k
    simp only [↓reduceIte]
    have hz2 := sq_sqrt hz
    have ha2 := sq_sqrt (ha i)
    ring_nf
    rw [hz2,ha2]
    ring
  · simp only [hik,↓reduceIte,sub_zero]
    have hz2 := sq_sqrt hz
    nlinarith only [congrArg (fun x : ℝ => x*sqrt (a i)*M i k*sqrt (a k)) hz2]

lemma pathDiagonal_opNorm {a : ι → ℝ} {A z : ℝ} (_hA0 : 0 ≤ A)
    (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) :
    opNorm (pathDiagonal a z) ≤ sqrt A := by
  apply opNorm_diagonal_le (sqrt_nonneg _)
  intro i
  rw [abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  have hz1 : sqrt z ≤ 1 := by simpa using sqrt_le_sqrt hz.2
  exact (mul_le_mul hz1 (sqrt_le_sqrt (hA i)) (sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma pathShift_opNorm {z q : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) :
    opNorm (pathShift (ι := ι) z q) ≤ q := by
  apply opNorm_diagonal_le hq
  intro i
  rw [abs_of_nonneg (mul_nonneg hz.1 hq)]
  exact (mul_le_mul_of_nonneg_right hz.2 hq).trans_eq (one_mul _)

lemma stabilityMatrix_opNorm {a : ι → ℝ} {A z q R : ℝ} {M : Matrix ι ι ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) (hM : opNorm M ≤ R) :
    opNorm (stabilityMatrix a z q M) ≤ 1+A*(R+q) := by
  rw [stabilityMatrix_path_rep a ha hz.1 q M]
  have hD := pathDiagonal_opNorm hA0 hA hz
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hD 2
    rwa [sq_sqrt hA0] at h
  apply (real_sandwich_stability_norm _ _ _).trans
  apply add_le_add le_rfl
  exact mul_le_mul hd2 (add_le_add hM (pathShift_opNorm hz hq))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) hA0

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma diagonal_mean_bounds {j A : ℝ} {a : ι → ℝ} (hj : 0 ≤ j)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    0 ≤ (j/(Fintype.card ι:ℝ))*∑ i, a i ∧
    (j/(Fintype.card ι:ℝ))*∑ i, a i ≤ j*A := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨mul_nonneg (div_nonneg hj hn.le) (Finset.sum_nonneg (fun i _ => ha i)),?_⟩
  have hs : (∑ i, a i) ≤ (Fintype.card ι:ℝ)*A := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hA i)
  calc
    _ ≤ (j/(Fintype.card ι:ℝ))*((Fintype.card ι:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hj hn.le)
    _ = _ := by field_simp

theorem goe_path_spectral_tail {j A ε : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (hε : 0 ≤ ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    let r := j/(Fintype.card ι:ℝ)
    let q := r*∑ i, a i
    let R := 2*sqrt j+ε
    let c := (1-sqrt j*A)^2/2
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1,
        ¬(opNorm (goeMatrix r g) < R+1 ∧
          c/2 < lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) ∧
          -(2+A*(R+j*A)) < lowerRayleigh (-liftMatrix (stabilityMatrix a z q (goeMatrix r g))))} ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j))+
        Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) := by
  intro r q R c
  let E := {g : MatrixCoordinates ι → ℝ | R < opNorm (goeMatrix r g)}
  let F := {g : MatrixCoordinates ι → ℝ | ∃ z ∈ Icc (0:ℝ) 1, ∃ p : EuclideanSpace ℝ ι,
    matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p < c*‖p‖^2}
  have hc0 : 0 < c := by
    have h : 0 < 1-sqrt j*A := sub_pos.mpr hsub
    dsimp [c]; positivity
  have hq := diagonal_mean_bounds hj.le ha hA
  have hs : {g | ∃ z ∈ Icc (0:ℝ) 1,
        ¬(opNorm (goeMatrix r g) < R+1 ∧
          c/2 < lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) ∧
          -(2+A*(R+j*A)) < lowerRayleigh (-liftMatrix (stabilityMatrix a z q (goeMatrix r g))))} ⊆ E ∪ F := by
    rintro g ⟨z,hz,hfail⟩
    by_contra hn
    have hE : opNorm (goeMatrix r g) ≤ R := by
      by_contra hh
      exact hn (Or.inl (lt_of_not_ge hh))
    have hF (p : EuclideanSpace ℝ ι) : c*‖p‖^2 ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p := by
      by_contra hh
      exact hn (Or.inr ⟨z,hz,p,lt_of_not_ge hh⟩)
    have hl : c ≤ lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) :=
      lowerRayleigh_lift_ge hF
    have hnorm := stabilityMatrix_opNorm ha hA hA0.le hz hq.1 hE
    have hbound : opNorm (stabilityMatrix a z q (goeMatrix r g)) ≤ 1+A*(R+j*A) :=
      hnorm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hq.2) hA0.le))
    have hu := lowerRayleigh_neg_lift_ge (stabilityMatrix a z q (goeMatrix r g))
    apply hfail
    refine ⟨by linarith,by linarith,?_⟩
    linarith
  calc
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real (E ∪ F) := measureReal_mono hs
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real E+
        (gaussianCoordinates (MatrixCoordinates ι)).real F := measureReal_union_le _ _
    _ ≤ _ := add_le_add (goe_norm_tail hj hε)
      (goe_diagonal_matrix_path_tail hj hA0 ha hA hsub herr)

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathBound (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  1+A*ComplexMatrix.fourierMoment f 0*(R+j*A)
def pathLip (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  ComplexMatrix.fl1 f*A^2*(R+j*A)+A*ComplexMatrix.fourierMoment f 0

lemma path_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) :
    0 ≤ pathBound f R j A ∧ 0 ≤ pathLip f R j A := by
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  unfold pathBound pathLip
  exact ⟨by positivity,by positivity⟩

lemma path_constants_bound (f : 𝓢(ℝ,ℂ)) {R j A z q : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (_hj : 0 ≤ j) (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A)
    (hq : 0 ≤ q) (hqA : q ≤ j*A) (hz : z ∈ Icc (0:ℝ) 1) :
    ComplexMatrix.kBound f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathBound f R j A ∧
    ComplexMatrix.kLip f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathLip f R j A ∧
    opNorm (pathDiagonal a z*pathDiagonal a z) ≤ A := by
  have hd := pathDiagonal_opNorm hA0 hA hz
  have hc := (pathShift_opNorm (ι := ι) hz hq).trans hqA
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have hh := pow_le_pow_left₀ (show 0 ≤ opNorm (pathDiagonal a z) from norm_nonneg _) hd 2
    rwa [sq_sqrt hA0] at hh
  have hd4 : opNorm (pathDiagonal a z)^4 ≤ A^2 := by
    calc
      _ = (opNorm (pathDiagonal a z)^2)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hd2 2
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  have hc0 : 0 ≤ R+opNorm (pathShift (ι := ι) z q) := add_nonneg hR (norm_nonneg _)
  unfold ComplexMatrix.kBound ComplexMatrix.kLip ComplexMatrix.gBound ComplexMatrix.gLip pathBound pathLip
  simp only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift]
  refine ⟨?_,?_,?_⟩
  · gcongr
  · gcongr
  · exact (opNorm_mul _ _).trans (by nlinarith)

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma matrixCoordinates_dimension_bound :
    ((Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal : ℝ≥0) ≤
      (Fintype.card ι:ℝ≥0)^2+Fintype.card ι := by
  have hn : 1 ≤ (Fintype.card (MatrixCoordinates ι) : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := MatrixCoordinates ι))
  have he : (1/(2:ℝ≥0∞)).toReal = (1/2:ℝ) := by norm_num
  rw [he]
  have h := NNReal.rpow_le_rpow_of_exponent_le hn (show (1/2:ℝ) ≤ 1 by norm_num)
  simpa [MatrixCoordinates,Fintype.card_sum,Fintype.card_prod,pow_two] using h

lemma path_goodSet_failure {j A ε z : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (hε : 0 < ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) (hz : z ∈ Icc (0:ℝ) 1) :
    let r := j/(Fintype.card ι:ℝ)
    let q := r*∑ i, a i
    let R := 2*sqrt j+ε
    let lo := (1-sqrt j*A)^2/4
    let hi := 2+A*(R+j*A)
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet r (R+1) lo hi (pathDiagonal a z) (pathShift z q))ᶜ ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j))+
        Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) := by
  intro r q R lo hi
  apply le_trans ?_ (goe_path_spectral_tail hj hA0 hε.le ha hA hsub herr)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro g hg
  refine ⟨z,hz,?_⟩
  intro hg'
  apply hg
  rw [stabilityMatrix_path_rep a ha hz.1 q] at hg'
  simpa only [truncationGoodSet,Set.mem_ofPred_eq,lo,hi,R,r,div_div,
    show (2:ℝ)*2=4 by norm_num] using hg'

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
