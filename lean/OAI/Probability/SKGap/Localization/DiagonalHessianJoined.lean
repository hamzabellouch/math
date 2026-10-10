import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalTolerance

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_half_holder {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |sqrt a-sqrt b| ≤ sqrt |a-b| := by
  have hsq : (sqrt a-sqrt b)^2 ≤ |a-b| := by
    rcases le_total a b with hab | hab
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      have hp := mul_nonneg (sqrt_nonneg a) (sub_nonneg.mpr (sqrt_le_sqrt hab))
      nlinarith [sq_sqrt ha,sq_sqrt hb]
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      have hp := mul_nonneg (sqrt_nonneg b) (sub_nonneg.mpr (sqrt_le_sqrt hab))
      nlinarith [sq_sqrt ha,sq_sqrt hb]
  simpa only [sqrt_sq_eq_abs] using sqrt_le_sqrt hsq

def diagonalRoot (a : ι → ℝ) : Matrix ι ι ℝ := diagonal (fun i => sqrt (a i))
def diagonalHessian (a : ι → ℝ) (K : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  1-diagonalRoot a*K*diagonalRoot a

lemma diagonalRoot_norm {a : ι → ℝ} {M : ℝ} (_hM : 0 ≤ M) (ha : ∀ i,a i ≤ M) :
    ‖diagonalRoot a‖ ≤ sqrt M := by
  rw [diagonalRoot,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (sqrt_nonneg M)).mpr
    (fun i => by rw [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]; exact sqrt_le_sqrt (ha i))

lemma diagonalRoot_half_holder {a b : ι → ℝ} {ζ : ℝ} (_hζ : 0 ≤ ζ)
    (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (hab : ∀ i,|a i-b i| ≤ ζ) :
    ‖diagonalRoot a-diagonalRoot b‖ ≤ sqrt ζ := by
  rw [diagonalRoot,diagonalRoot,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (sqrt_nonneg ζ)).mpr (fun i =>
    (sqrt_half_holder (ha i) (hb i)).trans (sqrt_le_sqrt (hab i)))

theorem diagonalHessian_half_holder {a b : ι → ℝ} {M ζ L : ℝ}
    (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hL : 0 ≤ L)
    (ha : ∀ i,a i ∈ Set.Icc 0 M) (hb : ∀ i,b i ∈ Set.Icc 0 M)
    (hab : ∀ i,|a i-b i| ≤ ζ) (K : Matrix ι ι ℝ) (hK : ‖K‖ ≤ L) :
    ‖diagonalHessian a K-diagonalHessian b K‖ ≤ 2*sqrt M*L*sqrt ζ := by
  have hD := diagonalRoot_norm hM (fun i => (ha i).2)
  have hE := diagonalRoot_norm hM (fun i => (hb i).2)
  have hDE := diagonalRoot_half_holder hζ (fun i => (ha i).1) (fun i => (hb i).1) hab
  have heq : diagonalHessian a K-diagonalHessian b K=
      -((diagonalRoot a-diagonalRoot b)*K*diagonalRoot a+
        diagonalRoot b*K*(diagonalRoot a-diagonalRoot b)) := by
    simp only [diagonalHessian,Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [heq,norm_neg]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans
  have hb₁ : ‖(diagonalRoot a-diagonalRoot b)*K‖ ≤ sqrt ζ*L :=
    (norm_mul_le _ _).trans (mul_le_mul hDE hK (norm_nonneg _) (sqrt_nonneg _))
  have hb₂ : ‖diagonalRoot b*K‖ ≤ sqrt M*L :=
    (norm_mul_le _ _).trans (mul_le_mul hE hK (norm_nonneg _) (sqrt_nonneg _))
  apply (add_le_add (mul_le_mul hb₁ hD (norm_nonneg _) (by positivity))
    (mul_le_mul hb₂ hDE (norm_nonneg _) (by positivity))).trans_eq
  ring

lemma diagonalHessian_hermitian (a : ι → ℝ) {K : Matrix ι ι ℝ} (hK : K.IsHermitian) :
    (diagonalHessian a K).IsHermitian := by
  unfold diagonalHessian Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
    diagonalRoot,Matrix.diagonal_conjTranspose,star_trivial,hK.eq]
  simp only [Matrix.mul_assoc]

lemma matrix_quadratic_op_bound (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (M*ᵥx)| ≤ ‖M‖*(x⬝ᵥx) := by
  let y : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  have hh := abs_real_inner_le_norm y (M.toEuclideanLin.toContinuousLinearMap y)
  have hn := M.toEuclideanLin.toContinuousLinearMap.le_opNorm y
  have hin : inner ℝ y (M.toEuclideanLin.toContinuousLinearMap y)=x⬝ᵥ(M*ᵥx) := by
    change (∑ i,(M*ᵥx) i*x i)=∑ i,x i*(M*ᵥx) i
    apply Finset.sum_congr rfl; intro i _; ring
  have hy : ‖y‖^2=x⬝ᵥx := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [y,dotProduct,pow_two]
  rw [hin] at hh
  calc
    _ ≤ ‖y‖*‖M.toEuclideanLin.toContinuousLinearMap y‖ := hh
    _ ≤ ‖y‖*(‖M‖*‖y‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by rw [← hy]; ring

theorem hermitian_margin_transfer {S T : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (_hT : T.IsHermitian) {c d : ℝ} (hd : ‖S-T‖ ≤ d)
    (hc : (T-c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (S-(c-d) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩
  · exact hS.sub (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))
  · intro x
    have hq := matrix_quadratic_op_bound (S-T) x
    have hp := hc.dotProduct_mulVec_nonneg x
    have hxx : 0 ≤ x⬝ᵥx := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have hbd := mul_le_mul_of_nonneg_right hd hxx
    simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      dotProduct_sub,dotProduct_smul,smul_eq_mul] at hp hq ⊢
    rcases abs_le.mp (hq.trans hbd) with ⟨hl,_⟩
    nlinarith only [hp,hl]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalConditionalMiddle {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let u := (empiricalUnit y q).ofLp
  let X := (empiricalGramColumns y (scalarD j p) s 0).ofLp
  let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
  conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p)
    (j*scalarBMoment p.1) (conditionalKappa j p) (conditionalEll j p) u Z g+
    j • vecMulVec X X+(2*j*q) • vecMulVec u u-
    (j*scalarBMoment p.1) • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma empirical_columns_one {n : ℕ} (y : Fin n → ℝ) (d s : ℝ) {q : ℝ}
    (hq : 0 < q) : sqrt q • (empiricalUnit y q).ofLp=(empiricalGramColumns y d s 1).ofLp := by
  have hsq : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  ext i
  simp only [empiricalUnit,empiricalGramColumns,gramCoordinates,WithLp.ofLp_toLp,
    Pi.smul_apply,smul_eq_mul,Matrix.cons_val,sqrt_mul (Nat.cast_nonneg n)]
  field_simp

lemma empirical_columns_two {n : ℕ} (y : Fin n → ℝ) (d : ℝ) {s : ℝ}
    (hs : 0 < s) : (sqrt s)⁻¹ • (sqrt s • (empiricalGramColumns y d s 2).ofLp)=
      (empiricalGramColumns y d s 2).ofLp := by
  rw [inv_smul_smul₀ (sqrt_pos.mpr hs).ne']

lemma empirical_columns_matrix {n : ℕ} (y : Fin n → ℝ) (d : ℝ) {q s : ℝ}
    (hq : 0 < q) (hs : 0 < s) (N : Fin n → ℝ) :
    conditionalColumns (empiricalGramColumns y d s 0).ofLp
      (sqrt q • (empiricalUnit y q).ofLp)
      ((sqrt s)⁻¹ • (sqrt s • (empiricalGramColumns y d s 2).ofLp)) N=
      extendColumns (fun r=>(empiricalGramColumns y d s r).ofLp) N := by
  rw [empirical_columns_one y d s hq,empirical_columns_two y d hs]
  ext i k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => rfl

lemma pathDiagonal_one_eq_sqrt {n : ℕ} (a : Fin n → ℝ) : pathDiagonal a 1=diagonalRoot a := by
  simp only [pathDiagonal,diagonalRoot,Real.sqrt_one,one_mul]

lemma pathDiagonal_sq {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i,0 ≤ a i) :
    pathDiagonal a 1*pathDiagonal a 1=diagonal a := by
  rw [pathDiagonal_one_eq_sqrt,diagonalRoot,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp only [← pow_two,Real.sq_sqrt (ha i)]

theorem conditionalEmpiricalCore_eq_hessian {n : ℕ} [NeZero n] (j t σ : ℝ)
    (a y : Fin n → ℝ) (g : MatrixCoordinates (Fin n) → ℝ)
    (ha : ∀ i,0 ≤ a i) (hq : 0 < scalarQMoment (empiricalLaw y))
    (hs : 0 < scalarS j (empiricalLaw y,t,σ)) (hBA : 0 < j/(n:ℝ)*∑ i,a i) :
    conditionalEmpiricalCore j t σ a y g=diagonalHessian a (empiricalConditionalMiddle j t σ y g) := by
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let BA := j/(n:ℝ)*∑ i,a i
  have hh := conditional_hessian_rank_form (j/(n:ℝ)) j (scalarA j p) B
    (conditionalKappa j p) (conditionalEll j p) (q := q) (s := s)
    (S := s+j*q) hq hs hBA
    (empiricalGramColumns y (scalarD j p) s 0).ofLp
    (empiricalUnit y q).ofLp
    (sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp)
    (pathDiagonal a 1) g
  dsimp only at hh
  rw [empirical_columns_matrix y (scalarD j p) hq hs,pathDiagonal_sq a ha] at hh
  have hB : B+(BA-B)=BA := by ring
  have hbil : goeBilinear (j/(n:ℝ)) (empiricalUnit y q).ofLp (empiricalUnit y q).ofLp g=
      matrixBilinear (goeMatrix (j/(n:ℝ)) g) (empiricalUnit y q) (empiricalUnit y q) := by
    rw [matrixBilinear_eq_pair]
    rfl
  rw [hbil] at hh
  symm
  convert hh using 1
  · simp only [diagonalHessian,empiricalConditionalMiddle,p,q,s,B,pathDiagonal_one_eq_sqrt,
      Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_one]
    abel
  · simp only [conditionalEmpiricalCore,conditionalBase,conditionalUpdateColumns,
      conditionalMeanData,conditionalScalarData,p,q,s,B,BA] at *
    rw [hB]
end SKGap
end
end

end OAI
