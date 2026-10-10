import Mathlib
import OAI.Probability.SKGap.Localization.DiagonalHessianJoined
import OAI.Probability.SKGap.Localization.ConditionalEmpiricalLaw
import OAI.Probability.SKGap.Entropy.ConditionalBadSet

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarQMoment_empirical_overlap {n : ℕ} [NeZero n] (y : Fin n → ℝ) :
    scalarQMoment (empiricalLaw y)=overlap y := by
  simp only [scalarQMoment,integral_empiricalLaw,Fintype.card_fin,overlap,magnetization,
    div_eq_mul_inv,mul_comm]

lemma empirical_columns_zero_outer {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d s j : ℝ) :
    j • vecMulVec (empiricalGramColumns y d s 0).ofLp (empiricalGramColumns y d s 0).ofLp=
      (j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hn : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)).ne'
  ext i k
  simp only [empiricalGramColumns,gramCoordinates,Matrix.cons_val,WithLp.ofLp_toLp,
    Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,mul_one]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma empirical_unit_outer {n : ℕ} [NeZero n] (y : Fin n → ℝ) {q : ℝ} (hq : 0 < q) (j : ℝ) :
    (2*j*q) • vecMulVec (empiricalUnit y q).ofLp (empiricalUnit y q).ofLp=
      (2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hc : sqrt ((n:ℝ)*q) ≠ 0 := (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq)).ne'
  ext i k
  simp only [empiricalUnit,WithLp.ofLp_toLp,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,magnetization]
  field_simp
  rw [Real.sq_sqrt (mul_nonneg hq.le (Nat.cast_nonneg n))]
  ring

lemma empiricalConditionalMiddle_literal {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) (g : MatrixCoordinates (Fin n) → ℝ) :
    empiricalConditionalMiddle j t σ y g=
      plantedInteraction j (empiricalConditionalGoe j t σ y g)+
      (2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y)-
      onsager j y • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  dsimp only [empiricalConditionalMiddle,empiricalConditionalGoe,plantedInteraction]
  rw [empirical_columns_zero_outer,empirical_unit_outer y hq,
    scalarBMoment,scalarQMoment_empirical_overlap]
  rfl

lemma fieldHessian_diagonalHessian {n : ℕ} (j : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (y a : Fin n → ℝ) :
    fieldHessian j (plantedInteraction j W) y a = diagonalHessian a
      (plantedInteraction j W+(2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y)-
        onsager j y • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  ext i k
  simp only [fieldHessian,hessianCore,diagonalHessian,diagonalRoot,Matrix.sub_apply,
    Matrix.one_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]
  ring

lemma empiricalConditionalGoe_hessian {n : ℕ} [NeZero n] (j t σ : ℝ) (y a : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) (g : MatrixCoordinates (Fin n) → ℝ) :
    fieldHessian j (plantedInteraction j (empiricalConditionalGoe j t σ y g)) y a=
      diagonalHessian a (empiricalConditionalMiddle j t σ y g) := by
  rw [empiricalConditionalMiddle_literal j t σ y hq g,fieldHessian_diagonalHessian]

lemma quadraticForm_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm M x=x⬝ᵥ(M*ᵥx) := by
  simp only [quadraticForm,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _; ring

lemma quadraticForm_margin {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {m : ℝ}
    (hM : (M-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖=1) : m ≤ quadraticForm M x.ofLp := by
  have hh := hM.dotProduct_mulVec_nonneg x.ofLp
  have hxx : x.ofLp⬝ᵥx.ofLp=1 := by
    have he := EuclideanSpace.real_norm_sq_eq x
    rw [hx,one_pow] at he
    simpa only [dotProduct,pow_two] using he.symm
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul,hxx,mul_one] at hh
  rw [quadraticForm_dotProduct]
  linarith

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurable_conditionalGoe_map {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    Measurable (fun g (p : Fin n × Fin n) => empiricalConditionalGoe j t σ y g p.1 p.2) := by
  dsimp [empiricalConditionalGoe,conditionalBlockMatrix,goeBlockResidual,goeBilinear,
    Matrix.mulVec,dotProduct,goeMatrix]
  fun_prop

lemma measurable_badField_fiber {n : ℕ} (j A ε c : ℝ) (y : Fin n → ℝ) :
    MeasurableSet {W : (Fin n × Fin n) → ℝ | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε c} :=
  ((isClosed_badFieldSet n j A ε c).preimage (by fun_prop)).measurableSet

lemma conditional_bad_le_freshbad {n : ℕ} [NeZero n] {j t σ A ε c m : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (hcm : c < m) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y) (empiricalObservation j t σ y)).real
      {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε c} ≤
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
        (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (empiricalConditionalMiddle j t σ y g)-
          m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} := by
  rw [show magnetization y=(fun i=>tanh (y i)) from rfl,empirical_conditional_law hj ht y hq]
  unfold Measure.real
  rw [Measure.map_apply (measurable_conditionalGoe_map j t σ y) (measurable_badField_fiber j A ε c y)]
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono
  intro g hg
  obtain ⟨a,ha,hclose,x,hx,hquad⟩ := hg
  refine ⟨a,ha,hclose,?_⟩
  intro hpsd
  rw [empiricalConditionalGoe_hessian j t σ y a hq g] at hquad
  exact (not_le_of_gt hcm) ((quadraticForm_margin hpsd x hx).trans hquad)

end SKGap
end
end

end OAI
