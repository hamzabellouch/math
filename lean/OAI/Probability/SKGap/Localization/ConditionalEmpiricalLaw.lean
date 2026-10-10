import Mathlib
import OAI.Probability.SKGap.Posterior.GOEPointwisePosterior
import OAI.Probability.SKGap.Posterior.ConditionalObservationData
import OAI.Probability.SKGap.Stability.ConditionalMeanScalar

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalObservation {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i=>y i-scalarD j (empiricalLaw y,t,σ)+j*scalarBMoment (empiricalLaw y)*tanh (y i)

def empiricalConditionalGoe {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p)
    (j*scalarBMoment p.1) (conditionalKappa j p) (conditionalEll j p)
    (empiricalUnit y q).ofLp (sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp) g

lemma empirical_observation_covariance {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (hq : 0 ≤ scalarQMoment (empiricalLaw y)) :
    (j/(n:ℝ))*sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y))^2+(t+σ^2)=
      scalarS j (empiricalLaw y,t,σ) ∧
    (t+σ^2)+2*(j/(n:ℝ))*sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y))^2=
      scalarS j (empiricalLaw y,t,σ)+j*scalarQMoment (empiricalLaw y) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hq)]
  dsimp [scalarS]
  constructor <;> field_simp <;> ring

lemma empirical_conditional_mean {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    let p : ScalarPoint := (empiricalLaw y,t,σ)
    let q := scalarQMoment p.1
    let s := scalarS j p
    let u := (empiricalUnit y q).ofLp
    let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
    (fun i k=>(goeRegressionCoefficient (j/(n:ℝ)) (t+σ^2) (fun l=>tanh (y l))*ᵥ
      empiricalObservation j t σ y) (i,k))=
      vecMulVec u ((j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u) u+
      (2*j*(scalarA j p+j*scalarBMoment p.1*q)/(s+j*q)) • vecMulVec u u := by
  dsimp only
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let c := sqrt ((n:ℝ)*q)
  let u := (empiricalUnit y q).ofLp
  let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hv : 0 < t+σ^2 := add_pos_of_pos_of_nonneg ht (sq_nonneg _)
  have hs : 0 < s := add_pos_of_pos_of_nonneg hv (mul_nonneg hj hq.le)
  have hu : u⬝ᵥu=1 := empiricalUnit_unit y hq
  have hscale : c • u=(fun i=>tanh (y i)) := empirical_unit_scale y hq
  have hc := empirical_observation_covariance j t σ y hq.le
  have hdot : u⬝ᵥempiricalObservation j t σ y=(n:ℝ)*(scalarA j p+B*q)/c :=
    empirical_unit_observation_dot j t σ B y hq
  have hmean := goeRegressionCoefficient_block_mean (c := c) (div_nonneg hj hn.le) hv hu
    (empiricalObservation j t σ y)
  rw [hscale] at hmean
  rw [hc.1,hc.2,hdot] at hmean
  have hperp : ((j/(n:ℝ))*c/s) • (empiricalObservation j t σ y-
      ((n:ℝ)*(scalarA j p+B*q)/c) • u)=
      (j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u := by
    ext i
    have hzi := congrFun (empirical_Z_formula y (scalarD j p) hs) i
    change Z i=(y i-scalarD j p)/(sqrt (n:ℝ)*sqrt s) at hzi
    have hmi := congrFun hscale i
    change c*u i=tanh (y i) at hmi
    change (j/(n:ℝ)*c/s)*(y i-scalarD j p+B*tanh (y i)-
      ((n:ℝ)*(scalarA j p+B*q)/c)*u i)=
      j*sqrt (q/s)*Z i-j*scalarA j p/s*u i
    rw [← hmi,hzi]
    convert conditional_perp_mean_scalar hn hq hs j (scalarA j p) B
      (y i-scalarD j p) (u i) using 1
    ring
  rw [hperp] at hmean
  have hparallel := conditional_parallel_mean_scalar (S := s+j*q) hn hq j (scalarA j p) B
  rw [hparallel] at hmean
  exact hmean

theorem empirical_conditional_law {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (fun i=>tanh (y i)) (empiricalObservation j t σ y)=
      (gaussianCoordinates (MatrixCoordinates (Fin n))).map
        (fun g p=>empiricalConditionalGoe j t σ y g p.1 p.2) := by
  let q := scalarQMoment (empiricalLaw y)
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hv : 0 < t+σ^2 := add_pos_of_pos_of_nonneg ht (sq_nonneg _)
  have hh := conditionalGoeLaw_block (c := sqrt ((n:ℝ)*q)) (div_nonneg hj hn.le) hv
    (empiricalUnit_unit y hq) (empiricalObservation j t σ y)
  rw [empirical_unit_scale y hq] at hh
  rw [(empirical_observation_covariance j t σ y hq.le).1,
    (empirical_observation_covariance j t σ y hq.le).2] at hh
  rw [hh]
  congr 1
  funext g p
  have hmean := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ=>M p.1 p.2)
    (empirical_conditional_mean (σ := σ) hj ht y hq)
  change _+_=empiricalConditionalGoe j t σ y g p.1 p.2
  dsimp only [empiricalConditionalGoe,conditionalBlockMatrix]
  dsimp only at hmean
  rw [hmean]
  simp only [Matrix.add_apply,conditionalKappa,conditionalEll]
  ring
end SKGap
end
end

end OAI
