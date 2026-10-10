import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalHessianLaw
import OAI.Probability.SKGap.Localization.ScalarEmpirical
import OAI.Probability.SKGap.Gaussian.ScalarGaussianReductionAlgebra

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma tapField_planted_observation {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    tapField j (plantedInteraction j W) (fun i=>t+x i) y=
      empiricalObservation j t σ y-W*ᵥmagnetization y-x := by
  ext i
  simp only [tapField,plantedInteraction,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,vecMulVec_apply,mul_one,add_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,empiricalObservation,scalarD,scalarM,integral_empiricalLaw,
    Fintype.card_fin,scalarBMoment,scalarQMoment_empirical_overlap,onsager,
    magnetization,Pi.sub_apply,Matrix.mulVec,dotProduct]
  ring

lemma scalar_density_cancellation {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) :
    rankOneDensity ((j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2))
      (j/(n:ℝ)) (magnetization y) (empiricalObservation j t σ y)*
      exp ((n:ℝ)*j*(1-overlap y)^2/2)=
    sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y := by
  let p := scalarEmpirical y t σ
  let q := scalarQMoment (empiricalLaw y)
  let s := scalarS j p
  let S := s+j*q
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hq : 0 ≤ q := (scalarQMoment_bounds _).1
  have hs : 0 < s := add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) (mul_nonneg hj hq)
  have hS : 0 < S := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hm : magnetization y⬝ᵥmagnetization y=(n:ℝ)*q := by
    dsimp [q]
    rw [scalarQMoment_empirical_overlap]
    simp only [overlap,magnetization,dotProduct,← pow_two]
    field_simp
  have hx : (fun i=>y i-scalarD j p)⬝ᵥmagnetization y=(n:ℝ)*scalarA j p := by
    rw [dotProduct_comm]
    exact scalarA_empirical_sum j t σ y
  have hs' : (j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2)=s := by
    rw [hm]; dsimp [s,scalarS,p,scalarEmpirical,q]; field_simp; ring
  rw [hs']
  have hobs : empiricalObservation j t σ y=(fun i=>y i-scalarD j p)+(j*(1-q)) • magnetization y := rfl
  rw [hobs]
  have hc := rankOneDensity_cancellation hn hs hS.ne' (rfl : S=s+j*q)
    (fun i=>y i-scalarD j p) (magnetization y) hm hx (b := 1-q)
  have hb : 1-overlap y=1-q := by rw [← scalarQMoment_empirical_overlap]
  rw [hb,hc]
  have hd : productNormal (scalarD j p) s y=radialDensity (sqrt s) (fun i=>y i-scalarD j p) := by
    unfold productNormal
    rw [show s.toNNReal=NNReal.mk s hs.le from by ext; exact Real.coe_toNNReal _ hs.le]
    exact gaussian_density_shift _ hs.le y
  rw [scalarIntegrand,show scalarEmpirical y t σ=p from rfl,hd]
  simp only [Fintype.card_fin]
  have he : (n:ℝ)*j*(scalarA j p-s*(1-q))^2/(2*s*S)=(n:ℝ)*scalarPsi j p := by
    dsimp [S,s,q,p,scalarPsi,scalarEmpirical]
    ring
  rw [he]
  ring
end SKGap
end
end

end OAI
