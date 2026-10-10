import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularDirichletContinuation

namespace OAI

/-! Absolute convergence gives uniform bounds on each initial vertical line. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaDirichletNormMass (σ : ℝ) : ℝ :=
  ∑' n : Eisenstein, if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)

lemma cubicThetaDirichletNormMass_nonneg (σ : ℝ) : 0≤cubicThetaDirichletNormMass σ := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (_root_.norm_nonneg _) _

lemma cubicThetaDirichletNormMass_summable {σ : ℝ} (hσ : 2<σ) :
    Summable (fun n : Eisenstein => if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)) := by
  simpa only [norm_one,one_mul] using cubicTheta_mellin_weight_summable
    (a := fun _ : Eisenstein => (1:ℂ)) (by norm_num : (0:ℝ)≤1)
      (fun _ => by norm_num) hσ

theorem cubicThetaDirichlet_norm_le {a : Eisenstein→ℂ} {C σ : ℝ}
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C) (hσ : 2<σ)
    (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaDirichlet a s‖≤C*cubicThetaDirichletNormMass σ := by
  let w := fun n : Eisenstein => if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)
  have hw := cubicThetaDirichletNormMass_summable hσ
  have hb (n : Eisenstein) : ‖if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)‖≤C*w n := by
    by_cases hn : n=0
    · simp [hn,w]
    · simp only [hn,ite_false,w,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
        (cubicThetaFrequency_pos hn),Complex.neg_re,hs]
      exact mul_le_mul_of_nonneg_right (ha n hn) (Real.rpow_nonneg (_root_.norm_nonneg _) _)
  have hsum : Summable (fun n : Eisenstein => if n=0 then (0:ℂ) else
      a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)) := (hw.mul_left C).of_norm_bounded hb
  calc
    _ ≤ ∑' n, ‖if n=0 then (0:ℂ) else a n*(‖cubicThetaFrequency n‖:ℂ)^(-s)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, C*w n := Summable.tsum_le_tsum hb hsum.norm (hw.mul_left C)
    _ = _ := tsum_mul_left

theorem cubicThetaAngularDirichletContinuation_right_bound {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaAngularDirichletContinuation q x y rev k s‖≤
      81*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaAngularDirichletContinuation_eq hq x y hxy rev hk (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n hn => ?_) (by linarith : 2<2*σ-1) _ (by
      simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
        Complex.one_re,zero_mul,sub_zero,hs])
  rw [norm_mul,norm_theta hn,one_mul]
  exact cubicThetaAdditiveCoefficient_norm _ n

end CubicFirstMoment

end

end OAI
