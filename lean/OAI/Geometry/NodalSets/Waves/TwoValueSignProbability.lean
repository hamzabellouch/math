import OAI.Geometry.NodalSets.Waves.GaussianFactorTwoSided
import OAI.Geometry.NodalSets.Waves.GaussianUniformBall
import OAI.Geometry.NodalSets.Waves.TwoValueGaussianMap

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
local notation "E" => EuclideanSpace ℝ (Fin 2)

lemma two_value_sign_probability (d M : ℝ) (hd : 0 < d) (hM : 0 ≤ M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {ι : Type} [Fintype ι] (z w : ι → ℂ) (mean : E),
      ‖mean‖ ≤ M → (∑ i, ‖z i‖^2) ≤ 4 → (∑ i, ‖w i‖^2) ≤ 4 →
      (∀ u v : ℝ, d*(u^2+v^2) ≤ ∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2) →
      p ≤ gaussianPairs {a | 1 ≤ mean 0+pairLinearSum z a ∧ mean 1+pairLinearSum w a ≤ -1} := by
  let target : E := WithLp.toLp 2 ![2,-2]
  obtain ⟨p,hp,hball⟩ := uniform_affine_gaussian_ball (ι := Fin 2) (Real.sqrt d)⁻¹ 4 M 1
    (by positivity) (by norm_num) hM (by norm_num) target
  refine ⟨p,hp,?_⟩
  intro ι hfin z w mean hm hz hw hgap
  let T := pairJetMap ![z,w]
  have hlo (v : E) : d*‖v‖^2 ≤ ‖T.adjoint v‖^2 := by
    rw [pairJetMap_two_energy]
    simpa only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two] using hgap (v 0) (v 1)
  have hhi (v : E) : ‖T.adjoint v‖^2 ≤ (4:ℝ)^2*‖v‖^2 := by
    rw [pairJetMap_two_energy]
    have hh := two_point_energy_upper z w 4 hz hw (v 0) (v 1)
    have hn : ‖v‖^2 = (v 0)^2+(v 1)^2 := by rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    rw [hn]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  obtain ⟨L,hLaw,hLi,hL⟩ := exists_gaussian_factor_two_sided T d 4 hd (by norm_num) hlo hhi
  have hmap : gaussianPairs.map (fun a ↦ mean+T (WithLp.toLp 2 a)) =
      (stdGaussian E).map (fun v ↦ mean+L v) := by
    have hh := congrArg (fun μ : Measure E ↦ μ.map (fun v ↦ mean+v)) (pairJetMap_law ![z,w])
    rw [hLaw] at hh
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  have hb := hball L mean hLi hL hm
  rw [← hmap,Measure.map_apply (by fun_prop) isOpen_ball.measurableSet] at hb
  apply hb.trans (measure_mono ?_)
  intro a ha
  let y := mean+T (WithLp.toLp 2 a)
  have hn : ‖y-target‖ < 1 := by simpa only [mem_preimage,mem_ball,dist_eq_norm] using ha
  have h0 := (PiLp.norm_apply_le (y-target) 0).trans_lt hn
  have h1 := (PiLp.norm_apply_le (y-target) 1).trans_lt hn
  change |y 0-2| < 1 at h0
  change |y 1-(-2)| < 1 at h1
  have hy0 : y 0 = mean 0+pairLinearSum z a := by simp [y,T,pairJetMap_apply]
  have hy1 : y 1 = mean 1+pairLinearSum w a := by simp [y,T,pairJetMap_apply]
  change 1 ≤ mean 0+pairLinearSum z a ∧ mean 1+pairLinearSum w a ≤ -1
  rw [← hy0,← hy1]
  exact ⟨by linarith [(abs_lt.mp h0).1],by linarith [(abs_lt.mp h1).2]⟩

end
end Yau.Geometry

end OAI
