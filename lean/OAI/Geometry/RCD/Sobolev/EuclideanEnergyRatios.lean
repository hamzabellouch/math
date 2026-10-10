import OAI.Geometry.RCD.Sobolev.EuclideanEnergyDifferentiation

namespace OAI

/-! # Rescaling the local energy density by exact Euclidean ball volumes -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_ball_real {n : ℕ} (hn : 0<n) (x : Euclidean n)
    {r : ℝ} (hr : 0≤r) :
    volume.real (ball x r)=r^n*volume.real (ball (0:Euclidean n) 1) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [Measure.real,Measure.addHaar_ball volume x hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),finrank_euclideanSpace_fin]
  rfl

theorem euclidean_closedBall_real {n : ℕ} (hn : 0<n) (x : Euclidean n)
    {r : ℝ} (hr : 0≤r) :
    volume.real (closedBall x r)=r^n*volume.real (ball (0:Euclidean n) 1) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [show volume.real (closedBall x r)=volume.real (ball x r) by
    exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume x r)]
  exact euclidean_ball_real hn x hr

theorem euclidean_energy_ratio_limit {n : ℕ} (hn : 0<n)
    (ν : FiniteMeasure (Euclidean n)) (x : Euclidean n) {d θ c : ℝ}
    (hθ : 0<θ) (hc : 0<c)
    (hd : Tendsto (fun t => (ν : Measure (Euclidean n)).real (closedBall x t)/
      volume.real (closedBall x t)) (𝓝[>] 0) (𝓝 d))
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => (ν : Measure (Euclidean n)).real (closedBall x (c*r k))/
      volume.real (ball x (θ*r k))) atTop (𝓝 ((c/θ)^n*d)) := by
  have ht : Tendsto (fun k => c*r k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hlim.const_mul c,
      Eventually.of_forall fun k => mul_pos hc (hr k)⟩
  have hh := (hd.comp ht).const_mul ((c/θ)^n)
  apply hh.congr'
  filter_upwards [] with k
  have hV : volume.real (ball (0:Euclidean n) 1)≠0 :=
    (ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_ne_top).ne'
  dsimp only [Function.comp_def]
  rw [euclidean_closedBall_real hn x (mul_pos hc (hr k)).le,
    euclidean_ball_real hn x (mul_pos hθ (hr k)).le]
  rw [div_pow]
  field_simp [hV,hθ.ne',hc.ne',(hr k).ne']
  ring

end RegularPointCoordinates

end

end OAI
