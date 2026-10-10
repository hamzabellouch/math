import Mathlib
import OAI.Geometry.CAT0Fillings.Euler.Moments
import OAI.Geometry.CAT0Fillings.Euler.OppositePointwise

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.OppositeAverage
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma memLp_sqrt_energy {u : Ω → ℝ} {D : Ω → E} {β : ℝ}
    (hb : 0 ≤ β) (hu : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hv : MemLp (fun x => (u x)^(1+β)) 2 μ)
    (hD : MemLp (fun x => (u x)^β • D x) 2 μ) :
    MemLp (fun x => Real.sqrt ((u x)^(2+2*β)+4*β^2*(u x)^(2*β)*‖D x‖^2)) 2 μ := by
  let a : Ω → ℝ := fun x => (u x)^(1+β)
  let b : Ω → ℝ := fun x => 2*β*‖(u x)^β • D x‖
  have ha : MemLp a 2 μ := hv
  have hb' : MemLp b 2 μ := hD.norm.const_mul (2*β)
  have hF : MemLp (fun x => Real.sqrt (a x^2+b x^2)) 2 μ := by
    apply (ha.norm.add hb'.norm).of_le
      (Real.continuous_sqrt.comp_aestronglyMeasurable ((ha.aestronglyMeasurable.pow 2).add (hb'.aestronglyMeasurable.pow 2)))
    filter_upwards [] with x
    have hb0 : 0 ≤ b x := mul_nonneg (mul_nonneg (by norm_num) hb) (norm_nonneg _)
    change ‖Real.sqrt (a x^2+b x^2)‖ ≤ ‖‖a x‖+‖b x‖‖
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.norm_of_nonneg (by positivity)]
    simp only [Real.norm_eq_abs,abs_of_nonneg hb0]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_abs (a x),mul_nonneg (abs_nonneg (a x)) hb0]
  apply (memLp_congr_ae ?_).mp hF
  filter_upwards [hu] with x hx
  dsimp [a,b]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx β)]
  congr 1
  simp only [mul_pow,←Real.rpow_mul_natCast hx]
  ring_nf

lemma radial_integral_square {u r : Ω → ℝ} {R D : Ω → E} {β W : ℝ}
    (hb : 0 < β) (hW : 0 ≤ W)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u x) (hr : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hR : ∀ᵐ x ∂μ, ‖R x‖ ≤ 1)
    (hf : MemLp (fun x => r x*(u x)^(1+3*β)) 2 μ)
    (hv : MemLp (fun x => (u x)^(1+β)) 2 μ)
    (hD : MemLp (fun x => (u x)^β • D x) 2 μ)
    (hF : Integrable (fun x => r x*((u x)^(2+4*β)*Real.sqrt (1-‖R x‖^2)-
      2*β*(u x)^(1+4*β)*inner ℝ (R x) (D x))) μ)
    (hrad : W ≤ ∫ x, r x*((u x)^(2+4*β)*Real.sqrt (1-‖R x‖^2)-
      2*β*(u x)^(1+4*β)*inner ℝ (R x) (D x)) ∂μ) :
    W^2 ≤ (∫ x, r x^2*(u x)^(2+6*β) ∂μ)*
      (∫ x, (u x)^(2+2*β)+4*β^2*(u x)^(2*β)*‖D x‖^2 ∂μ) := by
  have hg := memLp_sqrt_energy hb.le hu hv hD
  have hf0 : ∀ᵐ x ∂μ, 0 ≤ r x*(u x)^(1+3*β) := by
    filter_upwards [hu,hr] with x hx hy using mul_nonneg hy (Real.rpow_nonneg hx _)
  have hg0 : ∀ᵐ x ∂μ, 0 ≤ Real.sqrt ((u x)^(2+2*β)+4*β^2*(u x)^(2*β)*‖D x‖^2) :=
    Eventually.of_forall fun _ => Real.sqrt_nonneg _
  have hh := integral_mono_ae hF (hf.integrable_mul hg) (by
    filter_upwards [hu,hr,hR] with x hx hy hz
    calc
      _ ≤ r x*((u x)^(1+3*β)*Real.sqrt ((u x)^(2+2*β)+4*β^2*(u x)^(2*β)*‖D x‖^2)) :=
        mul_le_mul_of_nonneg_left (radial_power_cauchy (R x) (D x) hx hb hz) hy
      _ = _ := by simp only [Pi.mul_apply]; ring)
  have hle := hrad.trans hh
  have hsq := (sq_le_sq₀ hW (hW.trans hle)).mpr hle
  apply (hsq.trans (integral_cauchy_square hf hg hf0 hg0)).trans_eq
  congr 1
  · apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [mul_pow,←Real.rpow_mul_natCast hx]
    congr 2
    ring
  · apply integral_congr_ae
    filter_upwards [hu] with x hx
    exact Real.sq_sqrt (by positivity)
end CAT0Fillings.OppositeAverage
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma opposite_all_center (hz : IsCycle T) (o : X) (v : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    (∫ x, (q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT)^2 ≤
      (∫ x, (q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT)*
      (∫ x, dist o x^2*(q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT) := by
  have hu := q.atlas_preserving.quasiMeasurePreserving.ae hv
  have hp (a : ℝ) (ha : 0 ≤ a) : MemLp (fun w => (q.inclusion v (q.atlasParam w))^a) 2 q.atlasMeasure :=
    (ClosedCalculus.power_memLp_two hv hm ha).comp_measurePreserving q.atlas_preserving
  have hD := q.weighted_gradient_memLp v (fun γ hγ => by
    obtain ⟨R,_,hR⟩ := hpow γ hγ
    exact ⟨R,hR⟩) hb.le
  have hp3 := hp (1+3*β) (by positivity)
  have hdist : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  have hf : MemLp (fun w => dist o (q.atlasParam w)*(q.inclusion v (q.atlasParam w))^(1+3*β)) 2 q.atlasMeasure := by
    apply (hp3.const_mul (Metric.diam (univ : Set X))).of_le (hdist.mul hp3.aestronglyMeasurable)
    filter_upwards [hu] with w hw
    simp only [Pi.mul_apply,Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg dist_nonneg (Real.rpow_nonneg hw _)),
      abs_of_nonneg (mul_nonneg Metric.diam_nonneg (Real.rpow_nonneg hw _))]
    exact mul_le_mul_of_nonneg_right (radius_bound o (q.atlasParam w)) (Real.rpow_nonneg hw _)
  have hR : ∀ᵐ w ∂q.atlasMeasure, ‖q.gradient (LipschitzWith.dist_right o) w‖ ≤ 1 := by
    simpa only [NNReal.coe_one] using q.ae_gradient_bound (LipschitzWith.dist_right o)
  have hW : 0 ≤ ∫ x, (q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT := by
    apply integral_nonneg_of_ae
    filter_upwards [hv] with x hx using Real.rpow_nonneg hx _
  obtain ⟨hF,hred⟩ := q.radial_power_integral hz o v hb hn hv hm hpow hr
  have hh := OppositeAverage.radial_integral_square hb hW hu
    (Eventually.of_forall (fun w : ℕ × Euc (k+1) => dist_nonneg (x := o) (y := q.atlasParam w)))
    hR hf (hp (1+β) (by positivity)) hD hF hred
  rw [q.euler_weighted_moment v hb hn hv hm hpow heuler] at hh
  have hI : AEStronglyMeasurable (fun x => dist o x^2*(q.inclusion v x)^(2+6*β)) (MassMeasure.currentMassMeasure hT) :=
    (by fun_prop : Continuous (fun x : X => dist o x^2)).aestronglyMeasurable.mul
      (ClosedCalculus.power_memLp_two hv hm (a := 2+6*β) (by positivity)).aestronglyMeasurable
  have hAt := integral_map (μ := q.atlasMeasure) (f := fun x => dist o x^2*(q.inclusion v x)^(2+6*β)) q.atlas_preserving.measurable.aemeasurable (by rw [q.atlas_preserving.map_eq]; exact hI)
  rw [q.atlas_preserving.map_eq] at hAt
  rw [←hAt] at hh
  exact hh.trans_eq (mul_comm _ _)
end CAT0Fillings.ChartGeometry
end

end OAI
