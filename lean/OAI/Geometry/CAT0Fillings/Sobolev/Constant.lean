import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Sobolev.Completion
import OAI.Geometry.CAT0Fillings.Sobolev.CriticalNorm

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) : q.Sobolev :=
  ⟨q.graphPoint hu,q.graphPoint_mem hu⟩

@[simp] lemma inclusion_lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.inclusion (q.lipSobolev hu) = value hu := rfl
@[simp] lemma closedGradient_lipSobolev {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.closedGradient (q.lipSobolev hu) = q.gradient hu := rfl

lemma gradient_const (c : ℝ) : q.gradient (LipschitzWith.const c) = 0 := by
  apply Lp.ext
  filter_upwards [(q.memLp_gradientFunction (LipschitzWith.const c)).coeFn_toLp,
    q.ae_gradientFunction_bound (LipschitzWith.const c),Lp.coeFn_zero (E := Euc (k+1)) (p := 2) (μ := q.atlasMeasure)] with w hw hb hz
  rw [gradient,hw,hz]
  apply norm_eq_zero.mp
  exact le_antisymm hb (norm_nonneg _)

noncomputable def constant (c : ℝ) : q.Sobolev := q.lipSobolev (LipschitzWith.const c)

@[simp] lemma closedGradient_constant (c : ℝ) : q.closedGradient (q.constant c) = 0 :=
  q.gradient_const c

lemma criticalNorm_constant {p : ℝ} (hp : 0 < p) (c : ℝ) :
    AnalyticMinimizer.criticalNorm q.inclusion p (q.constant c) =
      |c| *(mass T)^(1/p) := by
  dsimp only [AnalyticMinimizer.criticalNorm,constant]
  rw [q.inclusion_lipSobolev]
  have he : (value (hT := hT) (LipschitzWith.const c) : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun _ => c) := ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const c)).memLp 2).coeFn_toLp
  rw [AnalyticMinimizer.lpNorm_congr_ae he,
    lpNorm_const' (by positivity) ENNReal.ofReal_ne_top,MassMeasure.currentMassMeasure_total]
  rw [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs,one_div]

lemma norm_inclusion_constant_sq (c : ℝ) : ‖q.inclusion (q.constant c)‖^2 = c^2*mass T := by
  rw [constant,q.inclusion_lipSobolev,norm_value,lpNorm_const' (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,MassMeasure.currentMassMeasure_total,Real.norm_eq_abs]
  rw [mul_pow,sq_abs,←Real.rpow_mul_natCast (mass_nonneg T)]
  norm_num

instance sobolev_separable : SeparableSpace q.Sobolev := by
  let : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
  let : SecondCountableTopology X := inferInstance
  let : SecondCountableTopology (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) := inferInstance
  let : SecondCountableTopology (Lp (Euc (k+1)) 2 q.atlasMeasure) := inferInstance
  let : SecondCountableTopology q.GraphAmbient := inferInstanceAs
    (SecondCountableTopology (WithLp 2 ((Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) ×
      (Lp (Euc (k+1)) 2 q.atlasMeasure))))
  let : SecondCountableTopology q.Sobolev := inferInstanceAs
    (SecondCountableTopology (q.closedGraph : Set q.GraphAmbient))
  infer_instance

end CAT0Fillings.ChartGeometry
end

end OAI
