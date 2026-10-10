import OAI.Analysis.Daugavet.WholeBallConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uIota

namespace ExactModuli.KW

abbrev infiniteCube := ℕ → unitInterval
abbrev infiniteCubeMeasure : Measure infiniteCube :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

lemma infinite_coordinate_mp (i : ℕ) :
    MeasurePreserving (fun ω : infiniteCube => ω i) infiniteCubeMeasure volume :=
  ⟨measurable_pi_apply i, Measure.infinitePi_map_eval _ i⟩

lemma finite_coordinates_mp {ι : Type uIota} [Fintype ι] (c : ι → ℕ) (hc : Function.Injective c) :
    MeasurePreserving (fun ω : infiniteCube => fun i => ω (c i)) infiniteCubeMeasure (cubeMeasure ι) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj hc, Measure.infinitePi_eq_pi]

/-- The number of copies can be chosen arbitrarily late, after the whole-ball parameters.
    This is Mathlib's L1 strong law, applied to the exact Pareto multiplier. -/
lemma multiplier_averages {p h : ℝ} (hp : 1 < p) (hh : 0 < h) :
    ∃ n : ℕ, 0 < n ∧
      (∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1|
        ∂cubeMeasure (Fin n)) < h := by
  let X : ℕ → infiniteCube → ℝ := fun i ω => multiplier p (ω i)
  have hXi (i : ℕ) : Integrable (X i) infiniteCubeMeasure :=
    ((infinite_coordinate_mp i).integrable_comp (integrable_multiplier hp).aestronglyMeasurable).mpr
      (integrable_multiplier hp)
  have hdist (i : ℕ) : IdentDistrib (X i) (multiplier p) infiniteCubeMeasure volume :=
    mp_ident (infinite_coordinate_mp i) (measurable_multiplier p)
  have hind : iIndepFun X infiniteCubeMeasure := iIndepFun_infinitePi (fun _ => measurable_multiplier p)
  have hmean : (∫ ω, X 0 ω ∂infiniteCubeMeasure) = 1 :=
    (hdist 0).integral_eq.trans (integral_multiplier hp)
  have hLLN := strong_law_Lp (by norm_num : (1 : ℝ≥0∞) ≤ 1) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    X (memLp_one_iff_integrable.mpr (hXi 0)) (fun i j hij => hind.indepFun hij) (fun i => (hdist i).trans (hdist 0).symm)
  have hreal := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp hLLN
  simp only [ENNReal.toReal_zero, hmean, smul_eq_mul] at hreal
  have havg (n : ℕ) : Integrable
      (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - 1) infiniteCubeMeasure :=
    ((integrable_finsetSum _ (fun i _ => hXi i)).const_mul _).sub (integrable_const 1)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∫ ω, |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) - 1| ∂infiniteCubeMeasure) < h := by
    convert hreal.eventually (Iio_mem_nhds hh) using 1
    ext n
    simp only [Function.comp_apply]
    rw [eLpNorm_one_eq_lintegral_enorm (havg n).aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm (havg n).aestronglyMeasurable]
    rfl
  obtain ⟨n, hn, hn'⟩ := ((eventually_gt_atTop 0).and hevent).exists
  refine ⟨n, hn, ?_⟩
  have hmp := finite_coordinates_mp (fun j : Fin n => (j : ℕ)) Fin.val_injective
  have heq := mp_integral hmp
    (((integrable_rowSum hp (fun _ : Fin n => 1)).const_mul (n : ℝ)⁻¹).sub (integrable_const 1)).abs.aestronglyMeasurable
  simp only [rowSum, one_mul, Pi.sub_apply] at heq
  rw [← heq]
  have hefin (ω : infiniteCube) : (∑ j : Fin n, multiplier p (ω j)) =
      ∑ i ∈ Finset.range n, X i ω := Fin.sum_univ_eq_sum_range (fun j => multiplier p (ω j)) n
  simp only [hefin]
  exact hn'

end ExactModuli.KW

end

end OAI
