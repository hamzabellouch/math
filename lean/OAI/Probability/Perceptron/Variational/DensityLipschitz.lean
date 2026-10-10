import Mathlib
import OAI.Probability.Perceptron.Variational.DensityDerivative
import OAI.Probability.Perceptron.Variational.FieldContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma poissonRealMean_increment_bound (F : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀ M, |F (M+1)-F M|≤C) (r : ℝ≥0) :
    |poissonRealMean (fun M => F (M+1)-F M) r|≤C := by
  have hinc (M) : |(F (M+2)-F (M+1))-(F (M+1)-F M)|≤2*C := by
    exact (abs_sub _ _).trans (by linarith [hF M,hF (M+1)])
  rw [poissonRealMean_eq_integral (by positivity : 0≤2*C) hinc r]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := poissonMeasure r) (f := fun M => F (M+1)-F M)
    (ae_of_all _ fun M => by simpa only [Real.norm_eq_abs] using hF M)

lemma poissonRealMean_lipschitz_bound (F : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀ M, |F (M+1)-F M|≤C) (s t : ℝ≥0) :
    |poissonRealMean F t-poissonRealMean F s|≤C*|(t:ℝ)-(s:ℝ)| := by
  have hb : ∀ r ∈ Ici (0:ℝ), ‖deriv (poissonRealMean F) r‖≤C := by
    intro r hr
    rw [(hasDerivAt_poissonRealMean hC hF r).deriv,Real.norm_eq_abs]
    exact poissonRealMean_increment_bound F hC hF ⟨r,hr⟩
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r (_ : r∈Ici (0:ℝ)) => (hasDerivAt_poissonRealMean hC hF r).differentiableAt)
    hb (convex_Ici (0:ℝ)) s.coe_nonneg t.coe_nonneg

lemma sourceExpectedPressure_density_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (s t : ℝ≥0) :
    |sourceExpectedPressure n k f p d h z t u-sourceExpectedPressure n k f p d h z s u|≤
      ‖f‖*|(t:ℝ)-(s:ℝ)| := by
  have hB := poissonRealMean_lipschitz_bound (sourceCountExpectedLog n k f p d h z u)
    (norm_nonneg f) (sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1)
    ((n+1:ℕ)*s) ((n+1:ℕ)*t)
  simp only [sourceExpectedPressure_poissonMean n k f p d h z u hz hz0 hz1]
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(n+1:ℕ))]
  calc
    _ ≤ (1/(n+1:ℕ))*(‖f‖*|(((n+1:ℕ)*t:ℝ≥0):ℝ)-(((n+1:ℕ)*s:ℝ≥0):ℝ)|) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by
      simp only [NNReal.coe_mul,NNReal.coe_natCast]
      rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n+1))]
      field_simp


lemma enrichedFeatureBound_continuous (N : ℕ) :
    Continuous (fun u : Fin N→ℝ => (enrichedFeatureBound N u:ℝ)) := by
  change Continuous (fun u : Fin N→ℝ => Real.sqrt ((N:ℝ)+∑ j, perturbationAmplitude N u j^2))
  unfold perturbationAmplitude
  fun_prop

lemma sourceFieldDistance_joint_continuous {N k : ℕ} (p d : Fin N→ℕ)
    (h : Fin (k+1)→ℝ) : Continuous (fun a : (Fin N→ℝ)×(Fin (k+1)→ℝ) =>
      sourceFieldDistance p d a.1 a.2 h) := by
  have hc := (sourceFieldCoefficients_continuous (k := k) p d).comp
    (continuous_snd : Continuous (fun a : (Fin N→ℝ)×(Fin (k+1)→ℝ) => a.2))
  have he : Continuous (fun a : (Fin N→ℝ)×(Fin (k+1)→ℝ) => indexedCoefficientSquare k
      (fun l i => sourceFieldCoefficients p d a.2 l i-sourceFieldCoefficients p d h l i)) := by
    simpa only [Function.comp_def,Pi.sub_def] using
      (indexedCoefficientSquare_continuous (I := EnrichedIndex N N p) k).comp
        (hc.sub (continuous_const (y := sourceFieldCoefficients p d h)))
  have hf := (enrichedFeatureBound_continuous N).comp
    (continuous_fst : Continuous (fun a : (Fin N→ℝ)×(Fin (k+1)→ℝ) => a.1))
  unfold sourceFieldDistance
  exact (continuous_const.mul (continuous_const.mul
    (((continuous_const.mul (continuous_const.mul (hf.pow 2))).add
      (continuous_const.mul (he.mul (hf.pow 2)))).sqrt.mul
      (he.mul (hf.pow 2)).sqrt))).add
        (((continuous_apply _).comp continuous_snd).sub continuous_const).abs

abbrev SourceContactParameter (n k : ℕ) := ℝ≥0 × (Fin (k+1)→ℝ) × (Fin (n+1)→ℝ)

def sourceContactDomain (n k : ℕ) : Set (SourceContactParameter n k) :=
  {a | (∀ l, 0≤a.2.1 l) ∧ Monotone a.2.1 ∧ ∀ j, a.2.2 j∈Icc 1 2}

def sourceJointPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (z : Fin k→ℝ) (a : SourceContactParameter n k) : ℝ :=
  sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2

def sourceContactDistance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (a' a : SourceContactParameter n k) : ℝ :=
  ‖f‖*|(a'.1:ℝ)-(a.1:ℝ)|+sourceFieldDistance p d a'.2.2 a'.2.1 a.2.1+
    ∑ j : Fin (n+1), (4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ))*|a'.2.2 j-a.2.2 j|

lemma sourceContactDistance_continuous (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (a : SourceContactParameter n k) : Continuous (fun a' => sourceContactDistance n k f p d a' a) := by
  unfold sourceContactDistance
  have hf : Continuous (fun a' : SourceContactParameter n k => sourceFieldDistance p d a'.2.2 a'.2.1 a.2.1) :=
    (sourceFieldDistance_joint_continuous (N := n+1) (k := k) p d a.2.1).comp
      (f := fun a' : SourceContactParameter n k => (a'.2.2,a'.2.1))
      ((continuous_snd.snd : Continuous (fun a' : SourceContactParameter n k => a'.2.2)).prodMk
        (continuous_snd.fst : Continuous (fun a' : SourceContactParameter n k => a'.2.1)))
  apply Continuous.add
  · have ht : Continuous (fun a' : SourceContactParameter n k => ‖f‖*|(a'.1:ℝ)-(a.1:ℝ)|) := by
      exact continuous_const.mul ((NNReal.continuous_coe.comp
        (continuous_fst : Continuous (fun a' : SourceContactParameter n k => a'.1))).sub continuous_const).abs
    exact ht.add hf
  · apply continuous_finsetSum
    intro j hj
    fun_prop

lemma sourceContactDistance_self (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (a : SourceContactParameter n k) : sourceContactDistance n k f p d a a=0 := by
  simp [sourceContactDistance,sourceFieldDistance_self]

lemma sourceJointPressure_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i,z i<1)
    (a' a : SourceContactParameter n k) (ha' : a'∈sourceContactDomain n k) (ha : a∈sourceContactDomain n k) :
    |sourceJointPressure n k f p d z a'-sourceJointPressure n k f p d z a|≤
      sourceContactDistance n k f p d a' a := by
  have ht := sourceExpectedPressure_density_comparison n k f p d a'.2.1 z a'.2.2 hz hz0 hz1 a.1 a'.1
  have hh := sourceExpectedPressure_field_comparison n k f p d a'.2.2 a'.2.1 a.2.1 z hz hz0 hz1 a.1
  have hu := sourceExpectedPressure_box_comparison n k f p d a.2.1 ha.1 ha.2.1 z hz hz0 hz1 a.1
    (u := a.2.2) (v := a'.2.2) (fun j => ⟨by linarith [(ha.2.2 j).1],(ha.2.2 j).2⟩)
    (fun j => ⟨by linarith [(ha'.2.2 j).1],(ha'.2.2 j).2⟩)
  change |sourceExpectedPressure n k f p d a'.2.1 z a'.1 a'.2.2-
    sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2|≤_
  have hab := abs_sub_le (sourceExpectedPressure n k f p d a'.2.1 z a'.1 a'.2.2)
    (sourceExpectedPressure n k f p d a'.2.1 z a.1 a'.2.2)
    (sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2)
  have hbc := abs_sub_le (sourceExpectedPressure n k f p d a'.2.1 z a.1 a'.2.2)
    (sourceExpectedPressure n k f p d a.2.1 z a.1 a'.2.2)
    (sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2)
  change |sourceExpectedPressure n k f p d a.2.1 z a.1 a'.2.2-
    sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2|≤_ at hu
  unfold sourceContactDistance
  linarith

lemma sourceJointPressure_continuousOn (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i,z i<1) :
    ContinuousOn (sourceJointPressure n k f p d z) (sourceContactDomain n k) := by
  intro a ha
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Tendsto (fun a' => sourceContactDistance n k f p d a' a) (𝓝 a)
      (𝓝 (sourceContactDistance n k f p d a a)) :=
    (sourceContactDistance_continuous n k f p d a).continuousAt
  rw [sourceContactDistance_self] at hc
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (hc.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with a' ha'
  simpa only [Real.norm_eq_abs] using sourceJointPressure_comparison n k f p d z hz hz0 hz1 a' a ha' ha

end SphericalPerceptronFreeEnergy
end

end OAI
