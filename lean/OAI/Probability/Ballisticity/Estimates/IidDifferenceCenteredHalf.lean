import Mathlib
import OAI.Probability.Ballisticity.Estimates.SymmetrizedMgf

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma iid_difference_centered_eq_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsGaussian ν]
    (hmean : ∫ x, x ∂ν = 0)
    (hv : (μ.prod μ).map (fun p : E × E => p.1-p.2) = ν)
    (a : ℝ) (ha : a^2 = 1/2) :
    μ.map (fun x => x-∫ y, y ∂μ) = ν.map (fun x => a • x) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one,charFunDual_eq_charFun_map_one]
  rw [Measure.map_map L.measurable (show Measurable (fun x : E => x-∫ y, y ∂μ) by fun_prop),
    Measure.map_map L.measurable (show Measurable (fun x : E => a • x) by fun_prop)]
  change charFun (μ.map (fun x => L (x-∫ y, y ∂μ))) 1 =
    charFun (ν.map (fun x => L (a • x))) 1
  rw [iid_difference_gaussian_centered_linear μ ν hmean hv]
  have he : (fun x => L (a • x)) = (fun x : ℝ => a*x) ∘ L := by ext x; simp
  rw [he,← Measure.map_map (by fun_prop) L.measurable,IsGaussian.map_eq_gaussianReal,
    IsGaussian.integral_dual,hmean,map_zero,gaussianReal_map_const_mul,mul_zero]
  congr 2
  apply NNReal.eq
  simp [ha,div_eq_mul_inv,mul_comm]

lemma iid_diff_translation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c : E) :
    ((μ.map (fun x => x-c)).prod (μ.map (fun x => x-c))).map (fun p : E × E => p.1-p.2) =
      (μ.prod μ).map (fun p : E × E => p.1-p.2) := by
  have hf : Measurable (fun x : E => x-c) := by fun_prop
  rw [Measure.map_prod_map _ _ hf hf,Measure.map_map (show Measurable (fun p : E × E => p.1-p.2) by fun_prop)
    (hf.prodMap hf)]
  congr 1
  funext p
  change (p.1-c)-(p.2-c) = p.1-p.2
  abel

lemma weak_iid_difference_tendsto {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => ((μ n).prod (μ n)).map (fun pair => pair.1 - pair.2))
      atTop (𝓝 ((ν.prod ν).map (fun pair => pair.1 - pair.2))) :=
  (ProbabilityMeasure.continuous_map (continuous_fst.sub continuous_snd)).tendsto _ |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,ν) |>.comp (hμ.prodMk_nhds hμ))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gaussian_median_half (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v (Set.Iic m) = 1/2 ∧ gaussianReal m v (Set.Ici m) = 1/2 := by
  have : NullSingletonClass (gaussianReal m v) := nullSingletonClass_gaussianReal hv
  have hs : gaussianReal m v (Set.Iio m) = gaussianReal m v (Set.Ioi m) := by
    have hh : (gaussianReal m v).map (fun x => 2*m-x) = gaussianReal m v := by
      rw [gaussianReal_map_const_sub]; congr 1; ring
    calc
      _ = (Measure.map (fun x => 2*m-x) (gaussianReal m v)) (Set.Iio m) := by rw [hh]
      _ = _ := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
        apply congrArg (gaussianReal m v)
        ext x
        change 2*m-x < m ↔ m < x
        constructor <;> intro h <;> linarith
  have hl : gaussianReal m v (Set.Iio m) = gaussianReal m v (Set.Iic m) :=
    measure_congr Iio_ae_eq_Iic
  have hr : gaussianReal m v (Set.Ioi m) = gaussianReal m v (Set.Ici m) :=
    measure_congr Ioi_ae_eq_Ici
  have hsum : gaussianReal m v (Set.Iic m)+gaussianReal m v (Set.Ioi m) = 1 := by
    simpa only [Set.compl_Iic,measure_univ] using measure_add_measure_compl (μ := gaussianReal m v)
      measurableSet_Iic
  have he : gaussianReal m v (Set.Iic m) = 1/2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    have hh := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),← hs,hl] at hh
    norm_num at hh ⊢
    linarith
  exact ⟨he,by rw [← hr,← hs,hl,he]⟩

lemma gaussian_median_strict (m : ℝ) (v : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    (1/2 : ℝ≥0∞) < gaussianReal m v (Set.Iio (m+ε)) ∧
    (1/2 : ℝ≥0∞) < gaussianReal m v (Set.Ioi (m-ε)) := by
  by_cases hv : v = 0
  · subst v
    simp [hε,gaussianReal_zero_var]
  have hh := gaussian_median_half m v hv
  have hpos {a b : ℝ} (hab : a < b) : 0 < gaussianReal m v (Set.Ioo a b) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hz' := gaussianReal_absolutelyContinuous' m hv hz
    have hp : 0 < (volume : Measure ℝ) (Set.Ioo a b) := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    exact hp.ne' hz'
  constructor
  · have hc : Set.Iic m ∪ Set.Ioo m (m+ε) = Set.Iio (m+ε) := by
      ext x; simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ioo,Set.mem_Iio]; constructor
      · rintro (h|h) <;> linarith
      · intro h; by_cases hx : x ≤ m; exact Or.inl hx; exact Or.inr ⟨lt_of_not_ge hx,h⟩
    rw [← hc,measure_union (by exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge hx hy.1)
      measurableSet_Ioo,hh.1]
    exact ENNReal.lt_add_right (by norm_num) (hpos (by linarith)).ne'
  · have hc : Set.Ici m ∪ Set.Ioo (m-ε) m = Set.Ioi (m-ε) := by
      ext x; simp only [Set.mem_union,Set.mem_Ici,Set.mem_Ioo,Set.mem_Ioi]; constructor
      · rintro (h|h) <;> linarith
      · intro h; by_cases hx : m ≤ x; exact Or.inl hx; exact Or.inr ⟨h,lt_of_not_ge hx⟩
    rw [← hc,measure_union (by exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge hx hy.2)
      measurableSet_Ioo,hh.2]
    exact ENNReal.lt_add_right (by norm_num) (hpos (by linarith)).ne'

lemma median_tendsto_of_weak {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 ν)) (b : ℕ → ℝ) (m : ℝ)
    (hb : ∀ n, (1/2 : ℝ≥0∞) ≤ (μ n : Measure ℝ) (Set.Iic (b n)) ∧
      (1/2 : ℝ≥0∞) ≤ (μ n : Measure ℝ) (Set.Ici (b n)))
    (hm : ∀ ε > 0, (1/2 : ℝ≥0∞) < (ν : Measure ℝ) (Set.Iio (m+ε)) ∧
      (1/2 : ℝ≥0∞) < (ν : Measure ℝ) (Set.Ioi (m-ε))) :
    Tendsto b atTop (𝓝 m) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hu := eventually_lt_of_lt_liminf ((hm ε hε).1.trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ isOpen_Iio))
  have hl := eventually_lt_of_lt_liminf ((hm ε hε).2.trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ isOpen_Ioi))
  rw [eventually_atTop] at hu hl
  obtain ⟨N,hN⟩ := hu
  obtain ⟨M,hM⟩ := hl
  refine ⟨max N M,fun n hn => ?_⟩
  have hu := hN n (le_trans (le_max_left _ _) hn)
  have hl := hM n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq,abs_lt]
  constructor
  · by_contra! hh
    have he : Set.Ioi (m-ε) ⊆ (Set.Iic (b n))ᶜ := by intro x hx; simp only [Set.mem_compl_iff,Set.mem_Iic]; change m-ε < x at hx; linarith
    have hm' := (measure_mono (μ := (μ n : Measure ℝ)) he).trans_eq (measure_compl measurableSet_Iic (measure_ne_top _ _))
    rw [measure_univ] at hm'
    have hup : (μ n : Measure ℝ) (Set.Ioi (m-ε)) ≤ 1/2 := by
      calc _ ≤ 1-(μ n : Measure ℝ) (Set.Iic (b n)) := hm'
        _ ≤ 1-(1/2) := tsub_le_tsub_left (hb n).1 1
        _ = 1/2 := ENNReal.sub_half (by norm_num)
    exact not_lt_of_ge hup hl
  · by_contra! hh
    have he : Set.Iio (m+ε) ⊆ (Set.Ici (b n))ᶜ := by intro x hx; simp only [Set.mem_compl_iff,Set.mem_Ici]; change x < m+ε at hx; linarith
    have hm' := (measure_mono (μ := (μ n : Measure ℝ)) he).trans_eq (measure_compl measurableSet_Ici (measure_ne_top _ _))
    rw [measure_univ] at hm'
    have hup : (μ n : Measure ℝ) (Set.Iio (m+ε)) ≤ 1/2 := by
      calc _ ≤ 1-(μ n : Measure ℝ) (Set.Ici (b n)) := hm'
        _ ≤ 1-(1/2) := tsub_le_tsub_left (hb n).2 1
        _ = 1/2 := ENNReal.sub_half (by norm_num)
    exact not_lt_of_ge hup hu

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical

end
end

end OAI
