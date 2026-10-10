import Mathlib
import OAI.Probability.Ballisticity.Estimates.NonCollapsedSums

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma truncated_variance_tail_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) {z : ℝ} (hz : 0 ≤ z) :
    (3/4:ℝ)*z^2*μ.real {x | z < |S x|} ≤
      truncatedVariance μ S z-truncatedVariance μ S (z/2) := by
  have hi (a : ℝ) := integrable_truncated_square μ S hS a
  let E := {x | z < |S x|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hS.abs
  have hI : Integrable (E.indicator (fun _ => (3/4:ℝ)*z^2)) μ := (integrable_const _).indicator hE
  have heq : (∫ x, E.indicator (fun _ => (3/4:ℝ)*z^2) x ∂μ) = (3/4:ℝ)*z^2*μ.real E := by
    rw [integral_indicator hE]
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
  unfold truncatedVariance
  rw [← heq,← integral_sub (hi z) (hi (z/2))]
  apply integral_mono hI ((hi z).sub (hi (z/2)))
  intro x
  change E.indicator (fun _ => (3/4:ℝ)*z^2) x ≤ min ((S x)^2) (z^2)-min ((S x)^2) ((z/2)^2)
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx]
    have hh : z < |S x| := hx
    rw [min_eq_right (by nlinarith [sq_abs (S x)] : z^2 ≤ (S x)^2),
      min_eq_right (by nlinarith [sq_abs (S x)] : (z/2)^2 ≤ (S x)^2)]
    ring_nf
    rfl
  · rw [Set.indicator_of_notMem hx]
    exact sub_nonneg.mpr (min_le_min_left _ (by nlinarith : (z/2)^2 ≤ z^2))

lemma fluctuation_tail_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    fluctuationScale μ S r*μ.real {x | a*r < |S x|} ≤
      (4/(3*a^2))*((truncatedVariance μ S (a*r)-truncatedVariance μ S (a*r/2))/truncatedVariance μ S r) := by
  have hh := truncated_variance_tail_difference μ S hS (mul_nonneg ha.le hr.le)
  have hm := truncatedVariance_pos μ S hS hne hr
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  unfold fluctuationScale
  rw [div_mul_eq_mul_div,div_le_iff₀ hm]
  rw [mul_assoc,div_mul_cancel₀ _ (ne_of_gt hm)]
  rw [div_mul_eq_mul_div,le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) ha2)]
  nlinarith [hh]

lemma dyadicCut_add (j k : ℕ) : dyadicCut (j+k) = dyadicCut j*dyadicCut k := by
  exact pow_add _ _ _
lemma dyadicCut_succ (j : ℕ) : dyadicCut (j+1) = dyadicCut j/2 := by
  simp only [dyadicCut,pow_succ]
  ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma dyadic_profile_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (F : ℕ → ℝ) {F₀ : ℝ} (hF₀ : 0 < F₀) (hFle : ∀ j, F₀ ≤ F j)
    (hF : ∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j)))
    (hFlim : Tendsto F atTop (𝓝 F₀)) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      fluctuationScale μ S (dyadicCut j*r n)*μ.real {x | dyadicCut k*(dyadicCut j*r n) < |S x|} < δ := by
  let B := fun j => (4/(3*(dyadicCut k)^2))*((F (j+k)-F (j+k+1))/F j)
  have hB : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => F (j+k)) atTop (𝓝 F₀) := hFlim.comp (tendsto_add_atTop_nat k)
    have h2 : Tendsto (fun j => F (j+k+1)) atTop (𝓝 F₀) := hFlim.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat k))
    simpa only [B,Pi.div_apply,sub_self,zero_div,mul_zero] using tendsto_const_nhds.mul ((h1.sub h2).div hFlim (ne_of_gt hF₀))
  filter_upwards [hB.eventually (gt_mem_nhds hδ)] with j hj
  have hm (n) : truncatedVariance μ S (r n) ≠ 0 := ne_of_gt (truncatedVariance_pos μ S hS hne (hr n))
  have hFj : F j ≠ 0 := ne_of_gt (hF₀.trans_le (hFle j))
  have hlim : Tendsto (fun n => (4/(3*(dyadicCut k)^2))*
      ((truncatedVariance μ S (dyadicCut k*(dyadicCut j*r n))-
        truncatedVariance μ S (dyadicCut k*(dyadicCut j*r n)/2))/
        truncatedVariance μ S (dyadicCut j*r n))) atTop (𝓝 (B j)) := by
    have hh := ((((hF (j+k)).sub (hF (j+k+1))).div (hF j) hFj).const_mul (4/(3*(dyadicCut k)^2)))
    convert hh using 1
    funext n
    rw [dyadicCut_succ (j+k),dyadicCut_add]
    congr 1
    have heq₁ : dyadicCut k*(dyadicCut j*r n) = dyadicCut j*dyadicCut k*r n := by ring
    have heq₂ : dyadicCut k*(dyadicCut j*r n)/2 = (dyadicCut j*dyadicCut k/2)*r n := by ring
    rw [heq₂,heq₁]
    simp only [Pi.div_apply]
    field_simp [hm n]
  filter_upwards [hlim.eventually (gt_mem_nhds hj)] with n hn
  exact (fluctuation_tail_difference μ S hS hne (mul_pos (dyadicCut_pos j) (hr n)) (dyadicCut_pos k)).trans_lt hn

lemma isGaussianSequence_of_dyadic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hr0 : ∀ᶠ n in atTop, 0 ≤ r n)
    (hGauss : ∀ k, Tendsto (fun n => fluctuationScale μ S (r n)*μ.real {x | dyadicCut k*r n < |S x|}) atTop (𝓝 0)) :
    IsGaussianSequence μ S r := by
  refine ⟨hr,?_⟩
  intro a ha
  obtain ⟨k,hk⟩ := (dyadicCut_tendsto.eventually (gt_mem_nhds ha)).exists
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hGauss k)
    (Eventually.of_forall fun n => mul_nonneg (fluctuationScale_nonneg μ S _) measureReal_nonneg)
  filter_upwards [hr0] with n hn
  apply mul_le_mul_of_nonneg_left _ (fluctuationScale_nonneg μ S _)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  exact (mul_le_mul_of_nonneg_right hk.le hn).trans_lt hx

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma double_gaussian_selection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ)
    (z : ℕ → ℕ → ℝ) (hz : ∀ j, Tendsto (z j) atTop atTop)
    (htail : ∀ k, ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      fluctuationScale μ S (z j n)*μ.real {x | dyadicCut k*z j n < |S x|} < δ)
    (bad : ℕ → ℕ → ℝ) {δ : ℝ}
    (hbad : ¬ ∀ᶠ j in atTop, ∀ᶠ n in atTop, bad j n < δ) :
    ∃ j n : ℕ → ℕ, Tendsto j atTop atTop ∧
      IsGaussianSequence μ S (fun i => z (j i) (n i)) ∧
      (∀ i, δ ≤ bad (j i) (n i)) := by
  classical
  have hbad' : ∀ J, ∃ j, J ≤ j ∧ ∀ N, ∃ n, N ≤ n ∧ δ ≤ bad j n := by
    simpa only [eventually_atTop,not_exists,not_forall,Classical.not_imp,not_lt,exists_prop] using hbad
  have hex (i : ℕ) : ∃ j n, i ≤ j ∧ (i:ℝ)+1 ≤ z j n ∧ δ ≤ bad j n ∧
      ∀ k ≤ i, fluctuationScale μ S (z j n)*μ.real {x | dyadicCut k*z j n < |S x|} < 1/((i:ℝ)+1) := by
    have ht : ∀ᶠ j in atTop, ∀ k : Fin (i+1), ∀ᶠ n in atTop,
        fluctuationScale μ S (z j n)*μ.real {x | dyadicCut (k:ℕ)*z j n < |S x|} < 1/((i:ℝ)+1) :=
      eventually_all.mpr (fun k => htail k _ (by positivity))
    obtain ⟨J,hJ⟩ := eventually_atTop.mp ht
    obtain ⟨j,hji,hbadj⟩ := hbad' (max i J)
    have hev : ∀ᶠ n in atTop, (i:ℝ)+1 ≤ z j n ∧ ∀ k : Fin (i+1),
        fluctuationScale μ S (z j n)*μ.real {x | dyadicCut (k:ℕ)*z j n < |S x|} < 1/((i:ℝ)+1) :=
      ((hz j).eventually_ge_atTop _).and (eventually_all.mpr (hJ j ((le_max_right ..).trans hji)))
    obtain ⟨N,hN⟩ := eventually_atTop.mp hev
    obtain ⟨n,hn,hbn⟩ := hbadj N
    refine ⟨j,n,(le_max_left ..).trans hji,(hN n hn).1,hbn,?_⟩
    intro k hk
    exact (hN n hn).2 ⟨k,by omega⟩
  choose j n hj hz0 hbadn htailn using hex
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have hztop : Tendsto (fun i => z (j i) (n i)) atTop atTop := by
    apply tendsto_atTop_mono (fun i : ℕ => (by linarith [hz0 i] : (i:ℝ) ≤ z (j i) (n i)))
    exact tendsto_natCast_atTop_atTop
  refine ⟨j,n,hjtop,?_,hbadn⟩
  apply isGaussianSequence_of_dyadic μ S _ hztop
    (Eventually.of_forall fun i => by have := hz0 i; linarith)
  intro k
  have hlim : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun i => mul_nonneg (fluctuationScale_nonneg μ S _) measureReal_nonneg)
  filter_upwards [eventually_ge_atTop k] with i hi
  exact (htailn i k hi).le

end DirectionalTransience

end

end

end OAI
