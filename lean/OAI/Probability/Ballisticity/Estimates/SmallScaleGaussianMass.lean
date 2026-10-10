import Mathlib
import OAI.Probability.Ballisticity.Estimates.VarianceTailDifference
import OAI.Probability.Ballisticity.Coupling.GaussianQuenchedMass

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma dyadic_inv_tendsto : Tendsto (fun j => (dyadicCut j)⁻¹) atTop atTop :=
  tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
    ⟨dyadicCut_tendsto,Eventually.of_forall dyadicCut_pos⟩)

theorem small_scale_gaussian_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let μ := independentConditionedPairLaw ν ℓ
    let S := commonIncrementProcess ℓ f 0
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop atTop →
      ∀ (F : ℕ → ℝ) (F₀ : ℝ), 0 < F₀ → (∀ j, F₀ ≤ F j) → Tendsto F atTop (𝓝 F₀) →
      (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j))) →
      ∀ b : ℝ, 0 < b → ∀ x : Lattice d, ∀ δ : ℝ, 0 < δ →
        ∀ᶠ j in atTop, ∀ᶠ n in atTop,
          (environmentLaw ν).real {ω |
            (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊:ℕ) ω).real
              (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊
                (b*r n) (ρ*(dyadicCut j*r n))) < c} < δ := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  obtain ⟨c,hc,hGaussian⟩ := gaussian_quenched_mass ν hue e f hef htrans hρ
  refine ⟨c,hc,?_⟩
  intro r hr hrinf F F₀ hF₀ hFle hFlim hF b hb x δ hδ
  let z := fun j n => dyadicCut j*r n
  let bad := fun j n => (environmentLaw ν).real {ω |
    (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (z j n)⌋₊:ℕ) ω).real
      (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (z j n)⌋₊ (b*r n) (ρ*z j n)) < c}
  change ∀ᶠ j in atTop, ∀ᶠ n in atTop, bad j n < δ
  by_contra hbad
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have htail := dyadic_profile_gaussian_tail μ S (measurable_commonIncrementProcess ℓ f 0) hne r hr F hF₀ hFle hF hFlim
  obtain ⟨j,n,hj,hGauss,hbadn⟩ := double_gaussian_selection μ S z
    (fun j => hrinf.const_mul_atTop (dyadicCut_pos j)) (fun k δ hδ => htail k hδ) bad hbad
  have hbStar : Tendsto (fun i => b/dyadicCut (j i)) atTop atTop := by
    simpa only [div_eq_mul_inv,Function.comp_apply] using (dyadic_inv_tendsto.comp hj).const_mul_atTop hb
  have hconc := hGaussian (fun i => z (j i) (n i)) hGauss (fun i => b/dyadicCut (j i)) hbStar x
  have heq (i) : (b/dyadicCut (j i))*z (j i) (n i) = b*r (n i) := by
    dsimp [z]
    field_simp [ne_of_gt (dyadicCut_pos (j i))]
  simp only [heq] at hconc
  have hconc' : Tendsto (fun i => bad (j i) (n i)) atTop (𝓝 0) := hconc
  obtain ⟨i,hi⟩ := (hconc'.eventually (gt_mem_nhds hδ)).exists
  exact (not_lt_of_ge (hbadn i)) hi

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def bandTruncate (z R x : ℝ) : ℝ := symmetricTruncate R x-symmetricTruncate z x
lemma measurable_bandTruncate (z R : ℝ) : Measurable (bandTruncate z R) :=
  (measurable_symmetricTruncate R).sub (measurable_symmetricTruncate z)
lemma bandTruncate_bound {z R : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) (x : ℝ) : |bandTruncate z R x| ≤ R := by
  unfold bandTruncate symmetricTruncate
  by_cases hxz : |x| ≤ z
  · simp only [ite_eq_left hxz,ite_eq_left (hxz.trans hzR),sub_self,abs_zero]
    exact hz.trans hzR
  · simp only [ite_eq_right hxz,sub_zero]
    split_ifs with hxR
    · exact hxR
    · simpa using hz.trans hzR
lemma bandTruncate_neg (z R x : ℝ) : bandTruncate z R (-x) = -bandTruncate z R x := by
  simp only [bandTruncate,symmetricTruncate_neg]; ring

lemma bandTruncate_cost_identity {z R : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) (x : ℝ) :
    (bandTruncate z R x)^2+truncatedTailCost R x =
    min (x^2) (R^2)-min (x^2) (z^2)+truncatedTailCost z x := by
  have hs := sq_abs x
  have hx := abs_nonneg x
  unfold bandTruncate symmetricTruncate truncatedTailCost
  by_cases hxz : |x| ≤ z
  · have hxR := hxz.trans hzR
    simp only [ite_eq_left hxz,ite_eq_left hxR,ite_eq_right (not_lt.mpr hxz),ite_eq_right (not_lt.mpr hxR),sub_self,zero_pow (by norm_num : 2 ≠ 0),add_zero]
    rw [min_eq_left (by nlinarith : x^2 ≤ R^2),min_eq_left (by nlinarith : x^2 ≤ z^2),sub_self]
  · have hzx : z < |x| := lt_of_not_ge hxz
    by_cases hxR : |x| ≤ R
    · simp only [ite_eq_left hxR,ite_eq_right hxz,ite_eq_right (not_lt.mpr hxR),ite_eq_left hzx,sub_zero,add_zero]
      rw [min_eq_left (by nlinarith : x^2 ≤ R^2),min_eq_right (by nlinarith : z^2 ≤ x^2)]
      ring
    · have hRx : R < |x| := lt_of_not_ge hxR
      simp only [ite_eq_right hxz,ite_eq_right hxR,ite_eq_left hzx,ite_eq_left hRx,sub_self,zero_pow (by norm_num : 2 ≠ 0),zero_add]
      rw [min_eq_right (by nlinarith : R^2 ≤ x^2),min_eq_right (by nlinarith : z^2 ≤ x^2)]
      ring

lemma integral_truncatedTailCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (z : ℝ) :
    (∫ x, truncatedTailCost z (S x) ∂μ) = z^2*μ.real {x | z < |S x|} := by
  change (∫ x, ({x | z < |S x|}).indicator (fun _ => z^2) x ∂μ) = _
  rw [integral_indicator (measurableSet_lt measurable_const hS.abs)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]

lemma integrable_bandTruncate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {z R : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) : Integrable (fun x => bandTruncate z R (S x)) μ :=
  integrable_of_abs_bound μ _ ((measurable_bandTruncate z R).comp hS) R
    (fun sample => bandTruncate_bound hz hzR (S sample))

lemma integral_bandTruncate_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (z R : ℝ)
    (hsym : IdentDistrib S (fun x => -S x) μ μ) :
    ∫ x, bandTruncate z R (S x) ∂μ = 0 := by
  have hh := (hsym.comp (measurable_bandTruncate z R)).integral_eq
  change (∫ x, bandTruncate z R (S x) ∂μ) = (∫ x, bandTruncate z R (-S x) ∂μ) at hh
  simp only [bandTruncate_neg,integral_neg] at hh
  linarith

lemma integral_bandTruncate_cost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {z R : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) :
    (∫ x, (bandTruncate z R (S x))^2 ∂μ)+R^2*μ.real {x | R < |S x|} =
    truncatedVariance μ S R-truncatedVariance μ S z+z^2*μ.real {x | z < |S x|} := by
  have hB : Integrable (fun x => (bandTruncate z R (S x))^2) μ :=
    integrable_of_abs_bound μ _ (((measurable_bandTruncate z R).comp hS).pow_const 2) (R^2)
      (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (bandTruncate_bound hz hzR _) 2)
  have hT (a : ℝ) : Integrable (fun x => truncatedTailCost a (S x)) μ := by
    apply integrable_of_abs_bound μ _ ((measurable_truncatedTailCost a).comp hS) (a^2)
    intro x
    change |truncatedTailCost a (S x)| ≤ a^2
    unfold truncatedTailCost
    split_ifs <;> simp [abs_of_nonneg (sq_nonneg a),sq_nonneg a]
  rw [← integral_truncatedTailCost μ S hS R,← integral_add hB (hT R)]
  simp only [bandTruncate_cost_identity hz hzR]
  change (∫ a, ((fun x => min (S x^2) (R^2)) - (fun x => min (S x^2) (z^2))) a + truncatedTailCost z (S a) ∂μ) = _
  rw [integral_add ((integrable_truncated_square μ S hS R).sub (integrable_truncated_square μ S hS z)) (hT z)]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrable_truncated_square μ S hS R) (integrable_truncated_square μ S hS z),integral_truncatedTailCost μ S hS z]
  rfl

end DirectionalTransience

end

end

end OAI
