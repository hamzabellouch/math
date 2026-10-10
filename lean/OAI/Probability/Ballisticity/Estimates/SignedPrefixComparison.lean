import Mathlib
import OAI.Probability.Ballisticity.Estimates.ClippedAbsThreeHalves
import OAI.Probability.Ballisticity.Estimates.IidListProcess
import OAI.Probability.Ballisticity.Estimates.SharedEndpointTests

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma prefixVariation_signed_integral_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ=dot (realPosition y) ℓ) (H : ℝ)
    (F : Path d × Path d → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0≤M)
    (hFb : ∀ P, |F P|≤M)
    (W : HitWord x (Strip ℓ x H) (Upper ℓ x H) × HitWord y (Strip ℓ x H) (Upper ℓ x H) → ℝ)
    (hW : ∀ w P, P.1 ∈ RegularPath ℓ x → P.2 ∈ RegularPath ℓ y →
      P ∈ wordCylinder x w.1.val ×ˢ wordCylinder y w.2.val → F P=W w) :
    |(∫ P, F P ∂sharedConditionedPairLaw ν ℓ x y)-
      (∫ P, F P ∂(conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y))|≤
      (2*M)*prefixVariation ν ℓ x y H := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  let η := (conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans x y))
  let : IsProbabilityMeasure (conditionedFrom ν ℓ x) := conditionedFrom_probability ν ℓ x hp
  let : IsProbabilityMeasure (conditionedFrom ν ℓ y) := conditionedFrom_probability ν ℓ y hp
  have hi (σ : Measure (Path d × Path d)) [IsProbabilityMeasure σ] : Integrable F σ :=
    Integrable.mono' (integrable_const M) hF.aestronglyMeasurable (ae_of_all _ fun P => by
      simpa only [Real.norm_eq_abs] using hFb P)
  have hb := prefixVariation_integral_bound ν hue ℓ hℓ htrans x y hxy H (fun P => F P+M)
    (hF.add_const M) (show 0≤2*M by positivity)
    (fun P => by linarith [(abs_le.mp (hFb P)).1])
    (fun P => by linarith [(abs_le.mp (hFb P)).2]) (fun w => W w+M)
    (fun w P hx hy hw => by rw [hW w P hx hy hw])
  change |(∫ P, F P+M ∂μ)-(∫ P, F P+M ∂η)|≤_ at hb
  rw [integral_add (hi μ) (integrable_const _),integral_add (hi η) (integrable_const _)] at hb
  simpa only [integral_const,probReal_univ,one_smul,add_sub_add_right_eq_sub] using hb

lemma centeredFirstHit_on_hitWord {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ r : ℝ) {H : ℕ} (hH : 0<H)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H))
    (X : Path d) (hx : X ∈ RegularPath (realPosition (step e)) x)
    (hw : X ∈ wordCylinder x w.val) :
    centeredFirstHit (realPosition (step e)) f θ r H x X =
      (signedCoordinate f (wordPath x w.val w.val.length-x)-(H:ℝ)*θ)/r := by
  have hhit := hitWord_prefix x (Strip (realPosition (step e)) x H)
    (Upper (realPosition (step e)) x H) w hw
  have hrec := coordinate_hitAt_record e x X hx.1 hx.2.1 hH hhit
  simp only [centeredFirstHit,hrec,hw _ le_rfl]

lemma centeredPairTest_prefix_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (x y : Lattice d)
    (hxy : signedHeight e x=signedHeight e y) (θ r : ℝ) {H : ℕ} (hH : 0<H)
    (G₁ G₂ : ℝ →ᵇ ℝ) :
    |(∫ P, G₁ (centeredFirstHit (realPosition (step e)) f θ r H x P.1)*
        G₂ (centeredFirstHit (realPosition (step e)) f θ r H y P.2)
        ∂sharedConditionedPairLaw ν (realPosition (step e)) x y)-
      (∫ P, G₁ (centeredFirstHit (realPosition (step e)) f θ r H x P.1)*
        G₂ (centeredFirstHit (realPosition (step e)) f θ r H y P.2)
        ∂(conditionedFrom ν (realPosition (step e)) x).prod
          (conditionedFrom ν (realPosition (step e)) y))|≤
      (2*(‖G₁‖*‖G₂‖))*prefixVariation ν (realPosition (step e)) x y H := by
  let ℓ := realPosition (step e)
  have hhxy : dot (realPosition x) ℓ=dot (realPosition y) ℓ := by
    simp only [ℓ,signedHeight_projection,hxy]
  have hs : Strip ℓ x (H:ℝ)=Strip ℓ y (H:ℝ) := by unfold Strip; rw [hhxy]
  have ht : Upper ℓ x (H:ℝ)=Upper ℓ y (H:ℝ) := by unfold Upper; rw [hhxy]
  apply prefixVariation_signed_integral_bound ν hue ℓ (signed_direction_unit e) htrans x y hhxy H
    (fun P => G₁ (centeredFirstHit ℓ f θ r H x P.1)*G₂ (centeredFirstHit ℓ f θ r H y P.2))
    (((G₁.continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_fst).mul
      ((G₂.continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_snd))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun P => by rw [abs_mul]; exact mul_le_mul (G₁.norm_coe_le_norm _) (G₂.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _))
    (fun w => G₁ ((signedCoordinate f (wordPath x w.1.val w.1.val.length-x)-(H:ℝ)*θ)/r)*
      G₂ ((signedCoordinate f (wordPath y w.2.val w.2.val.length-y)-(H:ℝ)*θ)/r))
  intro w P hx hy hw
  rw [centeredFirstHit_on_hitWord e f x θ r hH w.1 P.1 hx hw.1]
  let w₂ : HitWord y (Strip ℓ y H) (Upper ℓ y H) := ⟨w.2.val,by simpa only [← hs,← ht] using w.2.property⟩
  rw [centeredFirstHit_on_hitWord e f y θ r hH w₂ P.2 hy hw.2]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma centeredFirstHit_integral_recenter {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (x : Lattice d) (G : ℝ →ᵇ ℝ) :
    (∫ X, G (centeredFirstHit ℓ f θ r H x X) ∂conditionedFrom ν ℓ x) =
      ∫ X, G (centeredFirstHit ℓ f θ r H 0 X) ∂conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedFrom ν ℓ x) :=
    conditionedFrom_probability ν ℓ x
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  have he : (conditionedFrom ν ℓ x).map (fun X : Path d => fun n => X n-x)=conditionedLaw ν ℓ := by
    ext A hA
    rw [Measure.map_apply hm hA]
    exact conditionedFrom_recenter ν ℓ x A hA
  rw [← he,integral_map hm.aemeasurable
    (show AEStronglyMeasurable (fun X : Path d => G (centeredFirstHit ℓ f θ r H 0 X))
      ((conditionedFrom ν ℓ x).map (fun X : Path d => fun n => X n-x)) from
      (Integrable.of_bound
        (G.continuous.measurable.comp (measurable_centeredFirstHit ℓ f θ r H 0)).aestronglyMeasurable
        ‖G‖ (ae_of_all _ fun path => G.norm_coe_le_norm _)).aestronglyMeasurable)]
  congr 1
  funext X
  simp only [centeredFirstHit,sub_zero]

lemma independent_centered_test_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    {t : ℝ} (ht : 0 < t) (G : ℝ →ᵇ ℝ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    Tendsto (fun i => ∫ X, G (centeredFirstHit ℓ f (θ i) (r i) ⌊t*n i⌋₊ 0 X) ∂conditionedLaw ν ℓ)
      atTop (𝓝 (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ hp
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  obtain ⟨W,hW,hWf⟩ := transverse_firstHit_linear_path_limit ν hue e f hef htrans r hr ht.le
  have hnpos : ∀ i, 0 < n i := fun i => recordFluctuationScale_pos ν hue e f hef htrans (hrpos i)
  have hn := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hf : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw (t*(1/(2*commonMeanWidth ν ℓ))) I := by
    intro I
    simpa only [div_eq_mul_inv,one_mul] using hWf I
  have hh := varying_height_path_gaussian_eval (fun _ => μ)
    (fun i h X => signedCoordinate f (recordIndexPosition ℓ h X)-(h:ℝ)*θ i)
    (fun i h => ((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ h)).sub_const _) r n hnpos t ht
    (1/(2*commonMeanWidth ν ℓ)) W hW hf (fun i => ⌊t*n i⌋₊)
    (fun i => Nat.floor_le (mul_pos ht (hnpos i)).le)
    ((tendsto_nat_floor_mul_div_atTop ht.le).comp hn)
  have hi := integral_bounded_test_tendsto (fun _ => μ) _
    (⟨gaussianReal 0 (Real.toNNReal ((1/(2*commonMeanWidth ν ℓ))*t)),inferInstance⟩ : ProbabilityMeasure ℝ) hh G
  simpa only [centeredFirstHit,sub_zero,ProbabilityMeasure.coe_mk,div_eq_mul_inv,one_mul,
    mul_comm ((2*commonMeanWidth ν ℓ)⁻¹)] using hi

lemma independent_centered_clip_product_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) {t : ℝ} (ht : 0 < t) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    Tendsto (fun i => ∫ P, symmetricClip w (centeredFirstHit ℓ f (θ i) (r i) ⌊t*n i⌋₊ (x i) P.1)*
      symmetricClip w (centeredFirstHit ℓ f (θ i) (r i) ⌊t*n i⌋₊ (y i) P.2)
      ∂(conditionedFrom ν ℓ (x i)).prod (conditionedFrom ν ℓ (y i))) atTop (𝓝 0) := by
  dsimp only
  have hi := independent_centered_test_limit ν hue e f hef htrans r hrpos hr ht (symmetricClip w)
  dsimp only at hi
  rw [symmetricClip_gaussian_integral] at hi
  have hh := hi.mul hi
  simp only [mul_zero] at hh
  apply hh.congr
  intro i
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
  let : IsProbabilityMeasure (conditionedFrom ν (realPosition (step e)) (x i)) := conditionedFrom_probability ν _ _ hp
  let : IsProbabilityMeasure (conditionedFrom ν (realPosition (step e)) (y i)) := conditionedFrom_probability ν _ _ hp
  let ℓ := realPosition (step e)
  let θ := recordMedianSlope ν ℓ hp f (r i)
  let H := ⌊t*fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)⌋₊
  have he := integral_prod_mul (μ := conditionedFrom ν ℓ (x i)) (ν := conditionedFrom ν ℓ (y i))
    (fun X : Path d => symmetricClip w (centeredFirstHit ℓ f θ (r i) H (x i) X))
    (fun X : Path d => symmetricClip w (centeredFirstHit ℓ f θ (r i) H (y i) X))
  rw [centeredFirstHit_integral_recenter ν _ htrans,centeredFirstHit_integral_recenter ν _ htrans] at he
  exact he.symm

end DirectionalTransience

end

end

end OAI
