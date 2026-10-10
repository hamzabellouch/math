import Mathlib
import OAI.Probability.SKFluctuations.PhysicalPinnedTransport

namespace OAI

/-! Physical Moment Order. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem integral_power_root_mono_mul {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : ∀ q, 0 ≤ f q) (hg0 : ∀ q, 0 ≤ g q) (hg : Measurable g)
    {R : ℝ} (hR : ∀ q, g q ≤ R) {A : ℝ} (hA : 0 ≤ A)
    (hfg : ∀ᵐ q ∂μ, f q ≤ A*g q) {l : ℕ} (hl : 0 < l) :
    (∫ q, f q^l ∂μ)^((l:ℝ)⁻¹) ≤ A*(∫ q, g q^l ∂μ)^((l:ℝ)⁻¹) := by
  have hi : Integrable (fun q => (A*g q)^l) μ :=
    Integrable.of_bound ((measurable_const.mul hg).pow_const l).aestronglyMeasurable
      ((A*R)^l) (Eventually.of_forall fun q => by
        rw [Real.norm_of_nonneg (pow_nonneg (mul_nonneg hA (hg0 q)) l)]
        exact pow_le_pow_left₀ (mul_nonneg hA (hg0 q)) (mul_le_mul_of_nonneg_left (hR q) hA) l)
  have hh : (∫ q, f q^l ∂μ) ≤ ∫ q, (A*g q)^l ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall fun q => pow_nonneg (hf q) l) hi
      (hfg.mono fun q hq => pow_le_pow_left₀ (hf q) hq l)
  have he := Real.rpow_le_rpow (integral_nonneg fun q => pow_nonneg (hf q) l) hh
    (inv_nonneg.mpr (Nat.cast_nonneg l))
  rwa [integral_weighted_power_root μ g hg0 hl hA] at he

 theorem physicalNearRadiusIntegral_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    (a b η : ℝ) : Measurable (physicalNearRadiusIntegral n steps x τ a b η) := by
  have h := physicalCutPairSquare_joint n steps hc x hx hτ.measurable hτ.measurable
      (hτ.measurable.comp (measurable_id.add_const η)) hτ.measurable
      (hτ.measurable.comp (measurable_id.add_const η))
  change Measurable (fun z : ℝ × PhysicalPathState P n steps =>
      physicalNearLayerSquare n steps x (τ z.1) (τ (z.1+η)) z.2) at h
  unfold physicalNearRadiusIntegral intervalIntegral
  exact ((h.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc a b))).measurable.sub
    ((h.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc b a))).measurable

 theorem physicalNearRadiusIntegral_bound (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    {a b : ℝ} (hab : a ≤ b) (η : ℝ) (q : PhysicalPathState P n steps) :
    physicalNearRadiusIntegral n steps x τ a b η q ≤ 16*(b-a) := by
  have hm : Measurable (fun s => physicalNearLayerSquare n steps x (τ s) (τ (s+η)) q) :=
    (physicalCutPairSquare_joint n steps hc x hx hτ.measurable hτ.measurable
      (hτ.measurable.comp (measurable_id.add_const η)) hτ.measurable
      (hτ.measurable.comp (measurable_id.add_const η))).comp (measurable_id.prodMk measurable_const)
  rw [physicalNearRadiusIntegral,intervalIntegral.integral_of_le hab]
  have hh := integral_mono_of_nonneg
    (Eventually.of_forall fun s => physicalNearLayerSquare_nonneg n steps x _ _ q)
    (integrable_const (16:ℝ) (μ := volume.restrict (Ioc a b)))
    (Eventually.of_forall fun s => physicalCutPairSquare_le n steps hc x hx (τ s) (τ s) (τ (s+η)) (τ s) (τ (s+η)) q)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),smul_eq_mul,mul_comm] using hh

 theorem physicalNearRadiusIntegral_raw (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η) (hk : τ (b+η) ≤ steps.length+1) :
    (∫ q, (physicalNearRadiusIntegral n steps x τ a b η q)^l
      ∂physicalPathLaw μ n steps x hx)^((l:ℝ)⁻¹) ≤
      4*(nearPairMomentConstant l)^((l:ℝ)⁻¹)*η*
        (physicalRawRatio n l steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2 := by
  have hh := physicalNearRadiusIntegral_Lp n steps hc μ x hx hτ hab hη hl
  have h0 : 0 ≤ ∫ q, ‖actualSpinPath n steps x (τ (b+η)) q‖^(4*l)
      ∂physicalPathLaw μ n steps x hx := integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hraw := Real.rpow_le_rpow h0
    (physicalRawRatio_moment n l hl steps hc hxs μ x hx hk) (inv_nonneg.mpr (Nat.cast_nonneg l))
  have hQ : 0 ≤ physicalRawRatio n l steps c xs μ x hx :=
    (by norm_num : (0:ℝ) ≤ 1).trans (physicalRawRatio_one_le n l steps c xs μ x hx)
  have hS : 0 ≤ xs+physicalCutMass c steps (τ (b+η)) :=
    add_nonneg hxs.le (physicalCutMass_mem steps hc _).1
  rw [show (physicalRawRatio n l steps c xs μ x hx)^(4*l)*
      (xs+physicalCutMass c steps (τ (b+η)))^(2*l) =
      ((physicalRawRatio n l steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2)^l by
        simp only [mul_pow,← pow_mul]] at hraw
  rw [Real.pow_rpow_inv_natCast (by positivity) hl.ne'] at hraw
  have hC := nearPairMomentConstant_nonneg l
  exact hh.trans (by simpa only [physicalPathLaw, mul_assoc] using
    mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 4*(nearPairMomentConstant l)^((l:ℝ)⁻¹)*η))

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalNear_mass_le_radius (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    {a b : ℝ} (hab : a ≤ b) (η : ℝ) (ζ : Measure ℝ) [IsFiniteMeasure ζ]
    {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hζ : ζ ≤ ENNReal.ofReal A • volume.restrict (Ioc a b))
    (m : ℝ → ℝ) (hm : ∀ᵐ s ∂ζ, m s ∈ Icc (0:ℝ) M)
    (q : PhysicalPathState P n steps) :
    (∫ s, m s*physicalNearLayerSquare n steps x (τ s) (τ (s+η)) q ∂ζ) ≤
      (M*A)*physicalNearRadiusIntegral n steps x τ a b η q := by
  let f : ℝ → ℝ := fun s => physicalNearLayerSquare n steps x (τ s) (τ (s+η)) q
  have hj := physicalCutPairSquare_joint n steps hc x hx hτ.measurable hτ.measurable
    (hτ.measurable.comp (measurable_id.add_const η)) hτ.measurable
    (hτ.measurable.comp (measurable_id.add_const η))
  have hf : Measurable f := hj.comp (measurable_id.prodMk measurable_const)
  have hf0 s : 0 ≤ f s := physicalNearLayerSquare_nonneg n steps x _ _ q
  have hfb s : f s ≤ 16 := physicalCutPairSquare_le n steps hc x hx (τ s) (τ s)
    (τ (s+η)) (τ s) (τ (s+η)) q
  have hi : Integrable f ζ := Integrable.of_bound hf.aestronglyMeasurable 16
    (Eventually.of_forall fun s => by rw [Real.norm_of_nonneg (hf0 s)]; exact hfb s)
  let := Measure.smul_finite (volume.restrict (Ioc a b)) (ENNReal.ofReal_ne_top (r := A))
  have hμi : Integrable f (ENNReal.ofReal A • volume.restrict (Ioc a b)) :=
    Integrable.of_bound hf.aestronglyMeasurable 16
      (Eventually.of_forall fun s => by rw [Real.norm_of_nonneg (hf0 s)]; exact hfb s)
  have hmass := integral_mono_measure hζ (Eventually.of_forall hf0) hμi
  rw [integral_smul_measure,ENNReal.toReal_ofReal hA,smul_eq_mul] at hmass
  have hfirst : (∫ s, m s*f s ∂ζ) ≤ M*(∫ s, f s ∂ζ) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (hm.mono fun s hs => mul_nonneg hs.1 (hf0 s))
      (hi.const_mul M) (hm.mono fun s hs => mul_le_mul_of_nonneg_right hs.2 (hf0 s))
  exact hfirst.trans (by
    simpa only [physicalNearRadiusIntegral,intervalIntegral.integral_of_le hab,mul_assoc] using
      mul_le_mul_of_nonneg_left hmass hM)

 theorem physicalNear_mass_raw (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {τ : ℝ → ℕ} (hτ : Monotone τ)
    {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η) (hk : τ (b+η) ≤ steps.length+1)
    (ζ : Measure ℝ) [IsFiniteMeasure ζ] {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hζ : ζ ≤ ENNReal.ofReal A • volume.restrict (Ioc a b))
    (m : ℝ → ℝ) (hm : ∀ᵐ s ∂ζ, m s ∈ Icc (0:ℝ) M) :
    (∫ q, (∫ s, m s*physicalNearLayerSquare n steps x (τ s) (τ (s+η)) q ∂ζ)^l
      ∂physicalPathLaw μ n steps x hx)^((l:ℝ)⁻¹) ≤
      M*A*(4*(nearPairMomentConstant l)^((l:ℝ)⁻¹)*η*
        (physicalRawRatio n l steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2) := by
  have := physicalPathLaw_finite μ n steps hc x hx
  have hh := integral_power_root_mono_mul (physicalPathLaw μ n steps x hx)
    (f := fun q => ∫ s, m s*physicalNearLayerSquare n steps x (τ s) (τ (s+η)) q ∂ζ)
    (g := physicalNearRadiusIntegral n steps x τ a b η)
    (fun q => integral_nonneg_of_ae (hm.mono fun s hs => mul_nonneg hs.1 (physicalNearLayerSquare_nonneg n steps x _ _ q)))
    (physicalNearRadiusIntegral_nonneg n steps x τ hab η)
    (physicalNearRadiusIntegral_measurable n steps hc x hx hτ a b η)
    (physicalNearRadiusIntegral_bound n steps hc x hx hτ hab η)
    (mul_nonneg hM hA)
    (Eventually.of_forall fun q => physicalNear_mass_le_radius n steps hc x hx hτ hab η ζ hA hM hζ m hm q) hl
  exact hh.trans (mul_le_mul_of_nonneg_left
    (physicalNearRadiusIntegral_raw n l hl steps hc hxs μ x hx hτ hab hη hk) (mul_nonneg hM hA))

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem integral_power_root_sum_le_card {I Ω : Type*} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : I → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (h0 : ∀ i q, 0 ≤ f i q)
    {R : ℝ} (hR : ∀ i q, f i q ≤ R) {l : ℕ} (hl : 0 < l)
    {L : ℝ} (hL : 0 ≤ L)
    (hLp : ∀ i, (∫ q, f i q^l ∂μ)^((l:ℝ)⁻¹) ≤ L) :
    (∫ q, (∑ i, f i q)^l ∂μ)^((l:ℝ)⁻¹) ≤ Fintype.card I*L := by
  have hh := integral_power_root_le_mass (Measure.count : Measure I) μ
    (fun z : I × Ω => f z.1 z.2) (measurable_from_prod_countable_right hf)
    (fun z => h0 z.1 z.2) (fun z => hR z.1 z.2) hl hL
    (Eventually.of_forall hLp)
  have hm : (Measure.count : Measure I).real univ = Fintype.card I := by
    rw [Measure.real,Measure.count_apply_finite univ (Set.toFinite univ)]
    simp
  simpa only [integral_count,hm] using hh

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalPairMassIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P A : Type} [MeasurableSpace A] (x : P → FeatureIndex n → ℝ)
    (ζ : Measure A) (m : A → ℝ) (fork v w d e : A → ℕ)
    (p : PhysicalPathState P n steps) : ℝ :=
    ∫ s, m s*physicalCutPairSquare n steps x (fork s) (v s) (w s) (d s) (e s) p ∂ζ

 theorem physicalPairMassIntegral_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (ζ : Measure A) [SFinite ζ]
    {m : A → ℝ} {fork v w d e : A → ℕ} (hm : Measurable m)
    (hf : Measurable fork) (hv : Measurable v) (hw : Measurable w)
    (hd : Measurable d) (he : Measurable e) :
    Measurable (physicalPairMassIntegral n steps x ζ m fork v w d e) := by
  have h := (hm.comp measurable_fst).mul (physicalCutPairSquare_joint n steps hc x hx hf hv hw hd he)
  exact (h.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable

 theorem physicalPairMassIntegral_nonneg (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P A : Type} [MeasurableSpace A] (x : P → FeatureIndex n → ℝ)
    (ζ : Measure A) (m : A → ℝ) (fork v w d e : A → ℕ) (hm : ∀ s, 0 ≤ m s)
    (p : PhysicalPathState P n steps) :
    0 ≤ physicalPairMassIntegral n steps x ζ m fork v w d e p :=
  integral_nonneg fun s => mul_nonneg (hm s) (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p)

 theorem physicalPairMassIntegral_le (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (ζ : Measure A) [IsFiniteMeasure ζ]
    (m : A → ℝ) (fork v w d e : A → ℕ) (hm : ∀ s, m s ∈ Icc (0:ℝ) 1)
    (p : PhysicalPathState P n steps) :
    physicalPairMassIntegral n steps x ζ m fork v w d e p ≤ ζ.real univ*16 := by
  have hpoint s : m s*physicalCutPairSquare n steps x (fork s) (v s) (w s) (d s) (e s) p ≤ 16 := by
    calc
      _ ≤ 1*physicalCutPairSquare n steps x (fork s) (v s) (w s) (d s) (e s) p :=
        mul_le_mul_of_nonneg_right (hm s).2 (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p)
      _ ≤ 16 := by simpa using physicalCutPairSquare_le n steps hc x hx _ _ _ _ _ p
  simpa only [physicalPairMassIntegral,integral_const,smul_eq_mul] using
    integral_mono_of_nonneg
      (Eventually.of_forall fun s => mul_nonneg (hm s).1 (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p))
      (integrable_const (16:ℝ) (μ := ζ)) (Eventually.of_forall hpoint)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_physical_pair_band_sum (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (τ : ℝ → ℕ), Monotone τ →
    ∀ (a b η : ℝ), a ≤ b → 0 < η → τ (b+η) ≤ steps.length+1 →
    ∀ (ζ : Measure ℝ) [IsFiniteMeasure ζ] (A M : ℝ), 0 ≤ A → 0 ≤ M →
      ζ ≤ ENNReal.ofReal A • volume.restrict (Ioc a b) →
    ∀ (K : ℕ) (m : Fin (K+1) → ℝ → ℝ) (v w : Fin (K+1) → ℝ → ℕ),
      (∀ i, Measurable (m i)) → (∀ i, Measurable (v i)) → (∀ i, Measurable (w i)) →
      (∀ i s, m i s ∈ Icc (0:ℝ) 1) → (∀ᵐ s ∂ζ, m 0 s ≤ M) →
      v 0 = τ → w 0 = (fun s => τ (s+η)) →
      (∀ i j, i ≠ 0 ∨ j ≠ 0 → ∀ᵐ s ∂ζ,
        HasFarPairClock n steps c xs D₀ B H (m j s) (τ s) (v i s) (w i s) (v j s) (w j s)) →
    (∫ p, (∑ i : Fin (K+1), ∑ j : Fin (K+1),
      physicalPairMassIntegral n steps x ζ (m j) τ (v i) (w i) (v j) (w j) p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (K+1:ℕ)^2 *
        (M*A*(4*(nearPairMomentConstant (k+1))^(((k+1:ℕ):ℝ)⁻¹)*η*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2) +
        ζ.real univ*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))) := by
  filter_upwards [eventually_physical_far_mass_integral k B] with n hn
  intro P _ steps c D₀ xs H hD₀ hxs hH hs μ _ x hx τ hτ a b η hab hη hk ζ _ A M hA hM hζ K m v w hm hv hw hm01 hmM hv0 hw0 hclock
  have := physicalPathLaw_finite μ n steps hs x hx
  let near := M*A*(4*(nearPairMomentConstant (k+1))^(((k+1:ℕ):ℝ)⁻¹)*η*
    (physicalRawRatio n (k+1) steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2)
  let far := ζ.real univ*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
    (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))
  have hC := nearPairMomentConstant_nonneg (k+1)
  have hnear : 0 ≤ near := by dsimp [near]; positivity
  have hfar : 0 ≤ far := by dsimp [far]; positivity
  let f : (Fin (K+1) × Fin (K+1)) → PhysicalPathState P n steps → ℝ := fun i =>
    physicalPairMassIntegral n steps x ζ (m i.2) τ (v i.1) (w i.1) (v i.2) (w i.2)
  have hfm i : Measurable (f i) := physicalPairMassIntegral_measurable n steps hs x hx ζ
    (hm i.2) hτ.measurable (hv i.1) (hw i.1) (hv i.2) (hw i.2)
  have hf0 i p : 0 ≤ f i p := physicalPairMassIntegral_nonneg n steps x ζ
    (m i.2) τ (v i.1) (w i.1) (v i.2) (w i.2) (fun s => (hm01 i.2 s).1) p
  have hfB i p : f i p ≤ ζ.real univ*16 := physicalPairMassIntegral_le n steps hs x hx ζ
    (m i.2) τ (v i.1) (w i.1) (v i.2) (w i.2) (hm01 i.2) p
  have hroot i : (∫ p, f i p^(k+1) ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤ near+far := by
    by_cases hi : i.1=0 ∧ i.2=0
    · rcases hi with ⟨hi,hj⟩
      have hh := physicalNear_mass_raw n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hτ
        hab hη hk ζ hA hM hζ (m 0) (hmM.mono fun s hs => ⟨(hm01 0 s).1,hs⟩)
      apply le_trans _ (le_add_of_nonneg_right hfar)
      simpa only [f,physicalPairMassIntegral,hi,hj,hv0,hw0,physicalNearLayerSquare,physicalCutPairSquare,physicalCutIncrement,near] using hh
    · have hh := hn P ℝ steps c D₀ xs H hD₀ hxs hH hs μ ζ x hx
        (m i.2) τ (v i.1) (w i.1) (v i.2) (w i.2)
        (hm i.2) hτ.measurable (hv i.1) (hw i.1) (hv i.2) (hw i.2) (hm01 i.2)
        (hclock i.1 i.2 (by tauto))
      exact hh.trans (le_add_of_nonneg_left hnear)
  have hh := integral_power_root_sum_le_card (physicalPathLaw μ n steps x hx) f hfm hf0 hfB
    (Nat.succ_pos k) (add_nonneg hnear hfar) hroot
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two,Fintype.sum_prod_type,f,near,far] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalSusceptibilityMassIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P A : Type} [MeasurableSpace A] (x : P → FeatureIndex n → ℝ)
    (ζ : Measure A) (τ : A → ℕ) (p : PhysicalPathState P n steps) : ℝ :=
    ∫ s, physicalCutSusceptibility n steps x (τ s) p ∂ζ

 theorem physicalSusceptibilityMassIntegral_le_array (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P A : Type} [MeasurableSpace P] [MeasurableSpace A]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (ζ : Measure A) [IsFiniteMeasure ζ]
    {K : ℕ} (m : Fin (K+1) → A → ℝ) (t : Fin (K+2) → A → ℕ)
    (hm : ∀ i, Measurable (m i)) (ht : ∀ i, Measurable (t i))
    (hm01 : ∀ i s, m i s ∈ Icc (0:ℝ) 1)
    (hdata : ∀ᵐ s ∂ζ,
      t (Fin.last (K+1)) s = steps.length+1 ∧ m (Fin.last K) s=1 ∧
      CutPartition steps (t 0 s) (List.ofFn fun i : Fin K => (m i.castSucc s,t i.succ.castSucc s)) ∧
      ∀ B ∈ layersOfCuts steps (t 0 s)
        (List.ofFn fun i : Fin K => (m i.castSucc s,t i.succ.castSucc s)), ∀ st ∈ B.2, st.1 ≤ B.1)
    (p : PhysicalPathState P n steps) :
    physicalSusceptibilityMassIntegral n steps x ζ (t 0) p ≤
      (K+1:ℕ)*(∑ i : Fin (K+1), ∑ j : Fin (K+1),
        physicalPairMassIntegral n steps x ζ (m j) (t 0) (t i.castSucc) (t i.succ)
          (t j.castSucc) (t j.succ) p) := by
  let f : Fin (K+1) → Fin (K+1) → A → ℝ := fun i j s =>
    m j s*physicalCutPairSquare n steps x (t 0 s) (t i.castSucc s) (t i.succ s)
      (t j.castSucc s) (t j.succ s) p
  have hi i j : Integrable (f i j) ζ := by
    have hjoint : Measurable (f i j) := (hm j).mul ((physicalCutPairSquare_joint n steps hc x hx (ht 0)
      (ht i.castSucc) (ht i.succ) (ht j.castSucc) (ht j.succ)).comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : A => p))))
    apply Integrable.of_bound hjoint.aestronglyMeasurable 16
    filter_upwards [] with s
    rw [Real.norm_of_nonneg (mul_nonneg (hm01 j s).1 (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p))]
    exact (mul_le_mul_of_nonneg_right (hm01 j s).2
      (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p)).trans
      (by simpa using physicalCutPairSquare_le n steps hc x hx _ _ _ _ _ p)
  have hi' : Integrable (fun s => (K+1:ℕ)*(∑ i : Fin (K+1), ∑ j : Fin (K+1), f i j s)) ζ :=
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))).const_mul _
  have hh := integral_mono_of_nonneg
    (Eventually.of_forall fun s => physicalCutSusceptibility_nonneg n steps hc x (t 0 s) p)
    hi' (hdata.mono fun s h => physicalCutSusceptibility_le_array n steps hc
      (fun i => m i s) (fun i => t i s) h.1 h.2.1 h.2.2.1 h.2.2.2 x p)
  simp only [integral_const_mul] at hh
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))] at hh
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)] at hh
  exact hh

 theorem eventually_physical_susceptibility_band (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ xs H : ℝ),
      0 < D₀ → 0 < xs → 0 ≤ H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (τ : ℝ → ℕ), Monotone τ →
    ∀ (a b η : ℝ), a ≤ b → 0 < η → τ (b+η) ≤ steps.length+1 →
    ∀ (ζ : Measure ℝ) [IsFiniteMeasure ζ] (A M : ℝ), 0 ≤ A → 0 ≤ M →
      ζ ≤ ENNReal.ofReal A • volume.restrict (Ioc a b) →
    ∀ (K : ℕ) (m : Fin (K+1) → ℝ → ℝ) (t : Fin (K+2) → ℝ → ℕ),
      (∀ i, Measurable (m i)) → (∀ i, Measurable (t i)) →
      (∀ i s, m i s ∈ Icc (0:ℝ) 1) → (∀ᵐ s ∂ζ, m 0 s ≤ M) →
      t 0 = τ → t 1 = (fun s => τ (s+η)) →
      (∀ᵐ s ∂ζ,
        t (Fin.last (K+1)) s = steps.length+1 ∧ m (Fin.last K) s=1 ∧
        CutPartition steps (t 0 s) (List.ofFn fun i : Fin K => (m i.castSucc s,t i.succ.castSucc s)) ∧
        ∀ B ∈ layersOfCuts steps (t 0 s)
          (List.ofFn fun i : Fin K => (m i.castSucc s,t i.succ.castSucc s)), ∀ st ∈ B.2, st.1 ≤ B.1) →
      (∀ i j : Fin (K+1), i ≠ 0 ∨ j ≠ 0 → ∀ᵐ s ∂ζ,
        HasFarPairClock n steps c xs D₀ B H (m j s) (τ s)
          (t i.castSucc s) (t i.succ s) (t j.castSucc s) (t j.succ s)) →
    (∫ p, (physicalSusceptibilityMassIntegral n steps x ζ τ p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (K+1:ℕ)^3 *
        (M*A*(4*(nearPairMomentConstant (k+1))^(((k+1:ℕ):ℝ)⁻¹)*η*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^4*(xs+physicalCutMass c steps (τ (b+η)))^2) +
        ζ.real univ*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
          (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))) := by
  filter_upwards [eventually_physical_pair_band_sum k B] with n hn
  intro P _ steps c D₀ xs H hD₀ hxs hH hs μ _ x hx τ hτ a b η hab hη hk ζ _ A M hA hM hζ K m t hm ht hm01 hmM ht0 ht1 hdata hclock
  have := physicalPathLaw_finite μ n steps hs x hx
  let f (i j : Fin (K+1)) := physicalPairMassIntegral n steps x ζ (m j) τ
    (t i.castSucc) (t i.succ) (t j.castSucc) (t j.succ)
  have hfm i j : Measurable (f i j) := physicalPairMassIntegral_measurable n steps hs x hx ζ
    (hm j) hτ.measurable (ht i.castSucc) (ht i.succ) (ht j.castSucc) (ht j.succ)
  have hf0 i j p : 0 ≤ f i j p := physicalPairMassIntegral_nonneg n steps x ζ
    (m j) τ (t i.castSucc) (t i.succ) (t j.castSucc) (t j.succ) (fun s => (hm01 j s).1) p
  have hfB i j p : f i j p ≤ ζ.real univ*16 := physicalPairMassIntegral_le n steps hs x hx ζ
    (m j) τ (t i.castSucc) (t i.succ) (t j.castSucc) (t j.succ) (hm01 j) p
  have hh := integral_power_root_mono_mul (physicalPathLaw μ n steps x hx)
    (fun p => integral_nonneg fun s => physicalCutSusceptibility_nonneg n steps hs x (τ s) p)
    (fun p => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf0 i j p)
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hfm i j)
    (fun p => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hfB i j p)
    (Nat.cast_nonneg (K+1)) (Eventually.of_forall fun p => by
      simpa only [ht0,f,physicalSusceptibilityMassIntegral] using physicalSusceptibilityMassIntegral_le_array n steps hs x hx ζ m t hm ht hm01 hdata p)
    (Nat.succ_pos k)
  have hsum := hn P steps c D₀ xs H hD₀ hxs hH hs μ x hx τ hτ a b η hab hη hk ζ A M hA hM hζ K m
    (fun i => t i.castSucc) (fun i => t i.succ) hm (fun i => ht i.castSucc) (fun i => ht i.succ)
    hm01 hmM (by simpa using ht0) (by simpa using ht1) hclock
  exact hh.trans ((mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (K+1))).trans_eq (by ring))

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 def physicalWindowMass {ι : Type} (steps : List (GaussianStep ι)) (a : ℝ)
    (J : Finset (Fin (steps.length+1))) : ℝ := ∑ j ∈ J, pathMassDifferences steps a j

 def physicalWindowWeight {ι : Type} (steps : List (GaussianStep ι)) (a : ℝ)
    (J : Finset (Fin (steps.length+1))) (j : Fin (steps.length+1)) : ℝ :=
    if j ∈ J then (physicalWindowMass steps a J)⁻¹ else 0

 def physicalWindowCellMass {ι : Type} (steps : List (GaussianStep ι)) (a : ℝ)
    (J : Finset (Fin (steps.length+1))) (j : Fin (steps.length+1)) : ℝ :=
    if j ∈ J then pathMassDifferences steps a j else 0

 theorem physicalWindowWeight_nonneg {ι : Type} (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (J : Finset (Fin (steps.length+1))) (j : Fin (steps.length+1)) :
    0 ≤ physicalWindowWeight steps a J j := by
  unfold physicalWindowWeight
  split_ifs
  · exact inv_nonneg.mpr (Finset.sum_nonneg fun i _ => pathMassDifferences_nonneg steps ha i)
  · exact le_rfl

 theorem physicalWindowWeight_normalized {ι : Type} (steps : List (GaussianStep ι)) (a : ℝ)
    (J : Finset (Fin (steps.length+1))) (hv : 0 < physicalWindowMass steps a J) :
    ∑ j, pathMassDifferences steps a j*physicalWindowWeight steps a J j=1 := by
  simp only [physicalWindowWeight,mul_ite,mul_zero]
  rw [Finset.sum_ite_mem,Finset.univ_inter,← Finset.sum_mul]
  exact mul_inv_cancel₀ hv.ne'

 theorem physicalWindowCellMass_nonneg {ι : Type} (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (J : Finset (Fin (steps.length+1))) (j : Fin (steps.length+1)) :
    0 ≤ physicalWindowCellMass steps a J j := by
  unfold physicalWindowCellMass
  split_ifs
  · exact pathMassDifferences_nonneg steps ha j
  · exact le_rfl

 theorem physical_radius_window_energy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ)
    {P : Type} (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n steps) :
    (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps a (physicalWindowWeight steps a J) (x p.1) p.2).2 =
      (physicalWindowMass steps a J)⁻¹^2 *
        physicalSusceptibilityMassIntegral n steps x
          (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
            (physicalWindowCellMass steps a J)) (radiusGridCut r) p := by
  rw [physicalPinnedPair_snd_eq_sum n steps ha]
  unfold physicalSusceptibilityMassIntegral
  rw [integral_radiusCellMeasure_allow_zero _ _ _
    (fun j => or_iff_not_imp_left.mpr (hc j)) (physicalWindowCellMass_nonneg steps ha J)
    _ (fun j => physicalCutSusceptibility n steps x j.val p)
    (fun j s hs => by rw [radiusGridCut_cell r hr j hs])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold physicalWindowWeight physicalWindowCellMass
  split_ifs <;> ring

 theorem physical_radius_window_cap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (a : ℝ)
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ)
    {A l u : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ j, physicalWindowCellMass steps a J j ≤ A*(r j.succ-r j.castSucc))
    (hband : ∀ j, physicalWindowCellMass steps a J j ≠ 0 →
      Ioc (r j.castSucc) (r j.succ) ⊆ Ioc l u) :
    radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
      (physicalWindowCellMass steps a J) ≤ ENNReal.ofReal A • volume.restrict (Ioc l u) :=
    radiusCellMeasure_le_allow_zero _ _ _ (fun j => or_iff_not_imp_left.mpr (hc j)) hA
      hcap (radiusGridCell_disjoint r hr) hband

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem radiusCellMeasure_real_univ {I : Type} [Fintype I] (a b w : I → ℝ)
    (hab : ∀ i, w i = 0 ∨ a i < b i) (hw : ∀ i, 0 ≤ w i) :
    (radiusCellMeasure a b w).real univ = ∑ i, w i := by
  have h := integral_radiusCellMeasure_allow_zero a b w hab hw (fun _ => (1:ℝ))
    (fun _ => (1:ℝ)) (fun _ _ _ => rfl)
  simpa only [integral_const,smul_eq_mul,mul_one] using h

theorem physical_radius_window_mass {n : ℕ} (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ) :
    (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
      (physicalWindowCellMass steps a J)).real univ = physicalWindowMass steps a J := by
  rw [radiusCellMeasure_real_univ _ _ _ (fun j => or_iff_not_imp_left.mpr (hc j))
    (physicalWindowCellMass_nonneg steps ha J)]
  classical
  simp only [physicalWindowCellMass,physicalWindowMass,Finset.sum_ite_mem,Finset.univ_inter]

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def dyadicLayerScale (s : ℝ) (i : ℕ) : ℝ := (2:ℝ)^(i-1)*s

@[simp] theorem dyadicLayerScale_zero (s : ℝ) : dyadicLayerScale s 0=s := by simp [dyadicLayerScale]
@[simp] theorem dyadicLayerScale_one (s : ℝ) : dyadicLayerScale s 1=s := by simp [dyadicLayerScale]

theorem dyadicLayerScale_monotone {s : ℝ} (hs : 0 ≤ s) : Monotone (dyadicLayerScale s) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.sub_le_sub_right hij 1)) hs

theorem le_dyadicLayerScale {s : ℝ} (hs : 0 ≤ s) (i : ℕ) : s ≤ dyadicLayerScale s i := by
  simpa only [dyadicLayerScale_zero] using dyadicLayerScale_monotone hs (Nat.zero_le i)

theorem dyadicLayerScale_pos {s : ℝ} (hs : 0 < s) (i : ℕ) : 0 < dyadicLayerScale s i := by
  unfold dyadicLayerScale; positivity

theorem dyadicRadiusNode_le_twice_scale {s η : ℝ} (hηs : η ≤ s) (i : ℕ) :
    dyadicRadiusNode s η (i+1) ≤ 2*dyadicLayerScale s i := by
  cases i with
  | zero => simp; linarith
  | succ i =>
    rw [show i+1+1=i+2 by omega,dyadicRadiusNode_succ_succ]
    simp only [dyadicLayerScale,Nat.add_sub_cancel,pow_succ]
    ring_nf
    exact le_rfl

theorem dyadicRadiusNode_ge_scale {s η : ℝ} (hη : 0 ≤ η) (i : ℕ) :
    dyadicLayerScale s i ≤ dyadicRadiusNode s η i := by
  rcases i with _ | i
  · simp
  rcases i with _ | i
  · simp; exact hη
  · simp [dyadicRadiusNode,dyadicLayerScale]

theorem physicalDyadicMass_scale_bound (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs s η C R F : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 ≤ xs) (hxs_s : xs ≤ s) (hs : 0 < s)
    (hη : 0 ≤ η) (hηs : η ≤ s) (hC : 0 ≤ C) (hR : 0 < R)
    (hF₁ : 1+2*C ≤ F) (hF₂ : 1+1/R ≤ F)
    {J : ℕ} (hJ : 1 ≤ J) (τ : ℝ → ℕ) (hτ : Monotone τ)
    (hRend : R ≤ (2:ℝ)^J*s)
    (hm : ∀ r ∈ Icc s ((2:ℝ)^J*s), physicalCutMass c steps (τ r) ≤ C*r)
    (i : Fin (J+3)) :
    xs+physicalDyadicMass steps c J τ η i s ≤ F*dyadicLayerScale s i.val := by
  have hq := dyadicLayerScale_pos hs i.val
  have hxsq := hxs_s.trans (le_dyadicLayerScale (hxs.trans hxs_s) i.val)
  by_cases hi : i.val ≤ J
  · have hnode : dyadicRadiusNode s η (i.val+1) ∈ Icc s ((2:ℝ)^J*s) := by
      constructor
      · simpa only [dyadicRadiusNode_zero] using
          dyadicRadiusNode_monotone hs.le hη hηs (Nat.zero_le (i.val+1))
      · have hh := dyadicRadiusNode_monotone hs.le hη hηs (show i.val+1 ≤ J+1 by omega)
        have he : dyadicRadiusNode s η (J+1) = (2:ℝ)^J*s := by
          simp only [dyadicRadiusNode,show J+1 ≠ 0 by omega,show J+1 ≠ 1 by omega,↓reduceIte,Nat.add_sub_cancel]
        simpa only [he] using hh
    have he : physicalDyadicMass steps c J τ η i s =
        physicalCutMass c steps (τ (dyadicRadiusNode s η (i.val+1))) := by
      simp only [physicalDyadicMass,physicalDyadicCuts,Fin.val_succ,dyadicCutIndex,
        show i.val+1 ≤ J+1 by omega,↓reduceIte]
    rw [he]
    have hnode_le : dyadicRadiusNode s η (i.val+1) ≤
        min (2*dyadicLayerScale s i.val) ((2:ℝ)^J*s) :=
      le_min (dyadicRadiusNode_le_twice_scale hηs i.val) hnode.2
    have hh := ((physicalCutMass_monotone steps hc) (hτ hnode_le)).trans
      ((hm _ ⟨hnode.1.trans hnode_le,min_le_right _ _⟩).trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hC))
    calc
      xs+physicalCutMass c steps (τ (dyadicRadiusNode s η (i.val+1))) ≤
          dyadicLayerScale s i.val+C*(2*dyadicLayerScale s i.val) := add_le_add hxsq hh
      _ = (1+2*C)*dyadicLayerScale s i.val := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hF₁ hq.le
  · have hRq : R ≤ dyadicLayerScale s i.val := by
      apply hRend.trans
      have hh := dyadicLayerScale_monotone hs.le (show J+1 ≤ i.val by omega)
      simpa only [dyadicLayerScale,Nat.add_sub_cancel] using hh
    have hmass := (physicalCutMass_mem steps hc
      (physicalDyadicCuts J τ steps.length η i.succ s)).2
    have hlarge : 1 ≤ dyadicLayerScale s i.val/R := (le_div_iff₀ hR).2 (by simpa using hRq)
    calc
      _ ≤ dyadicLayerScale s i.val+1 := add_le_add hxsq hmass
      _ ≤ dyadicLayerScale s i.val+dyadicLayerScale s i.val/R := add_le_add le_rfl hlarge
      _ = (1+1/R)*dyadicLayerScale s i.val := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hF₂ hq.le

end SKFluctuations

end

end OAI
