import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularGainTranslationTests
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianWeightedConvergence

namespace OAI

section

/-! # The physical linear gain operator on incoming pair densities -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

local instance pairGainSphereSFinite : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite

def pairPreRate (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1

def pairPostRate (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ := pairPreRate g (scatterTriple z)

def pairGain (g : X × (Velocity × Velocity) → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, pairPostRate g (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

omit [MeasurableSpace X] in
theorem pairPostRate_scatter (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate g (scatterTriple z) = pairPreRate g z := by
  unfold pairPostRate
  rw [scatterTriple_involutive z]

theorem pairPreRate_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (pairPreRate g) := by
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · exact hg.comp measurable_fst

theorem pairGain_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (pairGain g) := by
  exact (((pairPreRate_measurable hg).comp scatterTriple_measurable).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem pairGain_integrable {μ : Measure X} [SFinite μ]
    {g : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (pairGain g) (μ.prod volume) := by
  have hp := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi
  change Integrable (pairPostRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) at hp
  have hh := (collision_test_marginal (pairPostRate g) (fun _ => (1:ℝ))
    (by simpa only [one_mul] using hp)).1
  change Integrable (fun p => ∫ q : Velocity × Sphere,
    pairPostRate g (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)
      (μ.prod volume)
  simpa only [one_mul] using hh

theorem pairGain_test {μ : Measure X} [SFinite μ]
    {g : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) :
    (∫ p, ψ p*pairGain g p ∂μ.prod volume) =
      ∫ z, g z*angularFamily ψ z ∂μ.prod (volume : Measure (Velocity × Velocity)) := by
  have hp := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi
  have htest : Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ (z.1.1,z.1.2.1)*pairPostRate g z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
    hp.bdd_mul (hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).aestronglyMeasurable
      (ae_of_all _ (fun z => hC _))
  unfold pairGain
  rw [(collision_test_marginal (pairPostRate g) ψ htest).2]
  have he := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z : (X × (Velocity × Velocity)) × Sphere => ψ (z.1.1,z.1.2.1)*pairPostRate g z)
  have hfun : (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z)) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*pairPreRate g z) := by
    funext z
    rw [pairPostRate_scatter]
    rfl
  change (∫ z, ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z)
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) = _ at he
  rw [hfun] at he
  rw [← he]
  have hsi := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable htest
  change Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
    ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) at hsi
  rw [hfun] at hsi
  rw [integral_prod _ hsi]
  apply integral_congr_ae
  filter_upwards [] with z
  change (∫ n : Sphere, ψ (z.1,scatterLeft z.2.1 z.2.2 n)*
    (collisionKernel z.2.1 z.2.2 n*g z) ∂sphereArea) = _
  calc
    _ = ∫ n : Sphere, g z*(collisionKernel z.2.1 z.2.2 n*
        ψ (z.1,scatterLeft z.2.1 z.2.2 n)) ∂sphereArea := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _ = _ := integral_const_mul _ _

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # L1 contraction from physical collision rates to gain densities -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance pairGainL1Sphere : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite

theorem pairGain_eLpNorm_le {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (pairGain g) 1 (μ.prod volume) ≤
      eLpNorm (pairPreRate g) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hm := ((pairPreRate_measurable hg).comp scatterTriple_measurable).comp
    collisionGrouping.symm.measurable
  have h := Compactness.eLpNorm_integral_le (μ := μ.prod volume)
    (ν := (volume : Measure Velocity).prod sphereArea) hm
  change eLpNorm (pairGain g) 1 (μ.prod volume) ≤ _ at h
  apply h.trans_eq
  rw [eLpNorm_comp_measurePreserving
    ((pairPreRate_measurable hg).comp scatterTriple_measurable).aestronglyMeasurable
    (collisionGrouping_measurePreserving μ).symm]
  exact eLpNorm_comp_measurePreserving (pairPreRate_measurable hg).aestronglyMeasurable
    (scatterTriple_measurePreserving μ)

theorem pairGain_sub_ae {g h : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hj : Integrable (pairPreRate h) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    pairGain (fun z => g z-h z) =ᵐ[μ.prod volume] fun p => pairGain g p-pairGain h p := by
  have hgi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi)
  have hhi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((scatterTriple_measurePreserving μ).integrable_comp_of_integrable hj)
  filter_upwards [hgi.prod_right_ae,hhi.prod_right_ae] with p hp hq
  change (∫ q : Velocity × Sphere, pairPostRate (fun z => g z-h z) (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea) = _
  have he q : pairPostRate (fun z => g z-h z) (collisionGrouping.symm (p,q)) =
      pairPostRate g (collisionGrouping.symm (p,q))-pairPostRate h (collisionGrouping.symm (p,q)) := by
    simp only [pairPostRate,pairPreRate,mul_sub]
  simp_rw [he]
  exact integral_sub hp hq

theorem pairGain_difference_eLpNorm_le {g h : X × (Velocity × Velocity) → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hj : Integrable (pairPreRate h) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    eLpNorm (fun p => pairGain g p-pairGain h p) 1 (μ.prod volume) ≤
      eLpNorm (fun z => pairPreRate g z-pairPreRate h z) 1
        ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  rw [← eLpNorm_congr_ae (pairGain_sub_ae hi hj)]
  have ht := pairGain_eLpNorm_le (μ := μ) (hg.sub hh)
  have he : pairPreRate (g-h) = (fun z => pairPreRate g z-pairPreRate h z) := by
    funext z
    change collisionKernel _ _ _*(g z.1-h z.1) = _
    exact mul_sub _ _ _
  rw [he] at ht
  exact ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The relative-velocity cutoff error vanishes under the product Gaussian moment -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

def relativeCutoff (b : ℝ) (f : Velocity × Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  if ‖p.1-p.2‖ < b then f p else 0

theorem relativeCutoff_measurable {f : Velocity × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (relativeCutoff b f) :=
  hf.ite (measurableSet_lt ((measurable_fst.sub measurable_snd).norm) measurable_const) measurable_const

theorem relativeCutoff_gaussian_error {b L : ℝ} (hb : 2 ≤ b) (hL : 0 ≤ L)
    {f : Velocity × Velocity → ℝ} (hf : ∀ p, |f p| ≤ L*(1+‖p.1‖+‖p.2‖))
    (p : Velocity × Velocity) :
    |relativeCutoff b f p-f p| ≤ (12*L/b)*(weight p.1*weight p.2) := by
  have hbp : 0 < b := by linarith
  unfold relativeCutoff
  split_ifs with hp
  · rw [sub_self,abs_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hL) hbp.le)
      (mul_nonneg (weight_pos _).le (weight_pos _).le)
  · rw [zero_sub,abs_neg]
    have hrel := le_of_not_gt hp
    have hsum := norm_sub_le p.1 p.2
    have htail : b/2 ≤ ‖p.1‖ ∨ b/2 ≤ ‖p.2‖ := by
      by_cases h : b/2 ≤ ‖p.1‖
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have hrate := pair_rate_le_gaussian_tail (by linarith : 1 ≤ b/2) p.1 p.2 htail
    have hmul := mul_le_mul_of_nonneg_left hrate hL
    have hf' := mul_le_mul_of_nonneg_left (hf p) (by positivity : 0 ≤ b/2)
    calc
      _ ≤ (12*L*(weight p.1*weight p.2))/b := (le_div_iff₀ hbp).mpr (by nlinarith)
      _ = _ := by ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The linear velocity moment controls the physical pair-to-gain operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def momentPair (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (1+‖z.2.1‖+‖z.2.2‖)*g z

theorem momentPair_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (momentPair g) := by
  unfold momentPair
  fun_prop

omit [SFinite μ] in
theorem pair_lift_eLpNorm_one {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (fun z : (X × (Velocity × Velocity)) × Sphere => g z.1) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      sphereArea univ*eLpNorm g 1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => g z.1) :=
    hg.comp measurable_fst
  rw [eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
    lintegral_prod _ hm.enorm.aemeasurable]
  simp only [lintegral_const]
  rw [lintegral_mul_const _ hg.enorm,mul_comm]

omit [SFinite μ] in
theorem pairPreRate_moment_norm_le {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (pairPreRate g) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      sphereArea univ*eLpNorm (momentPair g) 1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
  rw [← pair_lift_eLpNorm_one (momentPair_measurable hg)]
  apply eLpNorm_mono_ae (pairPreRate_measurable hg).aestronglyMeasurable
  filter_upwards [] with z
  change ‖collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1‖ ≤
    ‖(1+‖z.1.2.1‖+‖z.1.2.2‖)*g z.1‖
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (collisionKernel_nonneg _ _ _),
    Real.norm_of_nonneg (by positivity : 0 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖)]
  exact mul_le_mul_of_nonneg_right
    ((collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith)))
    (norm_nonneg _)

omit [SFinite μ] in
theorem pairPreRate_integrable_of_moment {g : X × (Velocity × Velocity) → ℝ}
    (hg : Measurable g) (hi : Integrable (momentPair g) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply memLp_one_iff_integrable.mp
  exact (pairPreRate_moment_norm_le hg).trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
    (memLp_one_iff_integrable.mpr hi))

theorem pairGain_moment_difference_le {g h : X × (Velocity × Velocity) → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hi : Integrable (momentPair g) (μ.prod (volume : Measure (Velocity × Velocity))))
    (hj : Integrable (momentPair h) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    eLpNorm (fun p => pairGain g p-pairGain h p) 1 (μ.prod volume) ≤
      sphereArea univ*eLpNorm (momentPair (fun z => g z-h z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) := by
  apply (pairGain_difference_eLpNorm_le hg hh (pairPreRate_integrable_of_moment hg hi)
    (pairPreRate_integrable_of_moment hh hj)).trans
  have he : (fun z => pairPreRate g z-pairPreRate h z) = pairPreRate (fun z => g z-h z) := by
    funext z
    exact (mul_sub _ _ _).symm
  rw [he]
  exact pairPreRate_moment_norm_le (hg.sub hh)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded compact truncation in the incoming pair moment norm -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def momentVelocityCut (R : ℝ) (g : X × (Velocity × Velocity) → ℝ) : X × (Velocity × Velocity) → ℝ :=
  (univ ×ˢ incomingBall R).indicator (momentPair g)

def boundedPairCut (R : ℝ) (B : ℝ≥0) (g : X × (Velocity × Velocity) → ℝ)
    (z : X × (Velocity × Velocity)) : ℝ := by
  classical
  exact if z.2 ∈ incomingBall R ∧ ‖momentPair g z‖ < (B:ℝ) then g z else 0

theorem incomingBall_measurable (R : ℝ) : MeasurableSet (incomingBall R) :=
  Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet

theorem boundedPairCut_measurable (R : ℝ) (B : ℝ≥0)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (boundedPairCut R B g) := by
  unfold boundedPairCut
  apply hg.ite _ measurable_const
  exact ((incomingBall_measurable R).preimage measurable_snd).inter
    (measurableSet_lt (momentPair_measurable hg).norm measurable_const)

omit [MeasurableSpace X] in
theorem boundedPairCut_bound (R : ℝ) (B : ℝ≥0)
    (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity)) :
    |boundedPairCut R B g z| ≤ B := by
  unfold boundedPairCut
  split_ifs with h
  · have hw : 1 ≤ 1+‖z.2.1‖+‖z.2.2‖ := by linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
    have hnorm : ‖g z‖ ≤ ‖momentPair g z‖ := by
      rw [momentPair,norm_mul,Real.norm_of_nonneg (by linarith : 0 ≤ 1+‖z.2.1‖+‖z.2.2‖)]
      nlinarith [norm_nonneg (g z)]
    have hlt : ‖momentPair g z‖ < (B:ℝ) := h.2
    exact hnorm.trans hlt.le
  · simp only [abs_zero,NNReal.coe_nonneg]

omit [MeasurableSpace X] in
theorem boundedPairCut_support (R : ℝ) (B : ℝ≥0)
    (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity))
    (hz : z.2 ∉ incomingBall R) : boundedPairCut R B g z = 0 := by
  simp only [boundedPairCut,hz,false_and,ite_false]

theorem boundedPairCut_moment_error {μ : Measure X} (R : ℝ) (B : ℝ≥0)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (momentPair (fun z => g z-boundedPairCut R B g z)) 1 (μ.prod volume) ≤
      eLpNorm (fun z => momentPair g z-momentVelocityCut R g z) 1 (μ.prod volume)+
      eLpNorm (({z | (B:ℝ) ≤ ‖momentPair g z‖}).indicator (momentPair g)) 1 (μ.prod volume) := by
  classical
  let A : Set (X × (Velocity × Velocity)) := {z | (B:ℝ) ≤ ‖momentPair g z‖}
  have he : momentPair (fun z => g z-boundedPairCut R B g z) =
      (fun z => momentPair g z-momentVelocityCut R g z)+A.indicator (momentVelocityCut R g) := by
    funext z
    simp only [Pi.add_apply,momentVelocityCut,Set.indicator_apply,mem_prod,mem_univ,true_and,A,mem_ofPred_eq]
    change (1+‖z.2.1‖+‖z.2.2‖)*(g z-
      (if z.2 ∈ incomingBall R ∧ ‖momentPair g z‖ < (B:ℝ) then g z else 0)) =
      (momentPair g z-(if z.2 ∈ incomingBall R then momentPair g z else 0))+
      (if (B:ℝ) ≤ ‖momentPair g z‖ then (if z.2 ∈ incomingBall R then momentPair g z else 0) else 0)
    by_cases hz : z.2 ∈ incomingBall R <;> by_cases ht : ‖momentPair g z‖ < (B:ℝ)
    all_goals
      simp only [← not_lt,hz,ht,not_true_eq_false,not_false_eq_true,ite_true,ite_false,
        and_true,and_false,sub_self,sub_zero,mul_zero,zero_add,add_zero] <;> rfl
  rw [he]
  apply (eLpNorm_add_le (by norm_num)).trans
  apply add_le_add_right
  have hvm : Measurable (momentVelocityCut R g) :=
    (momentPair_measurable hg).indicator (MeasurableSet.univ.prod (incomingBall_measurable R))
  have hAm : MeasurableSet A := measurableSet_le
    (measurable_const : Measurable (fun _ : X × (Velocity × Velocity) => (B:ℝ)))
    (momentPair_measurable hg).norm
  apply eLpNorm_mono_ae (hvm.indicator hAm).aestronglyMeasurable
  filter_upwards [] with z
  change ‖A.indicator (momentVelocityCut R g) z‖ ≤ ‖A.indicator (momentPair g) z‖
  by_cases hA : z ∈ A
  · simp only [indicator_of_mem hA,momentVelocityCut]
    exact norm_indicator_le_norm_self _ _
  · simp only [indicator_of_notMem hA,norm_zero,le_refl]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
