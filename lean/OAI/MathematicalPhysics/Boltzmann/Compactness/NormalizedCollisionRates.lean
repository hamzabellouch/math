import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakLinearMomentLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # The first-velocity-moment weight of the normalized pair is integrable -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairVelocityWeight (z : X × (Velocity × Velocity)) : ℝ := 1+‖z.2.1‖+‖z.2.2‖

def weightedNormalizedPair (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  pairVelocityWeight z*normalizedPair volume f z

theorem pairVelocityWeight_measurable : Measurable (pairVelocityWeight (X := X)) := by
  unfold pairVelocityWeight
  fun_prop

theorem weightedNormalizedPair_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (weightedNormalizedPair f) :=
  pairVelocityWeight_measurable.mul
    (normalizedTensor_measurable (fiberMass_measurable (ν := volume) hfm) hfm hfm)

theorem normalizedTensor_integrable_swap {d : X → ℝ} {f g : X × Velocity → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (normalizedTensor d g f) (μ.prod (volume.prod volume))) :
    Integrable (normalizedTensor d f g) (μ.prod (volume.prod volume)) := by
  apply memLp_one_iff_integrable.mp
  change eLpNorm (normalizedTensor d f g) 1 (μ.prod (volume.prod volume)) < ∞
  rw [normalizedTensor_norm_swap hd hf hg]
  exact memLp_one_iff_integrable.mpr hi

theorem weightedNormalizedPair_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume)) :
    Integrable (weightedNormalizedPair f) (μ.prod (volume.prod volume)) := by
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hli := linearMoment_integrable hfm hf hi
  have hdm := fiberMass_measurable (ν := volume) hfm
  have hdn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hlm := linearMoment_measurable hfm
  have hln (p : X × Velocity) : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  have hr := normalizedTensor_integrable hdm hdn hfm hlm hf hln hfi hli
    (ae_of_all _ (fun _ => le_rfl))
  have hl := normalizedTensor_integrable_swap hdm hlm hfm hr
  have hp := normalizedPair_integrable hfm hf hfi
  apply ((hl.add hr).sub hp).congr
  filter_upwards [] with z
  dsimp only [Pi.sub_apply,Pi.add_apply,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor,linearMoment]
  ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Entropy controls the complete mass-normalized velocity pair -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

private theorem bounded_nonnegative_product_div {a b A B r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hr : 0 ≤ r) :
    |a*b/(1+r)| ≤ A*B := by
  rw [abs_of_nonneg (div_nonneg (mul_nonneg ha hb) (by linarith))]
  apply (div_le_iff₀ (by linarith : 0 < 1+r)).mpr
  exact (mul_le_mul hA hB hb hA0).trans (by nlinarith [mul_nonneg (mul_nonneg hA0 hB0) hr])

theorem normalized_entropyTruncation_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z) :
    UniformIntegrable (fun n => normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
      (μ.prod (volume.prod volume)) := by
  let a : Velocity → ℝ := (Metric.closedBall (0:Velocity) R).indicator (fun _ => Real.exp R)
  have hai : Integrable a := (integrableOn_const
    (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet
  have ha0 v : 0 ≤ a v := indicator_nonneg (fun _ _ => (Real.exp_pos R).le) v
  have hub (n : ℕ) (p : X × Velocity) : entropyTruncation R (f n) p ≤ a p.2 := by
    by_cases hp : p.2 ∈ Metric.closedBall 0 R
    · rw [show a p.2 = Real.exp R from indicator_of_mem hp _]
      exact (entropyTruncation_bounds R (hf n) p).2
    · have hv : R < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [entropyTruncation_support R (f n) p hv,show a p.2 = 0 from indicator_of_notMem hp _]
  let b : X × (Velocity × Velocity) → ℝ := fun z => a z.2.1*a z.2.2
  have hbi : Integrable b (μ.prod (volume.prod volume)) := (hai.mul_prod hai).comp_snd μ
  have hbui := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num) (memLp_one_iff_integrable.mpr hbi)
  have hm n : Measurable (normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n))
      (entropyTruncation_measurable R (hfm n)) (entropyTruncation_measurable R (hfm n))
  have hdom (n : ℕ) (z : X × (Velocity × Velocity)) :
      ‖normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n)) z‖ ≤ b z := by
    change |entropyTruncation R (f n) (z.1,z.2.1)*entropyTruncation R (f n) (z.1,z.2.2)/
      (1+fiberMass volume (f n) z.1)| ≤ a z.2.1*a z.2.2
    exact bounded_nonnegative_product_div (entropyTruncation_bounds R (hf n) _).1
      (entropyTruncation_bounds R (hf n) _).1 (hub n _) (hub n _) (ha0 _) (ha0 _)
      (integral_nonneg (fun v => hf n (z.1,v)))
  have hmono (n : ℕ) (s : Set (X × (Velocity × Velocity))) :
      eLpNorm (normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
        ((μ.prod (volume.prod volume)).restrict s) ≤ eLpNorm b 1 ((μ.prod (volume.prod volume)).restrict s) :=
    eLpNorm_mono_real (hm n).aestronglyMeasurable (hdom n)
  refine ⟨unifIntegrable_iff.mpr ?_,?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,hδb⟩ := unifIntegrable_iff.mp hbui.1 ε hε
    exact ⟨δ,hδ,fun n s hs => (hmono n s).trans (hδb n s hs)⟩
  · obtain ⟨K,hK⟩ := hbui.2
    refine ⟨K,fun n => ?_⟩
    simpa only [Measure.restrict_univ] using (hmono n univ).trans
      (by simpa only [Measure.restrict_univ] using hK n)

theorem normalizedPair_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ z, entropyGauge (f n) z ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => normalizedPair volume (f n)) 1 (μ.prod (volume.prod volume)) := by
  let u := fun (j n : ℕ) => entropyTruncation ((j:ℝ)+1) (f n)
  apply uniformIntegrable_of_approximation
    (g := fun j n => normalizedTensor (fiberMass volume (f n)) (u j n) (u j n))
  · exact fun j => normalized_entropyTruncation_uniformIntegrable ((j:ℝ)+1) hfm hf
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    refine ⟨j,fun n => ?_⟩
    have hR : 1 ≤ (j:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have he := normalizedPair_truncation_error (hfm n)
      (entropyTruncation_measurable ((j:ℝ)+1) (hfm n)) (hf n)
      (fun p => (entropyTruncation_bounds ((j:ℝ)+1) (hf n) p).1)
      (fun p => by
        unfold entropyTruncation
        split_ifs
        · exact le_rfl
        · exact hf n p)
      (integrable_of_entropyGauge (hfm n) (hf n) (hi n))
      (entropyTruncation_integrable ((j:ℝ)+1) (hfm n) (hf n))
    calc
      _ ≤ 2*eLpNorm (fun z => f n z-u j n z) 1 (μ.prod volume) := he
      _ ≤ 2*ENNReal.ofReal (C/((j:ℝ)+1)) := mul_le_mul' le_rfl
        (entropyTruncation_L1_bound hR (hfm n) (hf n) (hi n) (hb n))
      _ = ENNReal.ofReal ((2*C)/((j:ℝ)+1)) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ ε := hj

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform velocity-tail control of the moment-weighted normalized pair -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairVelocityCut (R : ℝ) (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then weightedNormalizedPair f z else 0

theorem pairVelocityCut_measurable (R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (pairVelocityCut R f) :=
  (weightedNormalizedPair_measurable hfm).ite
    ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
      (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const

private theorem tail_coeff_bound {R a b : ℝ} (hR : 0 ≤ R) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (if a ≤ R ∧ b ≤ R then 0 else 1+a+b) ≤
      2*((if a ≤ R then 0 else 1+a)+(if b ≤ R then 0 else 1+b)) := by
  by_cases har : a ≤ R <;> by_cases hbr : b ≤ R <;>
    simp only [har,hbr,and_self,ite_true,ite_false,false_and,and_false,
      zero_add,add_zero] <;> (try linarith)

omit [MeasurableSpace X] in
private theorem tail_density_nonneg (R : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ linearMoment f p-velocityLinearCut R f p := by
  dsimp only [velocityLinearCut]
  split_ifs
  · simp only [sub_self,le_refl]
  · simp only [sub_zero,linearMoment]
    exact mul_nonneg (by positivity) (hf p)

omit [MeasurableSpace X] in
theorem pairVelocityCut_pointwise_error {R : ℝ} (hR : 0 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : X × (Velocity × Velocity)) :
    |weightedNormalizedPair f z-pairVelocityCut R f z| ≤
      2*(normalizedTensor (fiberMass volume f)
          (fun p => linearMoment f p-velocityLinearCut R f p) f z+
        normalizedTensor (fiberMass volume f) f
          (fun p => linearMoment f p-velocityLinearCut R f p) z) := by
  have hd : 0 < 1+fiberMass volume f z.1 := by
    have hm : 0 ≤ fiberMass volume f z.1 := integral_nonneg (fun v => hf (z.1,v))
    linarith
  have hprod : 0 ≤ f (z.1,z.2.1)*f (z.1,z.2.2) := mul_nonneg (hf _) (hf _)
  have hc := mul_le_mul_of_nonneg_right (tail_coeff_bound hR (norm_nonneg z.2.1) (norm_nonneg z.2.2)) hprod
  have hdiv := div_le_div_of_nonneg_right hc hd.le
  by_cases hv : ‖z.2.1‖ ≤ R <;> by_cases hw : ‖z.2.2‖ ≤ R
  all_goals
    simp only [weightedNormalizedPair,pairVelocityCut,pairVelocityWeight,normalizedPair,
      normalizedTensor,linearMoment,velocityLinearCut,hv,hw,and_self,
      ite_true,ite_false,false_and,and_false,sub_self,sub_zero,zero_mul,mul_zero,zero_div,
      zero_add,add_zero,abs_zero] at hdiv ⊢
  · exact le_refl _
  all_goals
    rw [abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg hprod hd.le))]
    convert hdiv using 1 <;> ring

theorem pairVelocityCut_L1_error {R C : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun z => weightedNormalizedPair f z-pairVelocityCut R f z) 1
      (μ.prod (volume.prod volume)) ≤ ENNReal.ofReal (8*C/R) := by
  let d : X × Velocity → ℝ := fun p => linearMoment f p-velocityLinearCut R f p
  have hdm : Measurable d := (linearMoment_measurable hfm).sub (velocityLinearCut_measurable R hfm)
  have hdi : Integrable d (μ.prod volume) :=
    (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hm := fiberMass_measurable (ν := volume) hfm
  have hmn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hd0 : ∀ p, 0 ≤ d p := tail_density_nonneg R hf
  have hright := normalizedTensor_L1_le hm hmn hfm hdm hf hd0 hfi hdi (ae_of_all _ (fun _ => le_rfl))
  have hleft : eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume)) ≤
      eLpNorm d 1 (μ.prod volume) := by
    rw [normalizedTensor_norm_swap hm hdm hfm]
    exact hright
  have hs_nonneg (z : X × (Velocity × Velocity)) :
      0 ≤ normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z := by
    have hden : 0 ≤ 1+fiberMass volume f z.1 := by linarith [hmn z.1]
    exact add_nonneg (div_nonneg (mul_nonneg (hd0 _) (hf _)) hden)
      (div_nonneg (mul_nonneg (hf _) (hd0 _)) hden)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ.prod (volume.prod volume))
    ((weightedNormalizedPair_measurable hfm).sub (pairVelocityCut_measurable R hfm)).aestronglyMeasurable
    (g := fun z => normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z)
    (c := 2) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,Real.norm_of_nonneg (hs_nonneg z)]
      exact pairVelocityCut_pointwise_error hR.le hf z)) 1
  calc
    _ ≤ 2*(eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume))+
        eLpNorm (normalizedTensor (fiberMass volume f) f d) 1 (μ.prod (volume.prod volume))) := by
      exact hnorm.trans (by norm_num; exact mul_le_mul' le_rfl (eLpNorm_add_le (by norm_num)))
    _ ≤ 2*(eLpNorm d 1 (μ.prod volume)+eLpNorm d 1 (μ.prod volume)) :=
      mul_le_mul' le_rfl (add_le_add hleft hright)
    _ ≤ 2*(ENNReal.ofReal (2*C/R)+ENNReal.ofReal (2*C/R)) :=
      mul_le_mul' le_rfl (add_le_add (velocityLinearCut_L1_error hR hfm hf hi hb)
        (velocityLinearCut_L1_error hR hfm hf hi hb))
    _ = ENNReal.ofReal (8*C/R) := by
      have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hf)).trans hb
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Passing the first-velocity-moment weight through normalized-pair convergence -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

private def boundedPairWeight (R : ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then pairVelocityWeight z else 0

private theorem boundedPairWeight_measurable (R : ℝ) :
    Measurable (boundedPairWeight (X := X) R) :=
  pairVelocityWeight_measurable.ite
    ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
      (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const

omit [MeasurableSpace X] in
private theorem boundedPairWeight_bound {R : ℝ} (hR : 0 ≤ R) (z : X × (Velocity × Velocity)) :
    |boundedPairWeight R z| ≤ 1+2*R := by
  dsimp only [boundedPairWeight]
  split_ifs with hz
  · rw [abs_of_nonneg (show 0 ≤ pairVelocityWeight z by dsimp [pairVelocityWeight]; positivity)]
    dsimp only [pairVelocityWeight]
    linarith [hz.1,hz.2]
  · simp only [abs_zero]
    linarith

omit [MeasurableSpace X] in
private theorem pairVelocityCut_eq_mul (R : ℝ) (f : X × Velocity → ℝ) :
    pairVelocityCut R f = fun z => boundedPairWeight R z*normalizedPair volume f z := by
  funext z
  dsimp only [pairVelocityCut,boundedPairWeight,weightedNormalizedPair]
  split_ifs <;> simp only [zero_mul]

theorem weak_weightedNormalizedPair
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hfb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (hgb : (∫ p, entropyGauge g p ∂μ.prod volume) ≤ C)
    (h : Published.WeakL1Converges (μ.prod (volume.prod volume))
      (fun n => normalizedPair volume (f n)) (normalizedPair volume g)) :
    Published.WeakL1Converges (μ.prod (volume.prod volume))
      (fun n => weightedNormalizedPair (f n)) (weightedNormalizedPair g) := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+1
  have hR j : 0 < R j := by dsimp [R]; positivity
  have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hg)).trans hgb
  have hcut j : Published.WeakL1Converges (μ.prod (volume.prod volume))
      (fun n => pairVelocityCut (R j) (f n)) (pairVelocityCut (R j) g) := by
    have hw := h.bounded_mul (boundedPairWeight_measurable (R j)) (1+2*R j)
      (boundedPairWeight_bound (hR j).le)
    simpa only [pairVelocityCut_eq_mul] using hw
  have hcuti j n : Integrable (pairVelocityCut (R j) (f n)) (μ.prod (volume.prod volume)) := by
    have hw := weightedNormalizedPair_integrable (hfm n) (hf n) (hfi n)
    have hs : MeasurableSet {z : X × (Velocity × Velocity) | ‖z.2.1‖ ≤ R j ∧ ‖z.2.2‖ ≤ R j} :=
      (measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
        (measurableSet_le (measurable_snd.snd.norm) measurable_const)
    apply (hw.indicator hs).congr
    filter_upwards [] with z
    by_cases hz : ‖z.2.1‖ ≤ R j ∧ ‖z.2.2‖ ≤ R j <;> simp [pairVelocityCut,Set.indicator,hz]
  apply Published.WeakL1Converges.of_L1_approximations
    (fun n => weightedNormalizedPair_integrable (hfm n) (hf n) (hfi n))
    (weightedNormalizedPair_measurable hgm) (weightedNormalizedPair_integrable hgm hg hgi)
    hcuti hcut (δ := fun j => 8*C/R j) (fun j => by positivity)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · exact fun j n => pairVelocityCut_L1_error (hR j) (hfm n) (hf n) (hfi n) (hfb n)
  · intro j
    change eLpNorm (pairVelocityCut (R j) g-weightedNormalizedPair g) 1 _ ≤ _
    rw [eLpNorm_sub_comm]
    exact pairVelocityCut_L1_error (hR j) hgm hg hgi hgb

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Velocity tightness of the actual mass-normalized pairs -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedPair_entropy_error {f : X × Velocity → ℝ} {R C : ℝ}
    (hR : 1 ≤ R) (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ z, entropyGauge f z ∂μ.prod volume) ≤ C) :
    eLpNorm (fun z => normalizedPair volume f z-
      normalizedTensor (fiberMass volume f) (entropyTruncation R f) (entropyTruncation R f) z)
      1 (μ.prod (volume.prod volume)) ≤ ENNReal.ofReal (2*C/R) := by
  have huf p : entropyTruncation R f p ≤ f p := by
    unfold entropyTruncation
    split_ifs
    · exact le_rfl
    · exact hf p
  have he := normalizedPair_truncation_error hfm (entropyTruncation_measurable R hfm) hf
    (fun p => (entropyTruncation_bounds R hf p).1) huf (integrable_of_entropyGauge hfm hf hi)
    (entropyTruncation_integrable R hfm hf)
  refine he.trans ((mul_le_mul' le_rfl (entropyTruncation_L1_bound hR hfm hf hi hb)).trans_eq ?_)
  rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

omit [MeasurableSpace X] in
private theorem truncated_pair_support (R : ℝ) (f : X × Velocity → ℝ)
    (z : X × (Velocity × Velocity))
    (hz : z ∉ Set.univ ×ˢ (Metric.closedBall (0:Velocity) R ×ˢ Metric.closedBall (0:Velocity) R)) :
    normalizedTensor (fiberMass volume f) (entropyTruncation R f) (entropyTruncation R f) z = 0 := by
  change entropyTruncation R f (z.1,z.2.1)*entropyTruncation R f (z.1,z.2.2)/
    (1+fiberMass volume f z.1) = 0
  by_cases hv : ‖z.2.1‖ ≤ R
  · have hw : R < ‖z.2.2‖ := by
      by_contra! hn
      exact hz ⟨mem_univ _,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv,
        by simpa only [Metric.mem_closedBall,dist_zero_right] using hn⟩
    rw [entropyTruncation_support R f (z.1,z.2.2) hw,mul_zero,zero_div]
  · rw [entropyTruncation_support R f (z.1,z.2.1) (lt_of_not_ge hv),zero_mul,zero_div]

theorem normalizedPair_unifTight {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ z, entropyGauge (f n) z ∂μ.prod volume) ≤ C) :
    UnifTight (fun n => normalizedPair volume (f n)) 1 (μ.prod (volume.prod volume)) := by
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
  let R : ℝ := (j:ℝ)+1
  let b : Set Velocity := Metric.closedBall 0 R
  let s : Set (X × (Velocity × Velocity)) := univ ×ˢ (b ×ˢ b)
  have hR : 1 ≤ R := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hs : MeasurableSet s := MeasurableSet.univ.prod
    (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet)
  refine ⟨s,?_,fun n => ?_⟩
  · dsimp only [s]
    rw [Measure.prod_prod,Measure.prod_prod]
    have hbfin : volume b ≠ ⊤ := (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) (ENNReal.mul_ne_top hbfin hbfin)
  · let u := entropyTruncation R (f n)
    have hzero z (hz : z ∉ s) : normalizedTensor (fiberMass volume (f n)) u u z = 0 :=
      truncated_pair_support R (f n) z hz
    have hdom z : ‖sᶜ.indicator (normalizedPair volume (f n)) z‖ ≤
        ‖normalizedPair volume (f n) z-normalizedTensor (fiberMass volume (f n)) u u z‖ := by
      by_cases hz : z ∈ s
      · rw [indicator_of_notMem (notMem_compl_iff.mpr hz),norm_zero]
        exact norm_nonneg _
      · rw [indicator_of_mem (mem_compl hz),hzero z hz,sub_zero]
    have hm := normalizedTensor_measurable (fiberMass_measurable (ν := volume) (hfm n)) (hfm n) (hfm n)
    exact (eLpNorm_mono (hm.indicator hs.compl).aestronglyMeasurable hdom).trans
      ((normalizedPair_entropy_error hR (hfm n) (hf n) (hi n) (hb n)).trans hj)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual pre- and post-collision rates normalized by the spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def massNormalizedPreRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  preRate f z/(1+fiberMass volume f z.1.1)

def massNormalizedPostRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  postRate f z/(1+fiberMass volume f z.1.1)

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = normalizedKernel z*weightedNormalizedPair f z.1 := by
  rw [massNormalizedPreRate,preRate_eq_normalized]
  dsimp only [pairDensity,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor]
  ring

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq_fun (f : X × Velocity → ℝ) :
    massNormalizedPreRate f = fun z => normalizedKernel z*weightedNormalizedPair f z.1 :=
  funext (massNormalizedPreRate_eq f)

omit [MeasurableSpace X] in
theorem massNormalizedPostRate_eq (f : X × Velocity → ℝ) :
    massNormalizedPostRate f = massNormalizedPreRate f ∘ scatterTriple := rfl

theorem massNormalizedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPreRate f) := by
  rw [massNormalizedPreRate_eq_fun]
  exact normalizedKernel_measurable.mul ((weightedNormalizedPair_measurable hfm).comp measurable_fst)

theorem massNormalizedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPostRate f) :=
  (massNormalizedPreRate_measurable hfm).comp scatterTriple_measurable

omit [SFinite μ] in
theorem massNormalizedPreRate_integrable {f : X × Velocity → ℝ} (_hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPreRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (hi.comp_fst sphereArea).bdd_mul normalizedKernel_measurable.aestronglyMeasurable
    (ae_of_all _ normalizedKernel_bound)
  simpa only [massNormalizedPreRate_eq_fun] using h

theorem massNormalizedPostRate_integrable {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPostRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (massNormalizedPreRate_integrable hfm hi)

theorem weak_massNormalizedPreRate {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => weightedNormalizedPair (f n)) (weightedNormalizedPair g))
    (hfi : ∀ n, Integrable (weightedNormalizedPair (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massNormalizedPreRate (f n)) (massNormalizedPreRate g) := by
  have h := (h.prod_constant (ν := sphereArea) hfi).bounded_mul normalizedKernel_measurable
    1 normalizedKernel_bound
  simpa only [massNormalizedPreRate_eq_fun] using h

theorem weak_massNormalizedPostRate {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => weightedNormalizedPair (f n)) (weightedNormalizedPair g))
    (hfi : ∀ n, Integrable (weightedNormalizedPair (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massNormalizedPostRate (f n)) (massNormalizedPostRate g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (scatterTriple_measurePreserving μ)
    (fun n => massNormalizedPostRate_measurable (hfm n)) (massNormalizedPostRate_measurable hgm)
  have hs (z : (X × (Velocity × Velocity)) × Sphere) := scatterTriple_involutive z
  simpa only [massNormalizedPostRate_eq,Function.comp_def,hs] using weak_massNormalizedPreRate h hfi

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
