import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveComparisonBound
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveContributionsIntegrable
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedCharacteristicGain
import OAI.MathematicalPhysics.Boltzmann.Branching.InitialLinearComparison
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionComparisonError
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PrefixComparisonConvergence
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # The actual positive source bound on one common observation window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.clipped_positive_survival (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {U : ℝ} (hUT : U ≤ T) {t : ℝ} (ht : t ∈ Icc 0 U)
    {K R : ℝ} (hK : 0 ≤ K) (p : Phase) :
    survivingInitial U f₀ S.kineticProfile (t,p)+finitePositiveSource U N K R S.kineticProfile (t,p) ≤
      S.density (t,TorusFlight.flight t p) := by
  let F := physicalCharacteristicFrequency S.kineticProfile
  let a : ℝ → ℝ := fun s => Published.twoTimeSurvival (volume.restrict (Icc 0 t)) F ((t,p),s)
  let g : ℝ → ℝ := fun s => S.characteristicGain (s,p)
  let c : ℝ → ℝ := fun s => characteristicClippedFiniteGain N K R S.kineticProfile (s,p)
  have hFm : Measurable F := physicalCharacteristicFrequency_measurable S.kineticProfile_measurable
  have hFn : ∀ z, 0 ≤ F z := physicalCharacteristicFrequency_nonneg
    (fun q => S.nonnegative (q.1.1,(q.1.2,q.2)))
  have ha : ∀ s, 0 < a s ∧ a s ≤ 1 :=
    fun s => Published.twoTimeSurvival_bounds _ _ _
  have ham : Measurable a := (Published.twoTimeSurvival_measurable hFm).comp
    (measurable_const.prodMk measurable_id)
  have hgm : Measurable g := S.characteristicGain_measurable.comp
    (measurable_id.prodMk measurable_const)
  have hcm : Measurable c := (characteristicClippedFiniteGain_measurable N K R
    S.kineticProfile_measurable).comp (measurable_id.prodMk measurable_const)
  have hcg s : 0 ≤ c s ∧ c s ≤ g s := clippedFiniteGain_bounds hN hK S.kineticProfile_measurable
    (fun q => S.nonnegative (q.1.1,(q.1.2,q.2))) ((s,(TorusFlight.flight s p).1),p.2)
  have hgb s : 0 ≤ g s ∧ g s ≤ gainBound N := gain_bounds hN S.kineticProfile_measurable
    (fun q => S.nonnegative (q.1.1,(q.1.2,q.2))) ((s,(TorusFlight.flight s p).1),p.2)
  have hi (b : ℝ → ℝ) (hbm : Measurable b) (hb : ∀ s, 0 ≤ b s ∧ b s ≤ gainBound N) :
      IntervalIntegrable (fun s => a s*b s) volume 0 t := by
    apply (intervalIntegrable_const (c := gainBound N)).mono_fun' (ham.mul hbm).aestronglyMeasurable
    filter_upwards [] with s
    change ‖a s*b s‖ ≤ gainBound N
    rw [Real.norm_of_nonneg (mul_nonneg (ha s).1.le (hb s).1)]
    exact (mul_le_of_le_one_left (hb s).1 (ha s).2).trans (hb s).2
  have hci := hi c hcm (fun s => ⟨(hcg s).1,(hcg s).2.trans (hgb s).2⟩)
  have hgi := hi g hgm hgb
  have hle : (∫ s in 0..t, a s*c s) ≤ ∫ s in 0..t, a s*g s :=
    intervalIntegral.integral_mono_on ht.1 hci hgi
      (fun s _ => mul_le_mul_of_nonneg_left (hcg s).2 (ha s).1.le)
  have hseed : survivingInitial U f₀ S.kineticProfile (t,p) =
      physicalCharacteristicSurvival t S.kineticProfile (t,p)*f₀ p := by
    unfold survivingInitial physicalCharacteristicSurvival Published.timeSurvival
    rw [Published.timePrimitive_eq_interval ht,
      Published.timePrimitive_eq_interval (show t ∈ Icc 0 t from ⟨ht.1,le_rfl⟩)]
  have hsource : finitePositiveSource U N K R S.kineticProfile (t,p) =
      ∫ s in 0..t, a s*c s := by
    have he := Published.timePrimitive_eq_interval ht
      (fun z : ℝ × Phase => Published.twoTimeSurvival (volume.restrict (Icc 0 U)) F ((t,p),z.1)*
        characteristicClippedFiniteGain N K R S.kineticProfile z) p
    change finitePositiveSource U N K R S.kineticProfile (t,p) = _ at he
    rw [he]
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
    have heU := Published.twoTimeSurvival_eq_interval ht hst hFn p
      (S.frequency_path_integrable hN.le p U)
    have het := Published.twoTimeSurvival_eq_interval ⟨ht.1,le_rfl⟩ hst hFn p
      (S.frequency_path_integrable hN.le p t)
    dsimp only [a,c]
    rw [heU,het]
  rw [hseed,hsource]
  exact (add_le_add le_rfl hle).trans
    (S.positive_physical_survival hN ⟨ht.1,ht.2.trans hUT⟩ p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The nonnegative collision error is the actual characteristic comparison error -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness TransportPrimitive

theorem BoundedCutoffSolution.collisionComparisonError_along
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) (r : ℝ) (p : Phase) :
    TorusFlight.along (TorusFlight.regroup
      (collisionComparisonError N M S.kineticProfile P.kineticProfile)) (r,p) =
      |S.characteristicGain (r,p)-P.characteristicGain (r,p)|/
        (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))+
      S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))+
      P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))+
      |physicalCharacteristicFrequency S.kineticProfile (r,p)-
        physicalCharacteristicFrequency P.kineticProfile (r,p)| := by
  change |(S.characteristicGain (r,p)-P.characteristicGain (r,p))/
      (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))|+
    |S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))|+
    |P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))|+_ = _
  rw [abs_div,abs_of_pos (show 0 < 1+S.density (r,TorusFlight.flight r p)+
    P.density (r,TorusFlight.flight r p) by
      have := S.nonnegative (r,TorusFlight.flight r p)
      have := P.nonnegative (r,TorusFlight.flight r p)
      positivity)]
  rw [abs_of_nonneg (div_nonneg (S.characteristicLossDefect_nonneg hN (r,p)) (by
    have := S.nonnegative (r,TorusFlight.flight r p); positivity))]
  rw [abs_of_nonneg (div_nonneg (P.characteristicLossDefect_nonneg hM (r,p)) (by
    have := P.nonnegative (r,TorusFlight.flight r p); positivity))]
  rfl

theorem BoundedCutoffSolution.positive_comparison_error
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) {t : ℝ} (ht : t ∈ Icc 0 H) (ht' : t ≤ K) (p : Phase) :
    |positiveDifference (S.density (t,TorusFlight.flight t p))
      (P.density (t,TorusFlight.flight t p))| ≤ |positiveDifference (f₀ p) (g₀ p)|+
      ∫ r in 0..t, TorusFlight.along (TorusFlight.regroup
        (collisionComparisonError N M S.kineticProfile P.kineticProfile)) (r,p) := by
  have he := S.positive_comparison P hN hM ht ht' p
  simpa only [S.collisionComparisonError_along P hN hM] using he

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual characteristic-comparison error vanishes on bounded windows -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.comparison_error_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (collisionComparisonError ((I n:ℝ)+1) ((J n:ℝ)+1)
      (approximatingSolution f hfm (I n)).kineticProfile
      (approximatingSolution f hfm (J n)).kineticProfile) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let U n := (approximatingSolution f hfm (I n)).kineticProfile
  let V n := (approximatingSolution f hfm (J n)).kineticProfile
  have hU n : Measurable (U n) := (approximatingSolution f hfm (I n)).kineticProfile_measurable
  have hV n : Measurable (V n) := (approximatingSolution f hfm (J n)).kineticProfile_measurable
  have hi' : Tendsto (fun n => i n+Nat.ceil T) atTop atTop :=
    (tendsto_add_atTop_nat (Nat.ceil T)).comp hit
  have hj' : Tendsto (fun n => j n+Nat.ceil T) atTop atTop :=
    (tendsto_add_atTop_nat (Nat.ceil T)).comp hjt
  have ha := G.gain_discrepancy_L1 hf hi hT hR i j hit hjt
  have hb := (G.loss_residual_L1 hf hi hT hR).comp hi'
  have hc := (G.loss_residual_L1 hf hi hT hR).comp hj'
  have hd := strongL1_sub_of_common_limit
    ((G.frequency_strong hf hi hT hR).comp hi') ((G.frequency_strong hf hi hT hR).comp hj')
  exact strongL1_abs_sum_four
    (fun n => ((gain_measurable _ (hU n)).sub (gain_measurable _ (hV n))).div
      ((measurable_const.add (hU n)).add (hV n)))
    (fun n => ((lossDensity_measurable (hU n)).sub (loss_measurable _ (hU n))).div
      (measurable_const.add (hU n)))
    (fun n => ((lossDensity_measurable (hV n)).sub (loss_measurable _ (hV n))).div
      (measurable_const.add (hV n)))
    (fun n => (kineticFrequency_measurable (hU n)).sub (kineticFrequency_measurable (hV n)))
    ha hb hc hd

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual comparison error also vanishes in characteristic coordinates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.characteristic_error_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (TorusFlight.along (TorusFlight.regroup
      (collisionComparisonError ((I n:ℝ)+1) ((J n:ℝ)+1)
        (approximatingSolution f hfm (I n)).kineticProfile
        (approximatingSolution f hfm (J n)).kineticProfile))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  have h := G.comparison_error_L1 hf hi hT hR i j hit hjt
  apply h.congr'
  apply Eventually.of_forall
  intro n
  exact (eLpNorm_comp_measurePreserving
    (collisionComparisonError_measurable
      (approximatingSolution f hfm _).kineticProfile_measurable
      (approximatingSolution f hfm _).kineticProfile_measurable).aestronglyMeasurable
    (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))).symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The positive-difference metric of actual approximation subsequences vanishes -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.positive_difference_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase => positiveDifference
      ((approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2))
      ((approximatingSolution f hfm (J n)).density (z.1,TorusFlight.flight z.1 z.2))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let S n := approximatingSolution f hfm (I n)
  let P n := approximatingSolution f hfm (J n)
  let U n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let V n (z : ℝ × Phase) := (P n).density (z.1,TorusFlight.flight z.1 z.2)
  let d n (p : Phase) := |positiveDifference (initialApproximation ((I n:ℝ)+1) f p)
    (initialApproximation ((J n:ℝ)+1) f p)|
  let E n := TorusFlight.along (TorusFlight.regroup
    (collisionComparisonError ((I n:ℝ)+1) ((J n:ℝ)+1) (S n).kineticProfile (P n).kineticProfile))
  have hUm n : Measurable (U n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hVm n : Measurable (V n) := (P n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hEm n : Measurable (E n) := (collisionComparisonError_measurable
    (S n).kineticProfile_measurable (P n).kineticProfile_measurable).comp
      ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)
  have hdm n : Measurable (d n) :=
    (((initialApproximation_measurable _ hfm).sub (initialApproximation_measurable _ hfm)).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add
        (initialApproximation_measurable _ hfm))).abs
  have hi' : Tendsto I atTop atTop := G.weakLimit.increasing.tendsto_atTop.comp
    ((tendsto_add_atTop_nat (Nat.ceil T)).comp hit)
  have hj' : Tendsto J atTop atTop := G.weakLimit.increasing.tendsto_atTop.comp
    ((tendsto_add_atTop_nat (Nat.ceil T)).comp hjt)
  have hν : (volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hdt := initialApproximation_comparison_L1 hfm hf (integrable_of_entropyGauge hfm hf hi)
    hi' hj' hν
  have het := G.characteristic_error_L1 hf hi hT hR i j hit hjt
  apply prefixComparison_strongL1 hT
    (fun n => ((hUm n).sub (hVm n)).div ((measurable_const.add (hUm n)).add (hVm n)))
    hEm hdm (fun n z => collisionComparisonError_nonneg _ _ _ _ _) _ hdt het
  intro n t ht p
  have hI : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) (i n)).trans (G.weakLimit.increasing.id_le _)
  have hJ : Nat.ceil T ≤ J n :=
    (Nat.le_add_left (Nat.ceil T) (j n)).trans (G.weakLimit.increasing.id_le _)
  have hIT : T ≤ (I n:ℝ)+1 := by
    have hc : T ≤ (Nat.ceil T:ℝ) := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (I n:ℝ) := by exact_mod_cast hI
    linarith
  have hJT : T ≤ (J n:ℝ)+1 := by
    have hc : T ≤ (Nat.ceil T:ℝ) := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (J n:ℝ) := by exact_mod_cast hJ
    linarith
  exact (S n).positive_comparison_error (P n) (by positivity) (by positivity)
    ⟨ht.1,ht.2.trans hIT⟩ (ht.2.trans hJT) p

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Any two late actual density subsequences approach each other in local L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.density_pair_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z =>
      (approximatingSolution f hfm (I n)).kineticProfile z-
      (approximatingSolution f hfm (J n)).kineticProfile z) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let U n := (approximatingSolution f hfm (I n)).kineticProfile
  let V n := (approximatingSolution f hfm (J n)).kineticProfile
  have hUm n : Measurable (U n) := (approximatingSolution f hfm (I n)).kineticProfile_measurable
  have hVm n : Measurable (V n) := (approximatingSolution f hfm (J n)).kineticProfile_measurable
  have hUn n z : 0 ≤ U n z := (approximatingSolution f hfm (I n)).nonnegative _
  have hVn n z : 0 ≤ V n z := (approximatingSolution f hfm (J n)).nonnegative _
  have hbase := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  have hUi := uniformIntegrable_restrict (uniformIntegrable_comp hbase I)
    (univ ×ˢ Metric.closedBall (0:Velocity) R)
  have hVi := uniformIntegrable_restrict (uniformIntegrable_comp hbase J)
    (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hUi hVi
  apply positiveDifference_L1 hUm hVm hUn hVn hUi hVi
  have hd := G.positive_difference_L1 hf hi hT hR i j hit hjt
  apply hd.congr'
  apply Eventually.of_forall
  intro n
  have hm : Measurable (fun z => positiveDifference (U n z) (V n z)) :=
    ((hUm n).sub (hVm n)).div ((measurable_const.add (hUm n)).add (hVm n))
  exact eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
    (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual global collision subsequence converges strongly in local L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.density_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z =>
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile z-
      G.weakLimit.kineticProfile z) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let F n := (approximatingSolution f hfm (G.weakLimit.indices (n+Nat.ceil T))).kineticProfile
  have hUI := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  have hfi n : Integrable (F n) (μ.prod ν) := by
    have h := memLp_one_iff_integrable.mp (hUI.memLp (G.weakLimit.indices (n+Nat.ceil T)))
    exact h.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hw := ((G.weakLimit.kinetic_weak_on_window hT).comp
    (tendsto_add_atTop_nat (Nat.ceil T))).restrict
      (s := univ ×ˢ Metric.closedBall (0:Velocity) R)
      (MeasurableSet.univ.prod measurableSet_closedBall)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hw
  have hp : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => eLpNorm (fun z => F (i n) z-F (j n) z) 1 (μ.prod ν)) atTop (𝓝 0) :=
    fun i j hit hjt => G.density_pair_L1 hf hi hT hR i j hit hjt
  have hs := strongL1_of_pairwise_subsequences hfi hw hp
  exact (tendsto_add_atTop_iff_nat (Nat.ceil T)).mp hs

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
