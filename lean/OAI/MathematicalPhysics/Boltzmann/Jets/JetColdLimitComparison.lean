import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianColdPhysical
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily
import OAI.MathematicalPhysics.Boltzmann.Jets.JetEnvelopeTimeIntegral
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Gaussian control of the actual finite annular datum -/

noncomputable section

open MeasureTheory
open scoped BigOperators
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetFiniteGaussian

def indices (N : ℕ) : Finset JetDatum.Index := (Finset.range N).product Finset.univ

def coefficient (s₀ η K d₀ : ℝ) (j : ℕ) : ℝ :=
  Real.exp 8 * (K / jetScale s₀ η j) * ((d₀ * jetScale s₀ η j ^ 10) ^ 3)⁻¹ * JetThermalKernel.bound

def amplitude (s₀ η K d₀ : ℝ) (N : ℕ) : ℝ :=
  1 + ∑ i ∈ indices N, coefficient s₀ η K d₀ i.1

theorem truncated_eq_sum (s₀ η K α γ d₀ : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    JetTruncation.truncated s₀ η K α γ d₀ N p =
      ∑ i ∈ indices N, JetDatum.term s₀ η K α γ d₀ i p := by
  unfold JetTruncation.truncated
  rw [tsum_eq_sum (s := indices N)]
  · apply Finset.sum_congr rfl
    intro i hi
    have h : i.1 < N := Finset.mem_range.mp (Finset.mem_product.mp hi).1
    rw [ite_eq_left h]
  · intro i hi
    rw [ite_eq_right]
    intro h
    exact hi (by simp [indices, h])

theorem coefficient_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (j : ℕ) : 0 ≤ coefficient s₀ η K d₀ j := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (j+1)
  have hJ := JetThermalKernel.bound_pos
  unfold coefficient jetScale
  positivity

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N := by
  have h := Finset.sum_nonneg (s := indices N)
    (fun i _ => coefficient_nonneg hs₀ hK hd₀ η i.1)
  unfold amplitude
  linarith

theorem term_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (i : JetDatum.Index) (p : JetPrototype.Phase) :
    JetDatum.term s₀ η K α γ d₀ i p ≤ coefficient s₀ η K d₀ i.1 * JetGaussianMoments.kernel 2 p.2 := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1+1)
  have hd : 0 < d₀ * jetScale s₀ η i.1 ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hcoef := coefficient_nonneg hs₀ hK hd₀.le η i.1
  by_cases hz : JetDatum.term s₀ η K α γ d₀ i p = 0
  · rw [hz]
    exact mul_nonneg hcoef (Real.exp_pos _).le
  have hv := JetSupport.density_support_two hd
    (JetDatumMoments.thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hz
  have hW : 1 ≤ Real.exp 8 * JetGaussianMoments.kernel 2 p.2 := by
    unfold JetGaussianMoments.kernel
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [norm_nonneg p.2]
  let A := (K / jetScale s₀ η i.1) * ((d₀ * jetScale s₀ η i.1 ^ 10) ^ 3)⁻¹ * JetThermalKernel.bound
  have hA : 0 ≤ A := by
    have hJ := JetThermalKernel.bound_pos
    dsimp [A]
    positivity
  calc
    _ ≤ A := JetBarrier.initial_density_bound hK hs hd.le η α γ i.2 p
    _ ≤ A * (Real.exp 8 * JetGaussianMoments.kernel 2 p.2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hA
    _ = _ := by unfold coefficient; dsimp [A]; ring

theorem truncated_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ JetTruncation.truncated s₀ η K α γ d₀ N p ∧
      JetTruncation.truncated s₀ η K α γ d₀ N p ≤
        amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 := by
  rw [truncated_eq_sum]
  constructor
  · exact Finset.sum_nonneg (fun i _ => JetDatum.term_nonneg hs₀ hK hd₀.le η α γ i p)
  · calc
      _ ≤ ∑ i ∈ indices N, coefficient s₀ η K d₀ i.1 * JetGaussianMoments.kernel 2 p.2 :=
        Finset.sum_le_sum (fun i _ => term_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ i p)
      _ = (∑ i ∈ indices N, coefficient s₀ η K d₀ i.1) * JetGaussianMoments.kernel 2 p.2 := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold amplitude; linarith) (Real.exp_pos _).le

end BoltzmannNonuniqueness.JetFiniteGaussian

end

end

section

/-! # The jet envelope bounds the constant-damped positive iteration -/

noncomputable section

open MeasureTheory Set Filter
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetDampedSupersolution

theorem envelope_integrable {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    IntervalIntegrable (JetSupersolution.along η K α γ s d a p) volume 0 t := by
  have hm : Measurable (fun r => JetTimeRegularity.positiveU η K α γ s d a
      (r, JetBarrier.flight r p)) := by
    apply (JetTimeRegularity.measurable_positiveU hα hγ hs η K d a).comp
    unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hb : IntegrableOn (fun _ : ℝ => 2 * JetEnvelopeBound.amplitude K s d) (Ioc 0 t) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi : IntegrableOn (fun r => JetTimeRegularity.positiveU η K α γ s d a
      (r, JetBarrier.flight r p)) (Ioc 0 t) := by
    apply hb.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, JetTimeRegularity.positiveU_eq hr.1.le]
    rw [abs_of_nonneg (JetSupersolution.nonneg hK hs hd η α γ r a _)]
    exact (JetSupersolution.le_twice_barrier hK hs hd hα hγ hr.1
      (hr.2.trans htmax) hε η a _).trans
      (mul_le_mul_of_nonneg_left (JetEnvelopeBound.barrier_le hK hs hd hr.1
        (hr.2.trans htmax) η α γ a _) (by norm_num))
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
  apply hi.congr_fun _ measurableSet_Ioc
  intro r hr
  exact JetTimeRegularity.positiveU_eq hr.1.le η K α γ s d a _

theorem cutoff_integral_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b L : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    Real.exp (-L*t) * density η K α γ s d a p +
      (∫ r in 0..t, Real.exp (-L*(t-r)) *
        (CollisionCutoff.gain b (fun v => JetSupersolution.U η K α γ s d r a
          ((JetBarrier.flight r p).1, v)) p.2 +
          L * JetSupersolution.along η K α γ s d a p r)) ≤
      JetSupersolution.along η K α γ s d a p t := by
  obtain ⟨l, hl, hlim⟩ := JetBarrierTrace.supersolution_right_limit hK hα hγ hs hd η a p
  have hb := DampedSupersolution.integral_bound ht
    (fun r hr hrt => JetBarrierTrace.supersolution_ac hα hγ hs hr hrt η K d a p)
    hlim (envelope_integrable hK hα hγ hs hd ht htmax hε η a p)
    (JetEnvelopeTimeIntegral.gain_integrable hK hα hγ hs hd ht htmax hε η b a p)
    (L := L) (by
      filter_upwards [JetCutoffSupersolution.ae_supersolution hK hs hd hα hγ hε η b a p]
        with r hr hrt
      exact hr hrt.1 (hrt.2.trans htmax))
  exact (add_le_add (mul_le_mul_of_nonneg_left hl (Real.exp_nonneg _)) le_rfl).trans hb

end BoltzmannNonuniqueness.JetDampedSupersolution

end

end

section

/-! # Local positive cutoff solutions for the finite periodic jet seed -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetFiniteLocal

def liftToTorus (p : JetPrototype.Phase) : Phase :=
  (torusProjection (PlaneChart.join p.1.1 p.1.2), p.2)

def seed (s₀ η K α γ d₀ : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  JetPeriodicDatum.pullback (JetTruncation.truncated s₀ η K α γ d₀ N) (liftToTorus p)

theorem measurable_seed (s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    Measurable (seed s₀ η K α γ d₀ N) := by
  have hj : Measurable (fun x : JetPrototype.Space => PlaneChart.join x.1 x.2) :=
    VelocityWeight.split.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hlift : Measurable liftToTorus := by
    unfold liftToTorus torusProjection
    fun_prop
  have hc : Measurable (fun p : Phase =>
      JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative p)) := by
    exact JetPeriodicDatum.phaseMap_measurePreserving.measurable.comp
      TorusChart.phase_measurePreserving.measurable
  exact (JetTruncation.truncated_measurable s₀ η K α γ d₀ N).comp (hc.comp hlift)

theorem seed_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ seed s₀ η K α γ d₀ N p ∧ seed s₀ η K α γ d₀ N p ≤
      JetFiniteGaussian.amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 :=
  JetFiniteGaussian.truncated_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ N _

theorem exists_local {s₀ η K d₀ α b : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀) (hb : 0 ≤ b)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (N : ℕ) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ g : ℝ × JetPrototype.Phase → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ (2 * JetFiniteGaussian.amplitude s₀ η K d₀ N) *
          JetGaussianMoments.kernel 2 z.2.2) ∧
        (∀ t ∈ Icc 0 T, ∀ p, g (t, p) =
          Real.exp (-L * t) * seed s₀ η K α γ d₀ N (JetBarrier.flight (-t) p) +
          ∫ r in 0..t, Real.exp (-L * (t - r)) *
            (CollisionCutoff.gain b (fun v => g (r, ((JetBarrier.flight (r-t) p).1, v))) p.2 +
            (L - CollisionCutoff.frequency b (fun v => g (r, ((JetBarrier.flight (r-t) p).1, v))) p.2) *
              g (r, JetBarrier.flight (r-t) p))) :=
  GaussianLocal.exists_positive_mild (by norm_num) hb
    (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀.le η N)
    (measurable_seed s₀ η K α γ d₀ N)
    (seed_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ N)

end BoltzmannNonuniqueness.JetFiniteLocal

end

end

section

/-! # Domination of the constructed cold components by the geometric envelope -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.GaussianLocal

namespace BoltzmannNonuniqueness.JetColdComparison

theorem step_le {β b L T R K α γ s d t : ℝ}
    (hβ : 0 < β) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hc₀ : ∀ p, JetGaussianMoments.kernel β p.2 * c₀ p ≤ density η K α γ s d a p)
    (hcU : ∀ r ∈ Ioc 0 T, ∀ p, physical β c (r,p) ≤ JetSupersolution.U η K α γ s d r a p)
    (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical β (PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing β b L F c))
      (t, JetBarrier.flight t p) ≤ JetSupersolution.along η K α γ s d a p t := by
  have htmax := ht.2.trans hTmax
  have hgi := JetEnvelopeTimeIntegral.gain_integrable hK hα hγ hs hd ht.1 htmax hε η b a p
  have hui := JetDampedSupersolution.envelope_integrable hK hα hγ hs hd ht.1 htmax hε η a p
  have hright : IntervalIntegrable (fun r => Real.exp (-L*(t-r)) *
      (CollisionCutoff.gain b (fun v => JetSupersolution.U η K α γ s d r a
        ((JetBarrier.flight r p).1,v)) p.2 + L * JetSupersolution.along η K α γ s d a p r)) volume 0 t :=
    (hgi.add (hui.const_mul L)).continuousOn_mul (by fun_prop)
  have hci := physical_cold_integrable hβ hb hL hT hR hloss hFm hcm hF hc ⟨ht.1.le,ht.2⟩ p
  have hint : (∫ r in 0..t, Real.exp (-L*(t-r)) *
      (CollisionCutoff.gain b (fun v => physical β c (r,((JetBarrier.flight r p).1,v))) p.2 +
        (L - CollisionCutoff.frequency b
          (fun v => physical β F (r,((JetBarrier.flight r p).1,v))) p.2) *
          physical β c (r,JetBarrier.flight r p))) ≤
      ∫ r in 0..t, Real.exp (-L*(t-r)) *
        (CollisionCutoff.gain b (fun v => JetSupersolution.U η K α γ s d r a
          ((JetBarrier.flight r p).1,v)) p.2 + L * JetSupersolution.along η K α γ s d a p r) := by
    apply intervalIntegral.integral_mono_ae_restrict ht.1.le hci hright
    have hzero : ∀ᵐ r : ℝ, r ≠ 0 := by apply ae_iff.mpr; simp
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Icc] with r hr hrt
    have hrpos : 0 < r := lt_of_le_of_ne hrt.1 hr.symm
    have hrT : r ∈ Ioc 0 T := ⟨hrpos,hrt.2.trans ht.2⟩
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply add_le_add
    · apply JetPicardComparison.cutoff_mono hK hα hγ hs hd hrpos
        (hrt.2.trans htmax) hε η b a _
      · have hm : Measurable (fun v => JetGaussianMoments.kernel β v) := by
          unfold JetGaussianMoments.kernel; fun_prop
        exact hm.mul (hcm.comp (by fun_prop))
      · intro v
        exact mul_nonneg (Real.exp_nonneg _) (hc _).1
      · intro v
        exact hcU r hrT _
    · have hν : 0 ≤ CollisionCutoff.frequency b
          (fun v => physical β F (r,((JetBarrier.flight r p).1,v))) p.2 :=
        GaussianCutoff.frequency_nonneg (f := state F) (fun q => (hF (q.1.1,(q.1.2,q.2))).1)
          β b ((r,(JetBarrier.flight r p).1),p.2)
      have hcn : 0 ≤ physical β c (r,JetBarrier.flight r p) :=
        mul_nonneg (Real.exp_nonneg _) (hc _).1
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ hν) hcn).trans
        (mul_le_mul_of_nonneg_left (hcU r hrT _) hL)
  rw [physical_value_along ⟨ht.1.le,ht.2⟩]
  exact (add_le_add (mul_le_mul_of_nonneg_left (hc₀ p) (Real.exp_nonneg _)) hint).trans
    (JetDampedSupersolution.cutoff_integral_bound hK hα hγ hs hd ht.1 htmax hε η b L a p)

end BoltzmannNonuniqueness.JetColdComparison

end

end

section

/-! # Actual cold limits inherit the pointwise jet bound -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.GaussianLocal

namespace BoltzmannNonuniqueness.JetColdComparison

theorem picard_le {β b L T R K α γ s d : ℝ}
    (hβ : 0 < β) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (hseed : ∀ p, JetGaussianMoments.kernel β p.2 * c₀ p ≤ density η K α γ s d a p) :
    ∀ n t, t ∈ Ioc 0 T → ∀ p,
      physical β (coldPicard β b L T F c₀ n) (t,p) ≤ JetSupersolution.U η K α γ s d t a p := by
  have hp := coldPicard_properties hβ hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq
  intro n
  induction n with
  | zero =>
    intro t ht p
    simpa only [physical, coldPicard, mul_zero] using JetSupersolution.nonneg hK hs hd η α γ t a p
  | succ n ih =>
    intro t ht p
    have hc (z) : 0 ≤ coldPicard β b L T F c₀ n z ∧ coldPicard β b L T F c₀ n z ≤ R :=
      ⟨((hp n).2 z).1, ((hp n).2 z).2.trans (hF z).2⟩
    have hh := step_le hβ hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a
      hFm (hp n).1 hF hc hseed ih ht (JetBarrier.flight (-t) p)
    simpa only [coldPicard, JetSupersolution.along, JetFreeTransport.flight_neg] using hh

theorem limit_le {β b L T R K α γ s d : ℝ}
    (hβ : 0 < β) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (hseed : ∀ p, JetGaussianMoments.kernel β p.2 * c₀ p ≤ density η K α γ s d a p)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical β (coldLimit β b L T F c₀) (t,p) ≤ JetSupersolution.U η K α γ s d t a p := by
  have hlim := (coldLimit_solution hβ hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq).2.2.2 (t,p)
  apply le_of_tendsto (hlim.const_mul (JetGaussianMoments.kernel β p.2))
  exact Eventually.of_forall (fun n =>
    picard_le hβ hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a hFm hc₀m hF hc₀ hF₀ hFeq hseed n t ht p)

end BoltzmannNonuniqueness.JetColdComparison

end

end

end OAI
