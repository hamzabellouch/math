import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import OAI.MathematicalPhysics.Boltzmann.Jets.JetColdLimitComparison
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Monotone and dominated limits for the weighted representative gain -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem integrable_cutoff {q R : ℝ} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (b : ℝ) (p : X × Velocity) (hp : p.2 ∈ good q) :
    Integrable (CollisionCutoff.integrand b (fun v => density q f (p.1,v)) p.2)
      ((volume : Measure Velocity).prod sphereArea) := by
  have hm : Measurable (fun v => density q f (p.1,v)) := (measurable_density hfm q).comp (measurable_const.prodMk measurable_id)
  have hn : ∀ v, 0 ≤ density q f (p.1,v) := fun v => (density_bounds (q := q) hf (p.1,v)).1
  exact CollisionCutoff.integrable_gain b hm hn p.2
    (GainOrder.integrable_of_le hm hn (fun v => (density_bounds (q := q) hf (p.1,v)).2) p.2
      (GainOrder.integrable_const_mul R p.2 (integrable_H_gain hp)))

theorem gain_mono {q R : ℝ} {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hfg : ∀ p, f p ≤ g p) (hg : ∀ p, g p ≤ R)
    (b : ℝ) (p : X × Velocity) : gain q b f p ≤ gain q b g p := by
  have hfn p : 0 ≤ f p ∧ f p ≤ R := ⟨hf p,(hfg p).trans (hg p)⟩
  have hgn p : 0 ≤ g p ∧ g p ≤ R := ⟨(hf p).trans (hfg p),hg p⟩
  unfold gain
  split_ifs with hp
  · apply div_le_div_of_nonneg_right _ (H_nonneg q p.2)
    apply integral_mono (integrable_cutoff hfm hfn b p hp) (integrable_cutoff hgm hgn b p hp)
    intro w
    unfold CollisionCutoff.integrand density
    have hL := mul_le_mul_of_nonneg_left (hfg (p.1,scatterLeft p.2 w.1 w.2)) (H_nonneg q (scatterLeft p.2 w.1 w.2))
    have hR := mul_le_mul_of_nonneg_left (hfg (p.1,scatterRight p.2 w.1 w.2)) (H_nonneg q (scatterRight p.2 w.1 w.2))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL (CollisionCutoff.kernel_nonneg _ _ _ _)) hR
      (mul_nonneg (H_nonneg _ _) (hf _))
      (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (mul_nonneg (H_nonneg _ _) (hgn _).1))
  · exact le_rfl

theorem gain_tendsto {q R : ℝ} (_hR : 0 ≤ R) {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p ∧ f n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p))) (b : ℝ) (p : X × Velocity) :
    Tendsto (fun n => gain q b (f n) p) atTop (𝓝 (gain q b g p)) := by
  unfold gain
  split_ifs with hp
  · apply Tendsto.div_const
    apply tendsto_integral_of_dominated_convergence
      (fun w => R^2 * GainOrder.integrand (H q) p.2 w)
    · intro n
      exact (integrable_cutoff (hfm n) (hf n) b p hp).aestronglyMeasurable
    · exact (integrable_H_gain hp).const_mul _
    · intro n
      apply ae_of_all
      intro w
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · apply (CollisionCutoff.integrand_le b (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1) p.2 w).trans
        have h := GainOrder.integrand_mono (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1)
          (fun v => (density_bounds (q := q) (hf n) (p.1,v)).2) p.2 w
        unfold GainOrder.integrand density at h ⊢
        nlinarith only [h]
      · exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
          (density_bounds (q := q) (hf n) _).1) (density_bounds (q := q) (hf n) _).1
    · apply ae_of_all
      intro w
      exact ((tendsto_const_nhds.mul (tendsto_const_nhds.mul (hlim _))).mul
        (tendsto_const_nhds.mul (hlim _)))
  · exact tendsto_const_nhds

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive local iteration in the manuscript's singular weighted norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

def forcing (q b L : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.source q b L (GaussianLocal.state f) ((z.1,z.2.1),z.2.2)

theorem measurable_forcing {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (forcing q b L f) :=
  (HotRepresentative.measurable_source (GaussianLocal.measurable_state hf) q b L).comp (by fun_prop)

theorem exists_normalized {q b L T A R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    (hball : A + T*(HotApplication.realBound q * R^2 + L*R) ≤ R)
    (hsmall : T*(2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ R) ∧
      ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z := by
  let S := HotApplication.realBound q * R^2 + L*R
  let K := 2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L
  have hS : 0 ≤ S := by
    have := (HotApplication.realBound_pos q).le
    dsimp [S]; positivity
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]; positivity
  obtain ⟨f,hf⟩ := PositiveIntegral.exists_fixed_point hT hL hA hR hS hK hball hsmall
    GaussianLocal.measurable_flight hf₀m hf₀
    (fun f => forcing q b L (fun z => f.val z))
    (fun f => measurable_forcing (BoundedMeasurable.measurable _ f.val) q b L)
    (fun f z => HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2))
    (fun f g z => HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ g.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2)))
      (fun p => g.property (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le _ f.val g.val (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2))
  exact ⟨fun z => f.val z, BoundedMeasurable.measurable _ f.val, f.property, hf⟩

theorem exists_normalized_time {q b A : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z ∧ f z ≤ 2*A) ∧
      ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z := by
  let R := 2*A
  let L := R * CutoffLipschitz.frequencyConstant q b
  let S := HotApplication.realBound q * R^2 + L*R
  let K := 2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 ≤ L := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hS : 0 ≤ S := by have := (HotApplication.realBound_pos q).le; dsimp [S]; positivity
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]; positivity
  let T := min (A/(S+1)) ((1/2)/(K+1))
  have hT : 0 < T := lt_min (div_pos hA (by positivity)) (div_pos (by norm_num) (by positivity))
  have hTS : T*(S+1) ≤ A := (le_div_iff₀ (by positivity : 0 < S+1)).mp (min_le_left _ _)
  have hTK : T*(K+1) ≤ 1/2 := (le_div_iff₀ (by positivity : 0 < K+1)).mp (min_le_right _ _)
  have hball : A+T*S ≤ R := by dsimp [R]; nlinarith
  have hsmall : T*K < 1 := by nlinarith
  exact ⟨T,L,hT,hL,exists_normalized hq hb hL hT.le hA.le hR le_rfl hball hsmall hf₀m hf₀⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniform frequency control by a cold core and the cap weight -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def weightFrequencyConstant (q V : ℝ) : ℝ :=
  2*Real.pi*(V*(∫ w, H q w)+(∫ w, ‖w‖*H q w))

theorem weightFrequencyConstant_nonneg (q : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ weightFrequencyConstant q V := by
  unfold weightFrequencyConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg hV (integral_nonneg (H_nonneg q)))
    (integral_nonneg (fun w => mul_nonneg (norm_nonneg w) (H_nonneg q w))))

theorem H_frequency_integrable {q : ℝ} (hq : q < 2) (v : Velocity) :
    Integrable (fun w => ‖v-w‖*H q w) :=
  integrable_frequency_integrand (fun p => H q p.2) 0 v (integrable_H hq)
    (by simpa only [pow_one] using integrable_moment_H hq 1)

theorem H_frequency_le {q V : ℝ} (hq : q < 2) {v : Velocity} (hv : ‖v‖ ≤ V) :
    frequency (fun p => H q p.2) 0 v ≤ weightFrequencyConstant q V := by
  have h := abs_frequency_le (fun p => H q p.2) 0 v (integrable_H hq)
    (by simpa only [pow_one] using integrable_moment_H hq 1)
  simp only [abs_of_nonneg (H_nonneg q _)] at h
  apply (le_abs_self _).trans (h.trans ?_)
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hv (integral_nonneg (H_nonneg q))) le_rfl)
    (by positivity)

theorem integral_rate_sum (f g : Velocity → ℝ) (v : Velocity) (A : ℝ)
    (hf : Integrable (fun w => ‖v-w‖*f w))
    (hg : Integrable (fun w => ‖v-w‖*g w)) :
    2*Real.pi*(∫ w, ‖v-w‖*(2*f w+A*g w)) =
      2*frequency (fun p => f p.2) 0 v+A*frequency (fun p => g p.2) 0 v := by
  have he : (fun w => ‖v-w‖*(2*f w+A*g w)) =
      (fun w => 2*(‖v-w‖*f w)+A*(‖v-w‖*g w)) := by
    funext w
    ring
  rw [he,integral_add (hf.const_mul 2) (hg.const_mul A),integral_const_mul,integral_const_mul]
  unfold frequency
  ring

namespace JetSupersolution

theorem core_add_weight_frequency_bound_ae {K s d α γ t q A V : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (hq : q < 2) (hA : 0 ≤ A) (η b : ℝ) (a : Bool) (x : JetPrototype.Space)
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ᵐ w, f w ≤ U η K α γ s d t a (x,w)+A*H q w)
    {v : Velocity} (hv : ‖v-JetBarrier.centerVelocity α γ s t a x‖ ≤ d)
    (hvV : ‖v‖ ≤ V) :
    CollisionCutoff.frequency b f v ≤ 4*JetBarrierCollision.frequencyConstant*K*d/s+
      A*weightFrequencyConstant q V := by
  let B : Velocity → ℝ := fun w => JetBarrier.barrier η K α γ s d t a (x,w)
  have hc := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
  have hβ : 0 < 2-t := by linarith
  have hBi : Integrable (fun w => ‖v-w‖*B w) := by
    apply integrable_frequency_integrand (fun p => B p.2) 0 v
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.integrable hβ hd
          (JetBarrierCollision.massScale η K α γ s d t a x)
          (JetBarrier.centerVelocity α γ s t a x)
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.first_moment_integrable hc hβ hd
          (JetBarrier.centerVelocity α γ s t a x)
  have hHi := H_frequency_integrable hq v
  have hsum : Integrable (fun w => ‖v-w‖*(2*B w+A*H q w)) := by
    convert (hBi.const_mul 2).add (hHi.const_mul A) using 1
    funext w
    simp only [Pi.add_apply]
    ring
  have hfg : ∀ᵐ w, f w ≤ 2*B w+A*H q w := by
    filter_upwards [hfU] with w hw
    exact hw.trans (add_le_add
      (le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x,w)) le_rfl)
  have hf := CollisionCutoff.frequency_le_majorant_ae b hfm hfn hfg v hsum
  rw [integral_rate_sum B (H q) v A hBi hHi] at hf
  have hbar := JetBarrierCollision.frequency_bound hK hs hd ht htmax η α γ a x 0 v
  change frequency (fun p => B p.2) 0 v ≤ _ at hbar
  have hcoef : 0 ≤ JetBarrierCollision.frequencyConstant*(K/s) :=
    mul_nonneg JetBarrierCollision.frequencyConstant_nonneg (div_nonneg hK hs.le)
  have hcore : 2*frequency (fun p => B p.2) 0 v ≤
      4*JetBarrierCollision.frequencyConstant*K*d/s := by
    have hb' := hbar.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hv) hcoef)
    calc
      _ ≤ 2*(JetBarrierCollision.frequencyConstant*(K/s)*(d+d)) := by linarith only [hb']
      _ = _ := by ring
  exact hf.trans (add_le_add hcore (mul_le_mul_of_nonneg_left (H_frequency_le hq hvV) hA))

theorem core_add_weight_frequency_bound {K s d α γ t q A V : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (hq : q < 2) (hA : 0 ≤ A) (η b : ℝ) (a : Bool) (x : JetPrototype.Space)
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ w, f w ≤ U η K α γ s d t a (x,w)+A*H q w)
    {v : Velocity} (hv : ‖v-JetBarrier.centerVelocity α γ s t a x‖ ≤ d)
    (hvV : ‖v‖ ≤ V) :
    CollisionCutoff.frequency b f v ≤ 4*JetBarrierCollision.frequencyConstant*K*d/s+
      A*weightFrequencyConstant q V :=
  core_add_weight_frequency_bound_ae hK hs hd hα hγ ht htmax hε hq hA η b a x
    hfm hfn (Filter.Eventually.of_forall hfU) hv hvV

end JetSupersolution
end BoltzmannNonuniqueness

end

end

section

/-! # The actual finite periodic datum in the singular weighted space -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedFiniteSeed

def amplitude (s₀ η K d₀ : ℝ) (N : ℕ) : ℝ :=
  JetFiniteGaussian.amplitude s₀ η K d₀ N * tiltConstant

def seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  JetFiniteLocal.seed s₀ η K α γ d₀ N p / H q p.2

theorem measurable_seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) :
    Measurable (seed s₀ η K α γ d₀ q N) :=
  (JetFiniteLocal.measurable_seed s₀ η K α γ d₀ N).div
    ((ChartKernel.measurable_H q).comp measurable_snd)

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N :=
  mul_pos (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀ η N) tiltConstant_pos

theorem seed_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ)^10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ seed s₀ η K α γ d₀ q N p ∧ seed s₀ η K α γ d₀ q N p ≤ amplitude s₀ η K d₀ N := by
  have h := JetFiniteLocal.seed_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ N p
  refine ⟨div_nonneg h.1 (H_nonneg q p.2), (div_le_iff₀ (H_pos q p.2)).mpr ?_⟩
  calc
    _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 := h.2
    _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * (tiltConstant * H q p.2) :=
      mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q p.2)
        (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀.le η N).le
    _ = _ := by unfold amplitude; ring

/-- A prescribed bounded nonnegative hot seed may be added to the actual
finite periodic cold datum before the positive local construction. -/
theorem exists_local {s₀ η K d₀ α q b B : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ)^10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (hq : q < 2) (hb : 0 ≤ b) (hB : 0 ≤ B) (γ : ℝ) (N : ℕ)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀)
    (hh₀ : ∀ p, 0 ≤ h₀ p ∧ h₀ p ≤ B) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ F : ℝ × JetPrototype.Phase → ℝ, Measurable F ∧
        (∀ z, 0 ≤ F z ∧ F z ≤ 2*(amplitude s₀ η K d₀ N+B)) ∧
        ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight
          (fun p => seed s₀ η K α γ d₀ q N p + h₀ p) (WeightedLocal.forcing q b L F) z := by
  apply WeightedLocal.exists_normalized_time hq hb
    (add_pos_of_pos_of_nonneg (amplitude_pos hs₀ hK hd₀.le η N) hB)
    ((measurable_seed s₀ η K α γ d₀ q N).add hh₀m)
  intro p
  have h := seed_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ q N p
  exact ⟨add_nonneg h.1 (hh₀ p).1, add_le_add h.2 (hh₀ p).2⟩

end BoltzmannNonuniqueness.WeightedFiniteSeed

end

end

section

/-! # Actual positive H-weighted local cutoff solutions

Only the published Carleman input is used to remove the fixed negligible
set of output velocities. Local existence itself is constructed in Lean.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedLocal

def physical (q : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  H q z.2.2 * f z

theorem physical_source {q b L : ℝ} (f : ℝ × JetPrototype.Phase → ℝ)
    {z : ℝ × JetPrototype.Phase} (hz : z.2.2 ∈ HotRepresentative.good q) :
    H q z.2.2 * forcing q b L f z =
      CollisionCutoff.gain b (fun v => physical q f (z.1,(z.2.1,v))) z.2.2 +
      (L - CollisionCutoff.frequency b (fun v => physical q f (z.1,(z.2.1,v))) z.2.2) *
        physical q f z := by
  unfold forcing HotRepresentative.source
  have he := HotRepresentative.physical_gain_eq (b := b) (GaussianLocal.state f)
    (p := ((z.1,z.2.1),z.2.2)) hz
  dsimp only at he
  rw [mul_add, he]
  simp only [GaussianLocal.state, physical, HotRepresentative.frequency,
    HotRepresentative.density, KineticCollisionNullSets.frequency, KineticCollisionNullSets.gain]
  ring

theorem physical_mild {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {f : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase) (hp : p.2 ∈ HotRepresentative.good q) :
    physical q f (t,p) =
      Real.exp (-L*t) * (H q p.2 * f₀ (JetBarrier.flight (-t) p)) +
      ∫ r in 0..t, Real.exp (-L*(t-r)) *
        (CollisionCutoff.gain b
          (fun v => physical q f (r,((JetBarrier.flight (r-t) p).1,v))) p.2 +
          (L - CollisionCutoff.frequency b
            (fun v => physical q f (r,((JetBarrier.flight (r-t) p).1,v))) p.2) *
            physical q f (r,JetBarrier.flight (r-t) p)) := by
  change H q p.2 * f (t,p) = _
  rw [hf (t,p), PositiveIntegral.value, GaussianLocal.time_eq ht, mul_add,
    ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro r _
    have he := physical_source (b := b) (L := L) f (z := (r,JetBarrier.flight (r-t) p)) hp
    change H q p.2 * _ = _ at he
    dsimp only at he ⊢
    rw [mul_left_comm, he]
    rfl

theorem exists_positive_mild (hcarleman : Published.GPV2009CarlemanInput)
    {q b A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {g₀ : JetPrototype.Phase → ℝ} (hg₀m : Measurable g₀)
    (hg₀ : ∀ p, 0 ≤ g₀ p ∧ g₀ p ≤ A * H q p.2) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ g : ℝ × JetPrototype.Phase → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ (2*A) * H q z.2.2) ∧
        (∀ᵐ v : Velocity, ∀ t ∈ Icc 0 T, ∀ x : JetPrototype.Space,
          g (t,(x,v)) = Real.exp (-L*t) * g₀ (JetBarrier.flight (-t) (x,v)) +
            ∫ r in 0..t, Real.exp (-L*(t-r)) *
              (CollisionCutoff.gain b
                (fun w => g (r,((JetBarrier.flight (r-t) (x,v)).1,w))) v +
                (L - CollisionCutoff.frequency b
                  (fun w => g (r,((JetBarrier.flight (r-t) (x,v)).1,w))) v) *
                  g (r,JetBarrier.flight (r-t) (x,v)))) := by
  let f₀ (p : JetPrototype.Phase) := g₀ p / H q p.2
  have hfm : Measurable f₀ := hg₀m.div ((ChartKernel.measurable_H q).comp measurable_snd)
  have hf₀ (p) : 0 ≤ f₀ p ∧ f₀ p ≤ A :=
    ⟨div_nonneg (hg₀ p).1 (H_nonneg q p.2), (div_le_iff₀ (H_pos q p.2)).mpr (hg₀ p).2⟩
  obtain ⟨T,L,hT,hL,f,hfm,hfb,hfeq⟩ := exists_normalized_time hq₂ hb hA hfm hf₀
  refine ⟨T,L,hT,hL,physical q f,?_,?_,?_⟩
  · exact ((ChartKernel.measurable_H q).comp measurable_snd.snd).mul hfm
  · intro z
    exact ⟨mul_nonneg (H_nonneg _ _) (hfb z).1,
      (mul_le_mul_of_nonneg_left (hfb z).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)⟩
  · filter_upwards [HotRepresentative.ae_good hcarleman hq₁ hq₂] with v hv t ht x
    have hm := physical_mild hfeq ht (x,v) hv
    have hi : H q v * f₀ (JetBarrier.flight (-t) (x,v)) = g₀ (JetBarrier.flight (-t) (x,v)) := by
      dsimp [f₀, JetBarrier.flight]
      field_simp [(H_pos q v).ne']
    rw [hi] at hm
    exact hm

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Exact collision expansion for bounded weighted densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem density_velocity_integrable {q R : ℝ} (hq : q < 2)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (x : X) :
    Integrable (fun v => density q f (x,v)) := by
  apply ((integrable_H hq).const_mul R).mono'
    (((measurable_density hfm q).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun v => by
    change ‖density q f (x,v)‖ ≤ R*H q v
    rw [Real.norm_of_nonneg (density_bounds hf (x,v)).1]
    exact (density_bounds hf (x,v)).2)

theorem physical_gain_add {q R b : ℝ} {c h : X × Velocity → ℝ}
    (hcm : Measurable c) (hhm : Measurable h)
    (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (hh : ∀ p, 0 ≤ h p ∧ h p ≤ R)
    (p : X × Velocity) (hp : p.2 ∈ good q) :
    KineticCollisionNullSets.gain b (density q (c+h)) p =
      KineticCollisionNullSets.gain b (density q c) p+
        2*mixedGainDensity b (density q c) (density q h) p+
        KineticCollisionNullSets.gain b (density q h) p := by
  have hsum : ∀ z, 0 ≤ (c+h) z ∧ (c+h) z ≤ R+R := fun z =>
    ⟨add_nonneg (hc z).1 (hh z).1,add_le_add (hc z).2 (hh z).2⟩
  have hi : Integrable (fun w : Velocity × Sphere =>
      mixedPostRate b (density q (c+h)) (density q (c+h)) (collisionGrouping.symm (p,w)))
      ((volume : Measure Velocity).prod sphereArea) := by
    apply (integrable_cutoff (hcm.add hhm) hsum b p hp).congr
    exact ae_of_all _ (fun w => by dsimp only; rw [mixedPostRate_formula]; rfl)
  have hcn z := (density_bounds (q := q) hc z).1
  have hhn z := (density_bounds (q := q) hh z).1
  have hcle z : density q c z ≤ density q (c+h) z := by
    dsimp only [density,Pi.add_apply]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hh z).1) (H_nonneg q z.2)
  have hhle z : density q h z ≤ density q (c+h) z := by
    dsimp only [density,Pi.add_apply]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hc z).1) (H_nonneg q z.2)
  have hplus : density q c+density q h = density q (c+h) := by
    funext z
    dsimp only [density,Pi.add_apply]
    ring
  have hcc := mixedPostRate_fiber_integrable (measurable_density hcm q) (measurable_density hcm q)
    hcn hcn hcle hcle p hi
  have hch := mixedPostRate_fiber_integrable (measurable_density hcm q) (measurable_density hhm q)
    hcn hhn hcle hhle p hi
  have hhc := mixedPostRate_fiber_integrable (measurable_density hhm q) (measurable_density hcm q)
    hhn hcn hhle hcle p hi
  have hhh := mixedPostRate_fiber_integrable (measurable_density hhm q) (measurable_density hhm q)
    hhn hhn hhle hhle p hi
  simpa only [hplus] using cutoffGain_add b (density q c) (density q h) p hcc hch hhc hhh

theorem physical_frequency_add {q R b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {c h : X × Velocity → ℝ} (hcm : Measurable c) (hhm : Measurable h)
    (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (hh : ∀ p, 0 ≤ h p ∧ h p ≤ R)
    (p : X × Velocity) :
    KineticCollisionNullSets.frequency b (density q (c+h)) p =
      KineticCollisionNullSets.frequency b (density q c) p+
        KineticCollisionNullSets.frequency b (density q h) p := by
  have hplus : density q c+density q h = density q (c+h) := by
    funext z
    dsimp only [density,Pi.add_apply]
    ring
  simpa only [hplus] using cutoffFrequency_add b (density q c) (density q h) p
    (CollisionCutoff.integrable_frequency hb (density_velocity_integrable hq hcm hc p.1) p.2)
    (CollisionCutoff.integrable_frequency hb (density_velocity_integrable hq hhm hh p.1) p.2)

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Quantitative dependence in the singular weighted local space -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_difference {q b L T R I : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ g₀ : JetPrototype.Phase → ℝ} (hseed : ∀ p, |f₀ p-g₀ p| ≤ I)
    {f g : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L g) z)
    (z : ℝ × JetPrototype.Phase) :
    |f z-g z| ≤ I / (1-T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)) := by
  let P := ℝ × JetPrototype.Phase
  let f' := BoundedMeasurable.ofBounded P f hfm R
    (fun z => by rw [abs_of_nonneg (hf z).1]; exact (hf z).2)
  let g' := BoundedMeasurable.ofBounded P g hgm R
    (fun z => by rw [abs_of_nonneg (hg z).1]; exact (hg z).2)
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]; positivity
  have hsource (u : ℝ × JetPrototype.Phase → ℝ) (hum : Measurable u)
      (hu : ∀ z, 0 ≤ u z ∧ u z ≤ R) (z) : |forcing q b L u z| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hum)
      (fun p => hu (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ forcing q b L u z ∧ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hdiff (z) : |forcing q b L f z-forcing q b L g z| ≤ K*dist f' g' :=
    HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state hfm) (GaussianLocal.measurable_state hgm)
      (fun p => hf (p.1.1,(p.1.2,p.2))) (fun p => hg (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le P f' g' (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2)
  have hd : dist f' g' ≤ I+(T*K)*dist f' g' := by
    apply BoundedMeasurable.dist_le P (by positivity)
    intro z
    change |f z-g z| ≤ _
    rw [hfeq z,hgeq z]
    simpa only [mul_assoc] using PositiveIntegral.value_difference_initial hT hL
      (mul_nonneg hK dist_nonneg) hI GaussianLocal.measurable_flight hseed
      (measurable_forcing hfm q b L) (measurable_forcing hgm q b L)
      (hsource f hfm hf) (hsource g hgm hg) hdiff z
  have hden : 0 < 1-T*K := by dsimp [K]; linarith
  have hdist : dist f' g' ≤ I/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hd])
  exact (BoundedMeasurable.dist_apply_le P f' g' z).trans hdist

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite-color domination for the H-weighted collision gain -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_gain_le {q R : ℝ} (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (b : ℝ) (p : X × Velocity) :
    ∑ i ∈ s, gain q b (c i) p ≤ gain q b F p := by
  classical
  by_cases hp : p.2 ∈ good q
  · have hci (i) (hi : i ∈ s) := integrable_cutoff (hcm i hi) (hc i hi) b p hp
    have hFi := integrable_cutoff hFm hF b p hp
    have hsumD (v : Velocity) : ∑ i ∈ s, density q (c i) (p.1,v) ≤ density q F (p.1,v) := by
      unfold density
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hSum _) (VelocityWeight.H_nonneg _ _)
    have hcn (i) (hi : i ∈ s) (v : Velocity) : 0 ≤ density q (c i) (p.1,v) :=
      (density_bounds (q := q) (hc i hi) (p.1,v)).1
    have hFn (v : Velocity) : 0 ≤ density q F (p.1,v) := (density_bounds (q := q) hF (p.1,v)).1
    simp only [gain,ite_eq_left hp]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (VelocityWeight.H_nonneg q p.2)
    change (∑ i ∈ s, ∫ w, CollisionCutoff.integrand b
      (fun v => density q (c i) (p.1,v)) p.2 w ∂((volume : Measure Velocity).prod sphereArea)) ≤ _
    rw [← integral_finsetSum _ hci]
    apply integral_mono (integrable_finsetSum s hci) hFi
    intro w
    have hdiag : (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
        density q (c i) (p.1,scatterRight p.2 w.1 w.2)) ≤
        density q F (p.1,scatterLeft p.2 w.1 w.2) * density q F (p.1,scatterRight p.2 w.1 w.2) := by
      calc
        _ ≤ ∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j hj => hcn j hj _) hi) (hcn i hi _)
        _ = (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2)) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul (hsumD _) (hsumD _) (Finset.sum_nonneg (fun i hi => hcn i hi _)) (hFn _)
    unfold CollisionCutoff.integrand
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hdiag (CollisionCutoff.kernel_nonneg _ _ _ _)
  · simp only [gain,ite_eq_right hp,Finset.sum_const_zero,le_refl]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Common-loss cold source in the singular weighted space -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

def coldSource (q b L : ℝ) (F c : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain q b c p + (L-frequency q b F p)*c p

theorem measurable_coldSource {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (q b L : ℝ) : Measurable (coldSource q b L F c) :=
  (measurable_gain hcm q b).add ((measurable_const.sub (measurable_frequency hFm q b)).mul hcm)

theorem coldSource_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (p : X × Velocity) :
    0 ≤ coldSource q b L F c p ∧ coldSource q b L F c p ≤ HotApplication.realBound q*R^2+L*R := by
  have hν := frequency_nonneg (fun p => (hF p).1) q b p
  have hνB := frequency_bound hq hb hFm hF p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hc p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hc p).1)
  · have hg := gain_bound (q := q) hR hcm hc b p
    have hl : (L-frequency q b F p)*c p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hc p).1).trans
        (mul_le_mul_of_nonneg_left (hc p).2 hLp)
    unfold coldSource
    nlinarith only [hg,hl]

theorem coldSource_mono {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c d : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c) (hdm : Measurable d)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hcn : ∀ p, 0 ≤ c p)
    (hcd : ∀ p, c p ≤ d p) (hdR : ∀ p, d p ≤ R) (p : X × Velocity) :
    coldSource q b L F c p ≤ coldSource q b L F d p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  exact add_le_add (gain_mono hcm hdm hcn hcd hdR b p)
    (mul_le_mul_of_nonneg_left (hcd p) (sub_nonneg.mpr hν))

theorem coldSource_tendsto {q R : ℝ} (hR : 0 ≤ R) (b L : ℝ) (F : X × Velocity → ℝ)
    {c : ℕ → X × Velocity → ℝ} {d : X × Velocity → ℝ}
    (hcm : ∀ n, Measurable (c n)) (hc : ∀ n p, 0 ≤ c n p ∧ c n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => c n p) atTop (𝓝 (d p))) (p : X × Velocity) :
    Tendsto (fun n => coldSource q b L F (c n) p) atTop (𝓝 (coldSource q b L F d p)) :=
  (gain_tendsto hR hcm hc hlim b p).add (tendsto_const_nhds.mul (hlim p))

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive cold iteration beneath the H-weighted total solution -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

def coldForcing (q b L : ℝ) (F c : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state c) ((z.1,z.2.1),z.2.2)

def coldPicard (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) : ℕ → ℝ × JetPrototype.Phase → ℝ
  | 0 => fun _ => 0
  | n+1 => PositiveIntegral.value T L JetBarrier.flight c₀
      (coldForcing q b L F (coldPicard q b L T F c₀ n))

theorem measurable_coldForcing {F c : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c) (q b L : ℝ) : Measurable (coldForcing q b L F c) :=
  (HotRepresentative.measurable_coldSource (GaussianLocal.measurable_state hFm)
    (GaussianLocal.measurable_state hcm) q b L).comp (by fun_prop)

theorem coldPicard_properties {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) z)
    (n : ℕ) : Measurable (coldPicard q b L T F c₀ n) ∧
      ∀ z, 0 ≤ coldPicard q b L T F c₀ n z ∧ coldPicard q b L T F c₀ n z ≤ F z := by
  let S := HotApplication.realBound q*R^2+L*R
  have hS : 0 ≤ S := add_nonneg (mul_nonneg (HotApplication.realBound_pos q).le (sq_nonneg _))
    (mul_nonneg hL hR)
  induction n with
  | zero => exact ⟨measurable_const,fun z => ⟨le_rfl,(hF z).1⟩⟩
  | succ n ih =>
    have hc (z) : 0 ≤ coldPicard q b L T F c₀ n z ∧ coldPicard q b L T F c₀ n z ≤ R :=
      ⟨(ih.2 z).1,(ih.2 z).2.trans (hF z).2⟩
    have hcm := measurable_coldForcing hFm ih.1 q b L
    have hcs (z) : 0 ≤ coldForcing q b L F (coldPicard q b L T F c₀ n) z ∧
        coldForcing q b L F (coldPicard q b L T F c₀ n) z ≤ S :=
      HotRepresentative.coldSource_bounds hq hb hR hloss
        (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state ih.1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) _
    have hfs (z) : 0 ≤ forcing q b L F z ∧ forcing q b L F z ≤ S :=
      HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
        (fun p => hF (p.1.1,(p.1.2,p.2))) _
    refine ⟨PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hc₀m hcm,fun z => ⟨?_,?_⟩⟩
    · exact (PositiveIntegral.value_bounds hT hL hR hS JetBarrier.flight
        (fun p => ⟨(hc₀ p).1,(hc₀ p).2.trans (hF₀ p)⟩) hcs z).1
    · rw [hFeq z]
      apply PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight (fun p => (hc₀ p).2)
        hcm (measurable_forcing hFm q b L)
        (fun z => by rw [abs_of_nonneg (hcs z).1]; exact (hcs z).2)
        (fun z => by rw [abs_of_nonneg (hfs z).1]; exact (hfs z).2)
      intro p
      exact HotRepresentative.coldSource_mono hq hb hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state ih.1) (GaussianLocal.measurable_state hFm)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => (ih.2 (p.1.1,(p.1.2,p.2))).1)
        (fun p => (ih.2 (p.1.1,(p.1.2,p.2))).2) (fun p => (hF (p.1.1,(p.1.2,p.2))).2) ((p.1,p.2.1),p.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Physical comparison form of the weighted cold iteration -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*}

theorem physical_gain_le {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (q b : ℝ) (p : X × Velocity) :
    H q p.2 * gain q b f p ≤ KineticCollisionNullSets.gain b (density q f) p := by
  classical
  by_cases hp : p.2 ∈ good q
  · exact (physical_gain_eq f hp).le
  · rw [gain,ite_eq_right hp,mul_zero]
    apply integral_nonneg
    intro w
    exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
      (mul_nonneg (H_nonneg _ _) (hf _))) (mul_nonneg (H_nonneg _ _) (hf _))

end BoltzmannNonuniqueness.HotRepresentative

namespace BoltzmannNonuniqueness.WeightedLocal

theorem physical_coldForcing_le {F c : ℝ × JetPrototype.Phase → ℝ}
    (hc : ∀ z, 0 ≤ c z) (q b L : ℝ) (z : ℝ × JetPrototype.Phase) :
    H q z.2.2 * coldForcing q b L F c z ≤
      CollisionCutoff.gain b (fun v => physical q c (z.1,(z.2.1,v))) z.2.2 +
      (L - CollisionCutoff.frequency b (fun v => physical q F (z.1,(z.2.1,v))) z.2.2) * physical q c z := by
  have he := HotRepresentative.physical_gain_le
    (f := GaussianLocal.state c) (fun p => hc (p.1.1,(p.1.2,p.2))) q b ((z.1,z.2.1),z.2.2)
  unfold coldForcing HotRepresentative.coldSource
  rw [mul_add]
  apply add_le_add he
  simp only [HotRepresentative.frequency,KineticCollisionNullSets.frequency,HotRepresentative.density,
    GaussianLocal.state,physical]
  exact (mul_left_comm _ _ _).le

theorem physical_value_along {q b L T t : ℝ} (ht : t ∈ Icc 0 T)
    (F c : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) :
    physical q (PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c))
      (t,JetBarrier.flight t p) = Real.exp (-L*t)*(H q p.2*c₀ p) +
      ∫ r in 0..t, Real.exp (-L*(t-r))*(H q p.2*coldForcing q b L F c (r,JetBarrier.flight r p)) := by
  unfold physical PositiveIntegral.value
  rw [GaussianLocal.time_eq ht]
  simp only [JetFreeTransport.flight_add,neg_add_cancel,JetFreeTransport.flight_zero,sub_add_cancel]
  change H q p.2 * _ = _
  rw [mul_add,← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    ring

theorem physical_cold_integrable {q b L T R t : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase) :
    IntervalIntegrable (fun r => Real.exp (-L*(t-r)) *
      (H q p.2*coldForcing q b L F c (r,JetBarrier.flight r p))) volume 0 t := by
  have hs (z) : |coldForcing q b L F c z| ≤ HotApplication.realBound q*R^2+L*R := by
    have hh := HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ coldForcing q b L F c z ∧ _ at hh
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hi := (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight
    (measurable_coldForcing hFm hcm q b L) hs (t,JetBarrier.flight t p)).const_mul (H q p.2)
  rw [GaussianLocal.time_eq ht] at hi
  simp only [JetFreeTransport.flight_add,sub_add_cancel] at hi
  have hi' : IntervalIntegrable (fun r => H q p.2 *
      (Real.exp (-L*(t-r))*coldForcing q b L F c (r,JetBarrier.flight r p))) volume 0 t := hi
  apply hi'.congr_ae
  filter_upwards [] with r
  ring

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Monotone construction of cold components in the singular weighted space -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

def coldLimit (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  ⨆ n, coldPicard q b L T F c₀ n z

theorem coldLimit_solution {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) z) :
    Measurable (coldLimit q b L T F c₀) ∧
      (∀ z, 0 ≤ coldLimit q b L T F c₀ z ∧ coldLimit q b L T F c₀ z ≤ F z) ∧
      (∀ z, coldLimit q b L T F c₀ z = PositiveIntegral.value T L JetBarrier.flight c₀
        (coldForcing q b L F (coldLimit q b L T F c₀)) z) ∧
      ∀ z, Tendsto (fun n => coldPicard q b L T F c₀ n z) atTop (𝓝 (coldLimit q b L T F c₀ z)) := by
  let u := coldPicard q b L T F c₀
  have hu := coldPicard_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq
  let S := HotApplication.realBound q*R^2+L*R
  have hbound (n) (z) : 0 ≤ u n z ∧ u n z ≤ R :=
    ⟨((hu n).2 z).1,((hu n).2 z).2.trans (hF z).2⟩
  have hsource (n) (z) : 0 ≤ coldForcing q b L F (u n) z ∧
      coldForcing q b L F (u n) z ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state (hu n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hbound n (p.1.1,(p.1.2,p.2))) _
  have hstep : ∀ n z, u n z ≤ u (n+1) z := by
    intro n
    induction n with
    | zero => intro z; exact ((hu 1).2 z).1
    | succ n ih =>
      intro z
      apply PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight (fun _ => le_rfl)
        (measurable_coldForcing hFm (hu n).1 q b L)
        (measurable_coldForcing hFm (hu (n+1)).1 q b L)
        (fun z => by rw [abs_of_nonneg (hsource n z).1]; exact (hsource n z).2)
        (fun z => by rw [abs_of_nonneg (hsource (n+1) z).1]; exact (hsource (n+1) z).2)
      intro p
      exact HotRepresentative.coldSource_mono hq hb hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state (hu n).1) (GaussianLocal.measurable_state (hu (n+1)).1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => (hbound n (p.1.1,(p.1.2,p.2))).1)
        (fun p => ih (p.1.1,(p.1.2,p.2))) (fun p => (hbound (n+1) (p.1.1,(p.1.2,p.2))).2) ((p.1,p.2.1),p.2.2)
  have hmono (z) : Monotone (fun n => u n z) := monotone_nat_of_le_succ (fun n => hstep n z)
  have hbdd (z) : BddAbove (Set.range (fun n => u n z)) :=
    ⟨F z,by rintro _ ⟨n,rfl⟩; exact ((hu n).2 z).2⟩
  let c := coldLimit q b L T F c₀
  have hlim (z) : Tendsto (fun n => u n z) atTop (𝓝 (c z)) := tendsto_atTop_ciSup (hmono z) (hbdd z)
  have hcm : Measurable c := measurable_of_tendsto_metrizable (fun n => (hu n).1) (tendsto_pi_nhds.mpr hlim)
  have hcb (z) : 0 ≤ c z ∧ c z ≤ F z :=
    ⟨(le_ciSup (hbdd z) 0 : u 0 z ≤ c z),ciSup_le (fun n => ((hu n).2 z).2)⟩
  refine ⟨hcm,hcb,?_,hlim⟩
  intro z
  have hsourcelim (p) : Tendsto (fun n => coldForcing q b L F (u n) p) atTop
      (𝓝 (coldForcing q b L F c p)) :=
    HotRepresentative.coldSource_tendsto hR b L (GaussianLocal.state F)
      (fun n => GaussianLocal.measurable_state (hu n).1)
      (fun n p => hbound n (p.1.1,(p.1.2,p.2)))
      (fun p => hlim (p.1.1,(p.1.2,p.2))) _
  have hv := PositiveIntegral.value_tendsto hT hL GaussianLocal.measurable_flight c₀
    (fun n => measurable_coldForcing hFm (hu n).1 q b L)
    (fun n p => by rw [abs_of_nonneg (hsource n p).1]; exact (hsource n p).2) hsourcelim z
  have hs := (hlim z).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hs hv

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Survival of an actual positive cold component along its free characteristics -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedLocal

theorem cold_path_eq_damped {q b L T t : ℝ} (ht : t ∈ Icc 0 T)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hc : ∀ s ∈ Icc 0 T, ∀ p, c (s,p) =
      PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (s,p))
    (p : JetPrototype.Phase) :
    c (t,JetBarrier.flight t p) = TransportPrimitive.damped L (c₀ p)
      (fun r => coldForcing q b L F c (r,JetBarrier.flight r p)) t := by
  rw [hc t ht,TransportPrimitive.damped_eq]
  unfold PositiveIntegral.value
  rw [GaussianLocal.time_eq ht]
  simp only [JetFreeTransport.flight_add,neg_add_cancel,JetFreeTransport.flight_zero,sub_add_cancel]

theorem cold_survival {q b L T R t : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hceq : ∀ s ∈ Icc 0 T, ∀ p, c (s,p) =
      PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (s,p))
    (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase)
    {E k : ℝ → ℝ} (hE : ContDiff ℝ 1 E) (hE' : ∀ r, HasDerivAt E (k r) r)
    (hν : ∀ᵐ r, r ∈ Icc 0 t → CollisionCutoff.frequency b
      (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2 ≤ k r) :
    Real.exp (E 0-E t)*c₀ p ≤ c (t,JetBarrier.flight t p) := by
  let g : ℝ → ℝ := fun r => coldForcing q b L F c (r,JetBarrier.flight r p)
  let S : ℝ := HotApplication.realBound q*R^2+L*R
  have hgb (r : ℝ) : 0 ≤ g r ∧ g r ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) _
  have hgm : Measurable g := (measurable_coldForcing hFm hcm q b L).comp
    (measurable_id.prodMk (GaussianLocal.measurable_flight.comp
      (measurable_id.prodMk measurable_const)))
  have hgi : IntervalIntegrable g volume 0 t := by
    apply (intervalIntegrable_const (c := S)).mono_fun' hgm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun r => by
      change ‖g r‖ ≤ S
      rw [Real.norm_eq_abs,abs_of_nonneg (hgb r).1]
      exact (hgb r).2)
  have hpath (r : ℝ) (hr : r ∈ Icc 0 t) :
      c (r,JetBarrier.flight r p) = TransportPrimitive.damped L (c₀ p) g r :=
    cold_path_eq_damped ⟨hr.1,hr.2.trans ht.2⟩ hceq p
  have hbound : ∀ᵐ r, r ∈ Icc 0 t →
      (L-k r)*TransportPrimitive.damped L (c₀ p) g r ≤ g r := by
    filter_upwards [hν] with r hνr hr
    rw [← hpath r hr]
    have hgain := HotRepresentative.gain_nonneg
      (fun p => (hc (p.1.1,(p.1.2,p.2))).1) q b
      ((r,(JetBarrier.flight r p).1),p.2)
    have hrate := hνr hr
    have hn := (hc (r,JetBarrier.flight r p)).1
    change 0 ≤ HotRepresentative.gain q b (GaussianLocal.state c)
      ((r,(JetBarrier.flight r p).1),p.2) at hgain
    change (L-k r)*c (r,JetBarrier.flight r p) ≤
      HotRepresentative.gain q b (GaussianLocal.state c) ((r,(JetBarrier.flight r p).1),p.2)+
        (L-CollisionCutoff.frequency b
          (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2)*
          c (r,JetBarrier.flight r p)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hrate L) hn).trans
      (le_add_of_nonneg_left hgain)
  rw [cold_path_eq_damped ht hceq p]
  exact TransportPrimitive.damped_survival ht.1 hgi hE hE' hbound

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Weighted collision representatives respect equality almost everywhere -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem density_congr (μ : Measure X) {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q : ℝ) : density q f =ᵐ[μ.prod volume] density q g := by
  filter_upwards [hfg] with p hp
  unfold density
  rw [hp]

theorem gain_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : gain q b f =ᵐ[μ.prod volume] gain q b g := by
  have hh := KineticCollisionNullSets.gain_congr μ (density_congr μ hfg q) b
  filter_upwards [hh] with p hp
  unfold gain
  split_ifs <;> simp only [hp]

theorem frequency_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : frequency q b f =ᵐ[μ.prod volume] frequency q b g :=
  KineticCollisionNullSets.frequency_congr μ (density_congr μ hfg q) b

theorem source_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b L : ℝ) : source q b L f =ᵐ[μ.prod volume] source q b L g := by
  filter_upwards [gain_congr μ hfg q b,frequency_congr μ hfg q b,hfg] with p hg hν hp
  unfold source
  rw [hg,hν,hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The collision source only depends on its current time slice -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

def timeSlice (F : ℝ × JetPrototype.Phase → ℝ) (s : ℝ) : ℝ × JetPrototype.Phase → ℝ :=
  fun u => F (s,u.2)

theorem forcing_timeSlice (q b L s t : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) :
    forcing q b L (timeSlice F s) (t,p) = forcing q b L F (s,p) := rfl

theorem forcing_eq_of_slice {F G : ℝ × JetPrototype.Phase → ℝ} {s t : ℝ}
    (h : ∀ p, F (s,p) = G (t,p)) (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L F (s,p) = forcing q b L G (t,p) := by
  have he : timeSlice F s = timeSlice G t := funext (fun u => h u.2)
  exact congrArg (fun H => forcing q b L H (0,p)) he

def paste (s : ℝ) (F G : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  if u.1 ≤ s then F u else G (u.1-s,u.2)

theorem forcing_paste_left {s t : ℝ} (ht : t ≤ s) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L F (t,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_left ht]) q b L p

theorem forcing_paste_right {s t : ℝ} (ht : s < t) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L G (t-s,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_right (not_le.mpr ht)]) q b L p

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Spatial covariance of the constructed weighted cold solutions -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

def shift (y : Space) (p : JetPrototype.Phase) : JetPrototype.Phase := (p.1-y,p.2)

def pull (y : Space) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  f (z.1,shift y z.2)

theorem measurable_shift (y : Space) : Measurable (shift y) := by
  unfold shift
  fun_prop

theorem measurable_pull {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (y : Space) :
    Measurable (pull y f) := hf.comp (measurable_fst.prodMk ((measurable_shift y).comp measurable_snd))

theorem shift_flight (y : Space) (t : ℝ) (p : JetPrototype.Phase) :
    shift y (JetBarrier.flight t p) = JetBarrier.flight t (shift y p) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [shift,JetBarrier.flight] <;> abel
  · rfl

theorem forcing_pull (q b L : ℝ) (y : Space) (f : ℝ × JetPrototype.Phase → ℝ) :
    WeightedLocal.forcing q b L (pull y f) = pull y (WeightedLocal.forcing q b L f) := rfl

theorem coldForcing_pull (q b L : ℝ) (y : Space) (F c : ℝ × JetPrototype.Phase → ℝ) :
    WeightedLocal.coldForcing q b L (pull y F) (pull y c) =
      pull y (WeightedLocal.coldForcing q b L F c) := rfl

theorem value_pull (T L : ℝ) (y : Space) (f₀ : JetPrototype.Phase → ℝ)
    (g : ℝ × JetPrototype.Phase → ℝ) :
    PositiveIntegral.value T L JetBarrier.flight (fun p => f₀ (shift y p)) (pull y g) =
      pull y (PositiveIntegral.value T L JetBarrier.flight f₀ g) := by
  funext z
  simp only [PositiveIntegral.value,pull,shift_flight]

theorem fixed_point_pull {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (z : ℝ × JetPrototype.Phase) :
    pull y F z = PositiveIntegral.value T L JetBarrier.flight
      (fun p => f₀ (shift y p)) (WeightedLocal.forcing q b L (pull y F)) z := by
  rw [forcing_pull,value_pull]
  exact hF _

theorem coldPicard_pull (q b L T : ℝ) (y : Space) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) (n : ℕ) :
    WeightedLocal.coldPicard q b L T (pull y F) (fun p => c₀ (shift y p)) n =
      pull y (WeightedLocal.coldPicard q b L T F c₀ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [WeightedLocal.coldPicard,ih,coldForcing_pull,value_pull]

theorem coldLimit_pull (q b L T : ℝ) (y : Space) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) :
    WeightedLocal.coldLimit q b L T (pull y F) (fun p => c₀ (shift y p)) =
      pull y (WeightedLocal.coldLimit q b L T F c₀) := by
  funext z
  simp only [WeightedLocal.coldLimit,coldPicard_pull,pull]

end BoltzmannNonuniqueness.WeightedTranslation

end

end

section

/-! # Geometric jet control for the constructed H-weighted cold iteration -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedJetComparison

theorem step_le {q b L T R K α γ s d t : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hc₀ : ∀ p, VelocityWeight.H q p.2*c₀ p ≤ density η K α γ s d a p)
    (hcU : ∀ r ∈ Ioc 0 T, ∀ p, physical q c (r,p) ≤ JetSupersolution.U η K α γ s d r a p)
    (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c))
      (t,JetBarrier.flight t p) ≤ JetSupersolution.along η K α γ s d a p t := by
  have htmax := ht.2.trans hTmax
  have hgi := JetEnvelopeTimeIntegral.gain_integrable hK hα hγ hs hd ht.1 htmax hε η b a p
  have hui := JetDampedSupersolution.envelope_integrable hK hα hγ hs hd ht.1 htmax hε η a p
  have hright : IntervalIntegrable (fun r => Real.exp (-L*(t-r)) *
      (CollisionCutoff.gain b (fun v => JetSupersolution.U η K α γ s d r a
        ((JetBarrier.flight r p).1,v)) p.2 + L*JetSupersolution.along η K α γ s d a p r)) volume 0 t :=
    (hgi.add (hui.const_mul L)).continuousOn_mul (by fun_prop)
  have hci := physical_cold_integrable hq hb hL hT hR hloss hFm hcm hF hc ⟨ht.1.le,ht.2⟩ p
  have hint : (∫ r in 0..t, Real.exp (-L*(t-r)) *
      (VelocityWeight.H q p.2*coldForcing q b L F c (r,JetBarrier.flight r p))) ≤
      ∫ r in 0..t, Real.exp (-L*(t-r)) *
        (CollisionCutoff.gain b (fun v => JetSupersolution.U η K α γ s d r a
          ((JetBarrier.flight r p).1,v)) p.2 + L*JetSupersolution.along η K α γ s d a p r) := by
    apply intervalIntegral.integral_mono_ae_restrict ht.1.le hci hright
    have hzero : ∀ᵐ r : ℝ, r ≠ 0 := by apply ae_iff.mpr; simp
    filter_upwards [ae_restrict_of_ae hzero,ae_restrict_mem measurableSet_Icc] with r hr hrt
    have hrpos : 0 < r := lt_of_le_of_ne hrt.1 hr.symm
    have hrT : r ∈ Ioc 0 T := ⟨hrpos,hrt.2.trans ht.2⟩
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply (physical_coldForcing_le (fun z => (hc z).1) q b L (r,JetBarrier.flight r p)).trans
    apply add_le_add
    · apply JetPicardComparison.cutoff_mono hK hα hγ hs hd hrpos
        (hrt.2.trans htmax) hε η b a _
      · exact ((ChartKernel.measurable_H q).mul (hcm.comp (by fun_prop)))
      · intro v
        exact mul_nonneg (VelocityWeight.H_nonneg _ _) (hc _).1
      · intro v
        exact hcU r hrT _
    · have hν : 0 ≤ CollisionCutoff.frequency b
          (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2 :=
        HotRepresentative.frequency_nonneg (f := GaussianLocal.state F)
          (fun x => (hF (x.1.1,(x.1.2,x.2))).1) q b ((r,(JetBarrier.flight r p).1),p.2)
      have hcn : 0 ≤ physical q c (r,JetBarrier.flight r p) :=
        mul_nonneg (VelocityWeight.H_nonneg _ _) (hc _).1
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ hν) hcn).trans
        (mul_le_mul_of_nonneg_left (hcU r hrT _) hL)
  rw [physical_value_along ⟨ht.1.le,ht.2⟩]
  exact (add_le_add (mul_le_mul_of_nonneg_left (hc₀ p) (Real.exp_nonneg _)) hint).trans
    (JetDampedSupersolution.cutoff_integral_bound hK hα hγ hs hd ht.1 htmax hε η b L a p)

end BoltzmannNonuniqueness.WeightedJetComparison

end

end

end OAI
