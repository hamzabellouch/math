import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationScales
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdTime
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotGain
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.Monotone

namespace OAI

section

/-! # Bounded positive periodic mild states and finite-step continuation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

structure PeriodicMildState (q b L T R : ℝ) (f₀ : JetPrototype.Phase → ℝ) where
  value : ℝ × JetPrototype.Phase → ℝ
  measurable_value : Measurable value
  value_bounds : ∀ u, 0 ≤ value u ∧ value u ≤ R
  mild : MildAE q b L T f₀ value
  clamped : ∀ u, value (PositiveIntegral.time T u.1,u.2) = value u
  periodic : ∀ n, pull (JetCopyDatum.displacement n) value = value

namespace PeriodicMildState

theorem all_mild {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hT : 0 ≤ T) :
    ∀ t, (fun p => F.value (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F.value) (t,p)) :=
  mild_all_of_time_clamp hT L F.clamped F.mild

def restrict {q b L T R S : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hS : 0 ≤ S) (hST : S ≤ T) :
    PeriodicMildState q b L S R f₀ where
  value := clampTime S F.value
  measurable_value := measurable_clampTime F.measurable_value S
  value_bounds u := F.value_bounds _
  mild := F.mild.restrict_clamp hS hST
  clamped := clampTime_idempotent hS F.value
  periodic n := by
    funext u
    exact congrFun (F.periodic n) (PositiveIntegral.time S u.1,u.2)

def initial {q b L A : ℝ} (hA : 0 ≤ A) {f₀ : JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (hper : ∀ n p, f₀ (shift (JetCopyDatum.displacement n) p) = f₀ p) :
    PeriodicMildState q b L 0 (2*A) f₀ where
  value u := f₀ u.2
  measurable_value := hf₀m.comp measurable_snd
  value_bounds u := ⟨(hf₀ u.2).1,(hf₀ u.2).2.trans (by linarith)⟩
  mild := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    apply ae_of_all
    intro p
    simp [PositiveIntegral.value,PositiveIntegral.time,JetBarrier.flight]
  clamped _ := rfl
  periodic n := funext (fun u => hper n u.2)

theorem exists_extension {q b A T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b (damping q b A) T (2*A) f₀)
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) (T+lifespan q b A) (2*A) f₀) := by
  obtain ⟨G,hGm,hG,hGeq,hGper,_⟩ := exists_continuation_step hq hb hA hT
    F.measurable_value F.value_bounds hFA F.mild F.periodic
  have htotal : 0 ≤ T+lifespan q b A := add_nonneg hT (lifespan_pos (q := q) hb hA).le
  refine ⟨⟨clampTime (T+lifespan q b A) G,measurable_clampTime hGm _,
    fun u => hG _,?_,clampTime_idempotent htotal G,?_⟩⟩
  · exact fun t _ => mildAE_all_times htotal (fun r _ => hGeq r) t
  · intro n
    funext u
    exact congrFun (hGper n) (PositiveIntegral.time (T+lifespan q b A) u.1,u.2)

end PeriodicMildState

theorem exists_to_time_of_apriori {q b A τ : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hτ : 0 ≤ τ) {f₀ : JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (hper : ∀ n p, f₀ (shift (JetCopyDatum.displacement n) p) = f₀ p)
    (hapriori : ∀ T, 0 ≤ T → T ≤ τ →
      ∀ F : PeriodicMildState q b (damping q b A) T (2*A) f₀,
        ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) τ (2*A) f₀) := by
  let δ := lifespan q b A
  have hδ : 0 < δ := lifespan_pos hb hA
  have hex : ∀ n : ℕ, Nonempty (PeriodicMildState q b (damping q b A)
      (min ((n:ℝ)*δ) τ) (2*A) f₀) := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.cast_zero,zero_mul,min_eq_left hτ] using
        (show Nonempty (PeriodicMildState q b (damping q b A) 0 (2*A) f₀) from
          ⟨PeriodicMildState.initial hA.le hf₀m hf₀ hper⟩)
    | succ n ih =>
      have hn : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      by_cases hstop : τ ≤ (n:ℝ)*δ
      · have hnext : τ ≤ ((n+1:ℕ):ℝ)*δ := by
          rw [Nat.cast_add,Nat.cast_one]
          nlinarith
        rw [min_eq_right hnext,min_eq_right hstop] at *
        exact ih
      · obtain ⟨F⟩ := ih
        have hS : 0 ≤ min ((n:ℝ)*δ) τ := le_min hn hτ
        obtain ⟨G⟩ := F.exists_extension hq hb hA hS
          (hapriori _ hS (min_le_right _ _) F)
        have hnew : 0 ≤ min (((n+1:ℕ):ℝ)*δ) τ :=
          le_min (mul_nonneg (Nat.cast_nonneg _) hδ.le) hτ
        have hle : min (((n+1:ℕ):ℝ)*δ) τ ≤ min ((n:ℝ)*δ) τ+δ := by
          rw [min_eq_left (le_of_not_ge hstop)]
          calc
            _ ≤ (((n+1:ℕ):ℝ)*δ) := min_le_left _ _
            _ = (n:ℝ)*δ+δ := by rw [Nat.cast_add,Nat.cast_one]; ring
        exact ⟨G.restrict hnew hle⟩
  obtain ⟨n,hn⟩ := exists_nat_ge (τ/δ)
  have hreach : τ ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  simpa only [min_eq_right hreach] using hex n

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # A bounded sequence of periodic mild states closes at its limiting seed -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem exists_seed_limit {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {f₀ : ℕ → JetPrototype.Phase → ℝ} {g₀ : JetPrototype.Phase → ℝ}
    (F : ∀ n, PeriodicMildState q b L T R (f₀ n))
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hseed : ∀ n, ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ a n) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : PeriodicMildState q b L T R g₀,
      ∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |(F n).value (t,p)-G.value (t,p)| ≤ C*a n := by
  obtain ⟨C,hC,hstable⟩ := bounded_interval_stability hq hb hL hT hR hloss
  let D := C+1
  have hD : 0 < D := by dsimp [D]; linarith
  have hpair (n m) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-f₀ m p| ≤ a n+a m := by
    filter_upwards [hseed n,hseed m] with p hn hm
    exact (abs_sub_le (f₀ n p) (g₀ p) (f₀ m p)).trans
      (add_le_add hn (by simpa only [abs_sub_comm] using hm))
  have hclose (n m t) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |(F n).value (t,p)-(F m).value (t,p)| ≤ D*a n+D*a m := by
    have hs := hstable (add_nonneg (ha n) (ha m)) (F n).measurable_value (F m).measurable_value
      (F n).value_bounds (F m).value_bounds (F n).mild (F m).mild (hpair n m)
      (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)
    filter_upwards [hs] with p hp
    rw [(F n).clamped (t,p),(F m).clamped (t,p)] at hp
    exact hp.trans (by dsimp [D]; nlinarith [ha n,ha m])
  have hseedD (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ D*a n :=
    (hseed n).mono (fun p hp => hp.trans (by dsimp [D]; nlinarith [ha n]))
  have haD : Tendsto (fun n => D*a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ha0
  obtain ⟨G,hGm,hGb,hGe,hFG,hInv⟩ := exists_mild_limit hq hb hL hT hR hloss
    (fun n => (F n).measurable_value) (fun n => (F n).value_bounds)
    (fun n => mul_nonneg hD.le (ha n)) haD hclose hseedD (fun n => (F n).all_mild hT)
  have hclamp : ∀ u, G (PositiveIntegral.time T u.1,u.2) = G u :=
    hInv (fun u => (PositiveIntegral.time T u.1,u.2)) (fun n => (F n).clamped)
  have hper (n) : WeightedTranslation.pull (JetCopyDatum.displacement n) G = G := by
    funext u
    exact hInv (fun u => (u.1,WeightedTranslation.shift (JetCopyDatum.displacement n) u.2))
      (fun k u => congrFun ((F k).periodic n) u) u
  exact ⟨D,hD,⟨G,hGm,hGb,fun t _ => hGe t,hclamp,hper⟩,hFG⟩

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Persistence of bounded periodic solutions under perturbing the initial seed -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem nearby_seed_exists {q b A B T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hBA : B < A)
    (F : PeriodicMildState q b (damping q b A) T (2*A) f₀)
    (hsmall : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {g₀ : JetPrototype.Phase → ℝ}, Measurable g₀ →
      (∀ p, 0 ≤ g₀ p ∧ g₀ p ≤ A) →
      (∀ n p, g₀ (shift (JetCopyDatum.displacement n) p) = g₀ p) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |g₀ p-f₀ p| ≤ ε) →
      Nonempty (PeriodicMildState q b (damping q b A) T (2*A) g₀) := by
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  obtain ⟨C,hC,hstable⟩ := bounded_interval_stability_uniform hq hb hL hT hR hloss
  let ε := (A-B)/(C+1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hBA) (by linarith)
  have heq : ε*(C+1) = A-B := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
  have hbound : B+C*ε ≤ A := by nlinarith [hε.le]
  refine ⟨ε,hε,?_⟩
  intro g₀ hgm hgb hgp hseed
  apply exists_to_time_of_apriori hq hb hA hT hgm hgb hgp
  intro S hS hST G
  let F' := F.restrict hS hST
  have hd := hstable hS hST hε.le G.measurable_value F'.measurable_value
    G.value_bounds F'.value_bounds G.mild F'.mild hseed S ⟨hS,le_rfl⟩
  filter_upwards [hd,hsmall S ⟨hS,hST⟩] with p hp hFp
  have he : F'.value (S,p) = F.value (S,p) := by
    change F.value (PositiveIntegral.time S S,p) = _
    rw [GaussianLocal.time_eq (show S ∈ Icc 0 S from ⟨hS,le_rfl⟩)]
  rw [he] at hp
  have h := (abs_sub_le_iff.mp hp).1
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # A bounded collision window preserving the elastic symmetries -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def collisionWindow (N : ℝ) : Set ((X × (Velocity × Velocity)) × Sphere) :=
  {z | ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ N^2}

def windowKernel (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (collisionWindow N).indicator (fun z => collisionKernel z.1.2.1 z.1.2.2 z.2) z

theorem collisionWindow_measurable (N : ℝ) : MeasurableSet (collisionWindow (X := X) N) := by
  apply measurableSet_le _ measurable_const
  fun_prop

theorem windowKernel_measurable (N : ℝ) : Measurable (windowKernel (X := X) N) := by
  apply Measurable.indicator _ (collisionWindow_measurable N)
  unfold collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem collisionWindow_bounds {N : ℝ} (hN : 0 ≤ N)
    {z : (X × (Velocity × Velocity)) × Sphere} (hz : z ∈ collisionWindow N) :
    ‖z.1.2.1‖ ≤ N ∧ ‖z.1.2.2‖ ≤ N := by
  change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ N^2 at hz
  constructor <;> nlinarith [sq_nonneg ‖z.1.2.1‖,sq_nonneg ‖z.1.2.2‖,
    norm_nonneg z.1.2.1,norm_nonneg z.1.2.2]

omit [MeasurableSpace X] in
theorem windowKernel_bounds {N : ℝ} (hN : 0 ≤ N)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ windowKernel N z ∧ windowKernel N z ≤ 2*N := by
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem hz]
    have hb := collisionWindow_bounds hN hz
    exact ⟨collisionKernel_nonneg _ _ _, (collisionKernel_le_norm _ _ _).trans
      ((norm_sub_le _ _).trans (by linarith [hb.1,hb.2]))⟩
  · simp only [windowKernel,indicator_of_notMem hz]
    exact ⟨le_rfl,by positivity⟩

omit [MeasurableSpace X] in
theorem windowKernel_scatter (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N (scatterTriple z) = windowKernel N z := by
  have hω : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hω
  have hw : scatterTriple z ∈ collisionWindow N ↔ z ∈ collisionWindow N := by
    change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
      ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ N^2) ↔ _
    rw [he]
    rfl
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem (hw.mpr hz),windowKernel,indicator_of_mem hz]
    exact collisionKernel_scatter _ _ _ hω
  · rw [windowKernel,indicator_of_notMem (fun h => hz (hw.mp h)),
      windowKernel,indicator_of_notMem hz]

theorem windowKernel_particleSwap (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N (particleSwap z) = windowKernel N z := by
  have hw : particleSwap z ∈ collisionWindow N ↔ z ∈ collisionWindow N := by
    change (‖z.1.2.2‖^2+‖z.1.2.1‖^2 ≤ N^2) ↔ _
    rw [add_comm]
    rfl
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem (hw.mpr hz),windowKernel,indicator_of_mem hz]
    exact hk
  · rw [windowKernel,indicator_of_notMem (fun h => hz (hw.mp h)),
      windowKernel,indicator_of_notMem hz]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Closedness of the cap under convergence of bounded seed parameters -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

def affineSeed (f ψ : JetPrototype.Phase → ℝ) (ell : ℝ) (p : JetPrototype.Phase) : ℝ :=
  f p+ell*ψ p

def hotPeak {I : Type*} [Countable I] {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (δ : ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (F : PeriodicMildState q b L T R f₀) : ℝ :=
  Cap.peak T δ (fun t => PhaseEssSup.size (fun p =>
    F.value (t,p)-∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)))

theorem affineSeed_difference {f ψ : JetPrototype.Phase → ℝ} {M : ℝ}
    (hψ : ∀ p, |ψ p| ≤ M) (a b : ℝ) (p : JetPrototype.Phase) :
    |affineSeed f ψ a p-affineSeed f ψ b p| ≤ |a-b| * M := by
  have he : affineSeed f ψ a p-affineSeed f ψ b p = (a-b)*ψ p := by unfold affineSeed; ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_left (hψ p) (abs_nonneg _)

theorem exists_cap_limit {I : Type*} [Countable I] {q b L T R δ M ell : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    {elln : ℕ → ℝ} (hell : Tendsto elln atTop (𝓝 ell))
    (hinit : ∀ p, affineSeed f ψ ell p ≤ R)
    (hinitn : ∀ n p, affineSeed f ψ (elln n) p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p)
    (hdomn : ∀ n (s : Finset I), ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ (elln n) p)
    (F : ∀ n, PeriodicMildState q b L T R (affineSeed f ψ (elln n)))
    (hcap : ∀ n, hotPeak δ c₀ (F n) ≤ 1) :
    ∃ G : PeriodicMildState q b L T R (affineSeed f ψ ell), hotPeak δ c₀ G ≤ 1 := by
  let a (n : ℕ) := |elln n-ell| * M
  have ha (n) : 0 ≤ a n := mul_nonneg (abs_nonneg _) hM
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h := (hell.sub_const ell).abs.mul_const M
    simpa only [sub_self,abs_zero,zero_mul] using h
  have hseed (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |affineSeed f ψ (elln n) p-affineSeed f ψ ell p| ≤ a n :=
    ae_of_all _ (affineSeed_difference hψ (elln n) ell)
  obtain ⟨_,_,G,_⟩ := exists_seed_limit hq hb hL hT hR hloss F ha ha0 hseed
  obtain ⟨C,hC,hst⟩ := exists_rebuilt_hot_stability_constant (I := I) hq hb hL hT hR hloss
  have hgm : Measurable (affineSeed f ψ ell) := hfm.add (hψm.const_mul ell)
  have hnm (n) : Measurable (affineSeed f ψ (elln n)) := hfm.add (hψm.const_mul (elln n))
  have hGreg := rebuilt_hot_continuous hq hb hL hT hR hloss G.measurable_value hgm hc₀m
    G.value_bounds hinit hc₀ hdom (G.all_mild hT)
  have hdiff (n) : |hotPeak δ c₀ (F n)-hotPeak δ c₀ G| ≤ C*a n/δ := by
    have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss (F n).measurable_value (hnm n) hc₀m
      (F n).value_bounds (hinitn n) hc₀ (hdomn n) ((F n).all_mild hT)
    exact Cap.peak_difference hT hδ (mul_nonneg hC.le (ha n)) hreg hGreg
      (hst (ha n) (F n).measurable_value G.measurable_value hc₀m (F n).value_bounds G.value_bounds
        hc₀ (hdomn n) hdom (hseed n) ((F n).all_mild hT) (G.all_mild hT))
  refine ⟨G,?_⟩
  have hupper (n) : hotPeak δ c₀ G ≤ 1+C*a n/δ := by
    have h := (abs_sub_le_iff.mp (hdiff n)).2
    linarith [hcap n]
  have hlim : Tendsto (fun n => 1+C*a n/δ) atTop (𝓝 1) := by
    have h := ((ha0.const_mul C).div_const δ).const_add 1
    simpa only [mul_zero,zero_div,add_zero] using h
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hupper

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Strict caps persist for nearby affine seed parameters -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem strict_cap_open {I : Type*} [Countable I] {q b A B T δ M L₀ ell : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hBA : B < A) (hell : ell ∈ Icc 0 L₀)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A)
    (hseedB : ∀ μ ∈ Icc 0 L₀, ∀ p, 0 ≤ affineSeed f ψ μ p ∧ affineSeed f ψ μ p ≤ A)
    (hdom : ∀ μ ∈ Icc 0 L₀, ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ μ p)
    (hper : ∀ μ ∈ Icc 0 L₀, ∀ n p,
      affineSeed f ψ μ (shift (JetCopyDatum.displacement n) p) = affineSeed f ψ μ p)
    (F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell))
    (hsmall : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B)
    (hcap : hotPeak δ c₀ F < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ μ ∈ Icc 0 L₀, |μ-ell| < r →
      ∃ G : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ μ), hotPeak δ c₀ G < 1 := by
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  obtain ⟨ε,hε,hnear⟩ := nearby_seed_exists hq hb hA hT hBA F hsmall
  obtain ⟨C,hC,hst⟩ := exists_rebuilt_hot_stability_constant (I := I) hq hb hL hT hR hloss
  let gap := 1-hotPeak δ c₀ F
  have hg : 0 < gap := sub_pos.mpr hcap
  let r := min (ε/(M+1)) (δ*gap/((C+1)*(M+1)))
  have hr : 0 < r := lt_min (div_pos hε (by positivity))
    (div_pos (mul_pos hδ hg) (by positivity))
  refine ⟨r,hr,?_⟩
  intro μ hμ hdist
  let d := |μ-ell|
  let e := d*M
  have hd : 0 ≤ d := abs_nonneg _
  have he : 0 ≤ e := mul_nonneg hd hM
  have hde : d*(M+1) < ε := (lt_div_iff₀ (by positivity : 0 < M+1)).mp
    (lt_of_lt_of_le hdist (min_le_left _ _))
  have heε : e ≤ ε := by dsimp [e]; nlinarith
  have hde' : d*((C+1)*(M+1)) < δ*gap :=
    (lt_div_iff₀ (by positivity : 0 < (C+1)*(M+1))).mp
      (lt_of_lt_of_le hdist (min_le_right _ _))
  have hce : C*e < δ*gap := by
    have hm : C*M ≤ (C+1)*(M+1) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hm hd
    calc
      C*e = d*(C*M) := by dsimp [e]; ring
      _ ≤ d*((C+1)*(M+1)) := hh
      _ < δ*gap := hde'
  have hdata (μ) (hμ : μ ∈ Icc 0 L₀) : Measurable (affineSeed f ψ μ) := hfm.add (hψm.const_mul μ)
  have hseed : ∀ᵐ p ∂FlightMeasure.phaseVolume, |affineSeed f ψ μ p-affineSeed f ψ ell p| ≤ e :=
    ae_of_all _ (affineSeed_difference hψ μ ell)
  obtain ⟨G⟩ := hnear (hdata μ hμ) (hseedB μ hμ) (hper μ hμ)
    (hseed.mono (fun p hp => hp.trans heε))
  have hupper (a) (ha : a ∈ Icc 0 L₀) (p) : affineSeed f ψ a p ≤ 2*A :=
    ((hseedB a ha p).2).trans (by linarith)
  have hregF := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value (hdata ell hell) hc₀m
    F.value_bounds (hupper ell hell) hc₀ (hdom ell hell) (F.all_mild hT)
  have hregG := rebuilt_hot_continuous hq hb hL hT hR hloss G.measurable_value (hdata μ hμ) hc₀m
    G.value_bounds (hupper μ hμ) hc₀ (hdom μ hμ) (G.all_mild hT)
  have hdiff : |hotPeak δ c₀ G-hotPeak δ c₀ F| ≤ C*e/δ :=
    Cap.peak_difference hT hδ (mul_nonneg hC.le he) hregG hregF
      (hst he G.measurable_value F.measurable_value hc₀m G.value_bounds F.value_bounds hc₀
        (hdom μ hμ) (hdom ell hell) hseed (G.all_mild hT) (F.all_mild hT))
  have hratio : C*e/δ < gap := (div_lt_iff₀ hδ).mpr (by nlinarith [hce])
  refine ⟨G,?_⟩
  have hh := (abs_sub_le_iff.mp hdiff).1
  dsimp [gap] at hratio
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Small primitives of bounded periodic functions of mean zero -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem bounded_intervalIntegrable {g : ℝ → ℝ} (hm : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (a b : ℝ) : IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem primitive_bound {g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0) (x : ℝ) :
    |∫ t in 0..x, g t| ≤ p := by
  let e := Int.fract (x/p)*p
  have he : e ∈ Ico 0 p := Int.fract_div_mul_self_mem_Ico p x hp
  have hi := bounded_intervalIntegrable hm hb
  have heq : (∫ t in 0..x, g t) = ∫ t in 0..e, g t := by
    rw [← Int.fract_div_mul_self_add_zsmul_eq p x hp.ne',
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 e) (hi e _),
      hper.intervalIntegral_add_zsmul_eq _ e hi,hper.intervalIntegral_add_eq e 0,
      zero_add,hmean,smul_zero,add_zero]
  rw [heq]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := e) (C := (1:ℝ)) (f := g) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg he.1,one_mul] at hnorm
  exact hnorm.trans he.2.le

theorem interval_bound {g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0) (a b : ℝ) :
    |∫ t in a..b, g t| ≤ 2*p := by
  have hi := bounded_intervalIntegrable hm hb
  have heq := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  have ha := primitive_bound hp hper hm hb hmean a
  have hb' := primitive_bound hp hper hm hb hmean b
  have htri := abs_sub_le (∫ t in 0..b, g t) 0 (∫ t in 0..a, g t)
  rw [sub_zero,zero_sub,abs_neg] at htri
  have hsub : (∫ t in a..b, g t) = (∫ t in 0..b, g t)-(∫ t in 0..a, g t) := by linarith
  rw [hsub]
  linarith

theorem test_bound {g φ : ℝ → ℝ} {p a b : ℝ} (hp : 0 < p) (hab : a ≤ b)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0)
    (hφ : AbsolutelyContinuousOnInterval φ a b) :
    |∫ t in a..b, φ t*g t| ≤ (2*p)*(|φ b|+∫ t in a..b, |deriv φ t|) := by
  let G : ℝ → ℝ := fun x => ∫ t in a..x, g t
  have hi := bounded_intervalIntegrable hm hb a b
  have hG : AbsolutelyContinuousOnInterval G a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hder : ∀ᵐ x, x ∈ uIcc a b → deriv G x = g x := by
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxab
    exact (hx hxab a (by simp)).deriv
  have heq : (∫ t in a..b, φ t*g t) = φ b*G b-(∫ t in a..b, deriv φ t*G t) := by
    calc
      _ = ∫ t in a..b, φ t*deriv G t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hder] with x hx hxab
        rw [hx (uIoc_subset_uIcc hxab)]
      _ = _ := by
        rw [hφ.integral_mul_deriv_eq_deriv_mul hG]
        simp [G]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun t => deriv φ t*G t) (g := fun t => (2*p)*|deriv φ t|) ?_
    (hφ.intervalIntegrable_deriv.norm.const_mul (2*p))
  · rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul] at hnorm
    rw [heq]
    have hGb := interval_bound hp hper hm hb hmean a b
    have hm := mul_le_mul_of_nonneg_left hGb (abs_nonneg (φ b))
    have ht := abs_sub (φ b*G b) (∫ t in a..b, deriv φ t*G t)
    rw [abs_mul] at ht
    nlinarith
  · filter_upwards [] with x _
    have hGB := interval_bound hp hper hm hb hmean a x
    change |deriv φ x*G x| ≤ (2*p)*|deriv φ x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hGB (abs_nonneg _)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

section

/-! # Selecting a seed whose periodic solution attains the cap -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem select_seed_at_cap {I : Type*} [Countable I] {q b A B T δ M L₀ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hBA : B < A) (hL₀ : 0 < L₀)
    {f ψ : JetPrototype.Phase → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hψ : ∀ p, |ψ p| ≤ M)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ 2*A)
    (hseedB : ∀ ell ∈ Icc 0 L₀, ∀ p, 0 ≤ affineSeed f ψ ell p ∧ affineSeed f ψ ell p ≤ A)
    (hdom : ∀ ell ∈ Icc 0 L₀, ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ affineSeed f ψ ell p)
    (hper : ∀ ell ∈ Icc 0 L₀, ∀ n p,
      affineSeed f ψ ell (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = affineSeed f ψ ell p)
    (hzero : ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ 0),
      hotPeak δ c₀ F < 1)
    (hlarge : ∀ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ L₀),
      1 < hotPeak δ c₀ F)
    (hbound : ∀ ell ∈ Icc 0 L₀,
      ∀ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell),
      hotPeak δ c₀ F ≤ 1 →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤ B) :
    ∃ ell ∈ Icc 0 L₀,
      ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell), hotPeak δ c₀ F = 1 := by
  classical
  let D : Set ℝ := {ell | ell ∈ Icc 0 L₀ ∧
    ∃ F : PeriodicMildState q b (damping q b A) T (2*A) (affineSeed f ψ ell), hotPeak δ c₀ F ≤ 1}
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hupper (ell) (hell : ell ∈ Icc 0 L₀) (p) : affineSeed f ψ ell p ≤ 2*A :=
    ((hseedB ell hell p).2).trans (by linarith)
  have hclosed : IsClosed D := by
    apply isSeqClosed_iff_isClosed.mp
    intro u ell hu hulim
    have hell : ell ∈ Icc 0 L₀ := isClosed_Icc.mem_of_tendsto hulim
      (Eventually.of_forall (fun n => (hu n).1))
    choose F hFc using fun n => (hu n).2
    obtain ⟨G,hG⟩ := exists_cap_limit hq hb hL hT hR hδ hM hloss hfm hψm hψ hc₀m hc₀ hulim
      (hupper ell hell) (fun n => hupper (u n) (hu n).1)
      (hdom ell hell) (fun n => hdom (u n) (hu n).1) F hFc
    exact ⟨hell,G,hG⟩
  have hnonempty : D.Nonempty := by
    obtain ⟨F,hF⟩ := hzero
    exact ⟨0,⟨⟨le_rfl,hL₀.le⟩,F,hF.le⟩⟩
  have hbdd : BddAbove D := ⟨L₀,fun ell hell => hell.1.2⟩
  let x := sSup D
  have hx : x ∈ D := hclosed.csSup_mem hnonempty hbdd
  have hxL : x < L₀ := by
    apply lt_of_le_of_ne hx.1.2
    intro he
    have hex := hx.2
    rw [he] at hex
    obtain ⟨F,hF⟩ := hex
    exact (not_lt_of_ge hF) (hlarge F)
  obtain ⟨F,hF⟩ := hx.2
  refine ⟨x,hx.1,F,?_⟩
  by_contra hne
  have hstrict : hotPeak δ c₀ F < 1 := lt_of_le_of_ne hF hne
  obtain ⟨r,hr,hopen⟩ := strict_cap_open hq hb hA hT hδ hM hBA hx.1 hfm hψm hψ hc₀m hc₀
    hseedB hdom hper F (hbound x hx.1 F hF) hstrict
  let d := min (r/2) ((L₀-x)/2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hdr : d < r := (min_le_left _ _).trans_lt (by linarith)
  have hdx : d ≤ (L₀-x)/2 := min_le_right _ _
  have hm : x+d ∈ Icc 0 L₀ := ⟨by linarith [hx.1.1],by linarith⟩
  have hdist : |x+d-x| < r := by rw [add_sub_cancel_left,abs_of_pos hd]; exact hdr
  obtain ⟨G,hG⟩ := hopen (x+d) hm hdist
  have hmD : x+d ∈ D := ⟨hm,G,hG.le⟩
  have hle : x+d ≤ x := le_csSup hbdd hmD
  linarith

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # A symmetric bounded-rate approximation for global periodic construction -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def rateSum (a b c d : ℝ) : ℝ := a+b+c+d

def pairRate (N a b c d : ℝ) : ℝ :=
  N^2*(a/(N+rateSum a b c d))*(b/(N+rateSum a b c d))

theorem rateSum_nonneg {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ rateSum a b c d := by unfold rateSum; positivity

theorem pairRate_eq (N a b c d : ℝ) :
    pairRate N a b c d = N^2*a*b/(N+rateSum a b c d)^2 := by unfold pairRate; simp only [div_eq_mul_inv, ← inv_pow]; ring

theorem pairRate_nonneg {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ pairRate N a b c d := by
  have hs := rateSum_nonneg ha hb hc hd
  unfold pairRate
  positivity

theorem pairRate_le_square {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairRate N a b c d ≤ N^2 := by
  have hs := rateSum_nonneg ha hb hc hd
  have hpos : 0 < N+rateSum a b c d := add_pos_of_pos_of_nonneg hN hs
  have h₁ : a/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  have h₂ : b/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  unfold pairRate
  calc
    _ ≤ N^2*1*1 := by gcongr
    _ = _ := by ring

theorem pairRate_swap_inputs (N a b c d : ℝ) :
    pairRate N b a c d = pairRate N a b c d := by unfold pairRate rateSum; ring

theorem pairRate_swap_outputs (N a b c d : ℝ) :
    pairRate N a b d c = pairRate N a b c d := by unfold pairRate rateSum; ring

theorem pairRate_tendsto (a b c d : ℝ) :
    Tendsto (fun N : ℝ => pairRate N a b c d) atTop (𝓝 (a*b)) := by
  let S := rateSum a b c d
  have hs : Tendsto (fun N : ℝ => S/N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun N : ℝ => 1/(1+S/N)) atTop (𝓝 1) := by
    have ht0 : Tendsto (fun N : ℝ => 1/(1+S/N)) atTop (𝓝 ((1:ℝ)/(1+0))) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).div
        (tendsto_const_nhds.add hs) (by norm_num)
    simpa only [add_zero, div_one] using ht0
  have hh := (ht.pow 2).const_mul (a*b)
  have hh' : Tendsto (fun N : ℝ => a*b*(1/(1+S/N))^2) atTop (𝓝 (a*b)) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  rw [pairRate_eq]
  rw [one_add_div hN.ne', one_div_div]
  dsimp [S]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Weak averaging on bounded intervals, uniformly over the phase -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem ac_test_tendsto_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0)
    {φ : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    Tendsto (fun n => ∫ x in a..b, φ x*g n x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun n => test_bound (hp n) hab (hper n) (hm n) (hb n) (hmean n) hφ)
  simpa only [mul_zero,zero_mul] using
    (hplim.const_mul 2).mul_const (|φ b|+∫ x in a..b, |deriv φ x|)

theorem uniformContinuous_test_tendsto_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0)
    {φ : ℝ → ℝ} (hφ : UniformContinuous φ) :
    Tendsto (fun n => ∫ x in a..b, φ x*g n x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(2*(|b-a|+1))
  have hden : 0 < 2*(|b-a|+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(2*(|b-a|+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨f,hfc,hf⟩ := hφ.exists_contDiff_dist_le hδ
  have hfAC : AbsolutelyContinuousOnInterval f a b :=
    (hfc.contDiffOn.of_le (by norm_num)).absolutelyContinuousOnInterval
  have hfzero := ac_test_tendsto_zero hab hp hplim hper hm hb hmean hfAC
  have hfsmall := Metric.tendsto_nhds.mp hfzero (ε/2) (by positivity)
  filter_upwards [hfsmall] with n hn
  have hiφ := (bounded_intervalIntegrable (hm n) (hb n) a b).continuousOn_mul
    hφ.continuous.continuousOn
  have hif := (bounded_intervalIntegrable (hm n) (hb n) a b).continuousOn_mul
    hfc.continuous.continuousOn
  have hdiff : (∫ x in a..b, φ x*g n x)-(∫ x in a..b, f x*g n x) =
      ∫ x in a..b, (φ x-f x)*g n x := by
    rw [← intervalIntegral.integral_sub hiφ hif]
    congr 1
    funext x
    ring
  have herr : |(∫ x in a..b, φ x*g n x)-(∫ x in a..b, f x*g n x)| ≤ δ*|b-a| := by
    rw [hdiff,← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [Real.norm_eq_abs,abs_mul]
    have hx : |φ x-f x| ≤ δ := by
      simpa only [Real.dist_eq,abs_sub_comm] using (hf x).le
    exact (mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg _)).trans
      (by simpa only [mul_one] using hx)
  rw [Real.dist_eq,sub_zero] at hn ⊢
  have htri := abs_sub_le (∫ x in a..b, φ x*g n x) (∫ x in a..b, f x*g n x) 0
  simp only [sub_zero] at htri
  nlinarith

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

section

/-! # Vanishing periodic oscillations against every L1 test -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem weakStar_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ}
    (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0) :
    Compactness.WeakStarLInfConverges volume g (fun _ => 0) := by
  apply Compactness.weakStar_of_continuous_compact_tests hm measurable_const
    (C := 1) (by norm_num) (Eventually.of_forall (fun n => ae_of_all _ (hb n)))
    (ae_of_all _ (fun _ => by norm_num))
  intro φ hφ hc
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0:ℝ)
  have hzero (x : ℝ) (hx : x ∉ Ioc (-R) R) : φ x = 0 := by
    by_contra hxφ
    have hnorm : |x| < R := by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hball (subset_closure hxφ)
    exact hx ⟨(abs_lt.mp hnorm).1,(abs_lt.mp hnorm).2.le⟩
  have heq (n : ℕ) : (∫ x, φ x*g n x) = ∫ x in (-R)..R, φ x*g n x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hzero x hx,zero_mul])).symm
  simp only [mul_zero,integral_zero]
  simp_rw [heq]
  exact uniformContinuous_test_tendsto_zero (by linarith) hp hplim hper hm hb hmean
    (hc.uniformContinuous_of_continuous hφ)

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

section

/-! # Uniform stability of the regularized collision fractions -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem fraction_difference_le {N a b s t : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (has : a ≤ s) (hb : 0 ≤ b) (hbt : b ≤ t) :
    |a/(N+s)-b/(N+t)| ≤ (|a-b|+|s-t|)/N := by
  have hs : 0 ≤ s := ha.trans has
  have ht : 0 ≤ t := hb.trans hbt
  have hNs : 0 < N+s := add_pos_of_pos_of_nonneg hN hs
  have hNt : 0 < N+t := add_pos_of_pos_of_nonneg hN ht
  have hratio : 0 ≤ b/(N+t) := div_nonneg hb hNt.le
  have hratio1 : b/(N+t) ≤ 1 := (div_le_one hNt).mpr (by linarith)
  have he : a/(N+s)-b/(N+t) = (a-b)/(N+s)+(b/(N+t))*(t-s)/(N+s) := by
    field_simp [hNs.ne', hNt.ne']
    ring
  rw [he]
  calc
    _ ≤ |(a-b)/(N+s)|+|(b/(N+t))*(t-s)/(N+s)| := abs_add_le _ _
    _ = |a-b|/(N+s)+(b/(N+t))*|s-t|/(N+s) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hNs,abs_of_nonneg hratio,abs_sub_comm t s]
    _ ≤ |a-b|/(N+s)+|s-t|/(N+s) := by
      gcongr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio1 (abs_nonneg (s-t))
    _ = (|a-b|+|s-t|)/(N+s) := by ring
    _ ≤ (|a-b|+|s-t|)/N := by
      gcongr
      linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global Lipschitz and linear bounds for the bounded collision rates -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem unit_product_difference {a b c d : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    |a*b-c*d| ≤ |b-d|+|a-c| := by
  have he : a*b-c*d = a*(b-d)+(a-c)*d := by ring
  rw [he]
  calc
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hd]
    _ ≤ 1*|b-d|+|a-c| *1 := by gcongr
    _ = _ := by ring

theorem rateSum_difference_le (a b c d a' b' c' d' : ℝ) :
    |rateSum a b c d-rateSum a' b' c' d'| ≤
      |a-a'|+|b-b'|+|c-c'|+|d-d'| := by
  unfold rateSum
  calc
    _ = |((a-a')+(b-b'))+(c-c')+(d-d')| := by congr 1; ring
    _ ≤ |(a-a')+(b-b')+(c-c')|+|d-d'| := abs_add_le _ _
    _ ≤ (|(a-a')+(b-b')|+|c-c'|)+|d-d'| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a-a'|+|b-b'|+|c-c'|)+|d-d'| := by gcongr; exact abs_add_le _ _

theorem pairRate_difference_le {N a b c d a' b' c' d' : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d') :
    |pairRate N a b c d-pairRate N a' b' c' d'| ≤
      3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := by
  let S := rateSum a b c d
  let S' := rateSum a' b' c' d'
  have hs : 0 ≤ S := rateSum_nonneg ha hb hc hd
  have hs' : 0 ≤ S' := rateSum_nonneg ha' hb' hc' hd'
  have has : a ≤ S := by dsimp [S,rateSum]; linarith
  have hbs : b ≤ S := by dsimp [S,rateSum]; linarith
  have has' : a' ≤ S' := by dsimp [S',rateSum]; linarith
  have hbs' : b' ≤ S' := by dsimp [S',rateSum]; linarith
  have hα : 0 ≤ a/(N+S) := div_nonneg ha (by linarith)
  have hα1 : a/(N+S) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hβ' : 0 ≤ b'/(N+S') := div_nonneg hb' (by linarith)
  have hβ'1 : b'/(N+S') ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hdiff := unit_product_difference (b := b/(N+S)) (c := a'/(N+S')) hα hα1 hβ' hβ'1
  have hfa := fraction_difference_le hN ha has ha' has'
  have hfb := fraction_difference_le hN hb hbs hb' hbs'
  have hsum := rateSum_difference_le a b c d a' b' c' d'
  change |N^2*(a/(N+S))*(b/(N+S))-N^2*(a'/(N+S'))*(b'/(N+S'))| ≤ _
  rw [show N^2*(a/(N+S))*(b/(N+S))-N^2*(a'/(N+S'))*(b'/(N+S')) =
    N^2*((a/(N+S))*(b/(N+S))-(a'/(N+S'))*(b'/(N+S'))) by ring,
    abs_mul,abs_of_nonneg (sq_nonneg N)]
  calc
    _ ≤ N^2*(|b/(N+S)-b'/(N+S')|+|a/(N+S)-a'/(N+S')|) := by gcongr
    _ ≤ N^2*((|b-b'|+|S-S'|)/N+(|a-a'|+|S-S'|)/N) := by gcongr
    _ ≤ N^2*((|b-b'|+(|a-a'|+|b-b'|+|c-c'|+|d-d'|))/N+
      (|a-a'|+(|a-a'|+|b-b'|+|c-c'|+|d-d'|))/N) := by gcongr
    _ ≤ 3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := by
      field_simp
      nlinarith [abs_nonneg (a-a'),abs_nonneg (b-b'),abs_nonneg (c-c'),abs_nonneg (d-d')]

theorem pairRate_le_linear {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairRate N a b c d ≤ N*a := by
  have hs := rateSum_nonneg ha hb hc hd
  have hpos : 0 < N+rateSum a b c d := add_pos_of_pos_of_nonneg hN hs
  have hratio : b/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  have haN : a/(N+rateSum a b c d) ≤ a/N := by gcongr; linarith
  unfold pairRate
  calc
    _ ≤ N^2*(a/N)*1 := by gcongr
    _ = N*a := by field_simp [hN.ne']

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual symmetric regularized hard-sphere collision rates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def regularizedPreRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  windowKernel N z * pairRate N (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))

def regularizedPostRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPreRate N f (scatterTriple z)

theorem regularizedPreRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (regularizedPreRate N f) := by
  apply (windowKernel_measurable N).mul
  unfold pairRate rateSum scatterLeft scatterRight normalComponent
  fun_prop

theorem regularizedPostRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (regularizedPostRate N f) :=
  (regularizedPreRate_measurable N hf).comp scatterTriple_measurable

omit [MeasurableSpace X] in
theorem regularizedPostRate_formula (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f z = windowKernel N z *
      pairRate N (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2)) := by
  have hω : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  unfold regularizedPostRate regularizedPreRate
  rw [windowKernel_scatter]
  change windowKernel N z * pairRate N _ _
    (f (z.1.1,scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2))
    (f (z.1.1,scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)) = _
  rw [scatterLeft_involutive _ _ _ hω,scatterRight_involutive _ _ _ hω]
  rfl

omit [MeasurableSpace X] in
theorem regularizedPostRate_scatter (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f (scatterTriple z) = regularizedPreRate N f z := by
  unfold regularizedPostRate
  rw [scatterTriple_involutive]

theorem regularizedPreRate_particleSwap (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f (particleSwap z) = regularizedPreRate N f z := by
  unfold regularizedPreRate
  rw [windowKernel_particleSwap]
  change windowKernel N z * pairRate N (f (z.1.1,z.1.2.2)) (f (z.1.1,z.1.2.1))
    (f (z.1.1,scatterLeft z.1.2.2 z.1.2.1 z.2))
    (f (z.1.1,scatterRight z.1.2.2 z.1.2.1 z.2)) = _
  rw [scatterLeft_swap z.1.2.2 z.1.2.1 z.2,scatterRight_swap z.1.2.2 z.1.2.1 z.2]
  congr 1
  unfold pairRate rateSum
  ring

omit [MeasurableSpace X] in
theorem regularizedPreRate_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ regularizedPreRate N f z ∧ regularizedPreRate N f z ≤ 2*N^3 := by
  have hw := windowKernel_bounds hN.le z
  have hn := pairRate_nonneg hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hb := pairRate_le_square hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  exact ⟨mul_nonneg hw.1 hn,(mul_le_mul hw.2 hb hn (by positivity)).trans_eq (by ring)⟩

omit [MeasurableSpace X] in
theorem regularizedPreRate_linear {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f z ≤ 2*N^2*f (z.1.1,z.1.2.1) := by
  have hw := windowKernel_bounds hN.le z
  have hn := pairRate_nonneg hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hb := pairRate_le_linear hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  exact (mul_le_mul hw.2 hb hn (by positivity)).trans_eq (by ring)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform compact-velocity logarithmic bounds for positive regularization -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem maxwellian_le_center (v : Velocity) : maxwellian v ≤ maxwellian 0 := by
  have h0 : maxwellian 0 = (2*Real.pi)^(-(3/2:ℝ)) := by norm_num [maxwellian]
  rw [h0]
  have he : Real.exp (-‖v‖^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖v‖])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem maxwellian_lower_on_ball {N : ℝ} (hN : 0 ≤ N) (v : Velocity) (hv : ‖v‖ ≤ N) :
    maxwellian 0*Real.exp (-N^2/2) ≤ maxwellian v := by
  have h0 : maxwellian 0 = (2*Real.pi)^(-(3/2:ℝ)) := by norm_num [maxwellian]
  rw [h0]
  unfold maxwellian
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hs := (sq_le_sq₀ (norm_nonneg _) hN).mpr hv
  linarith

def logRegularizationConstant (N B : ℝ) : ℝ :=
  |Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1)|

theorem log_regularization_bound {N B δ a : ℝ} (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (haB : a ≤ B)
    (v : Velocity) (hv : ‖v‖ ≤ N) :
    |Real.log ((a+δ*maxwellian v)/maxwellian v)| ≤
      |Real.log δ|+logRegularizationConstant N B := by
  have hm := maxwellian_pos v
  have hm0 : 0 < maxwellian 0*Real.exp (-N^2/2) :=
    mul_pos (maxwellian_pos 0) (Real.exp_pos _)
  have hl := maxwellian_lower_on_ball hN v hv
  have hu : 0 < B/(maxwellian 0*Real.exp (-N^2/2))+1 := by positivity
  have hlo : δ ≤ (a+δ*maxwellian v)/maxwellian v := by
    rw [le_div_iff₀ hm]
    linarith
  have hhi : (a+δ*maxwellian v)/maxwellian v ≤
      B/(maxwellian 0*Real.exp (-N^2/2))+1 := by
    calc
      _ = a/maxwellian v+δ := by field_simp
      _ ≤ B/(maxwellian 0*Real.exp (-N^2/2))+1 :=
        add_le_add (div_le_div₀ hB haB hm0 hl) hδ1
  have hloglo := Real.log_le_log hδ hlo
  have hloghi := Real.log_le_log (hδ.trans_le hlo) hhi
  unfold logRegularizationConstant
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log δ),abs_nonneg (Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1))]
  · linarith [le_abs_self (Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1)),abs_nonneg (Real.log δ)]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integral symmetries of the actual regularized collision rates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPostRate_particleSwap (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f (particleSwap z) = regularizedPostRate N f z := by
  unfold regularizedPostRate
  rw [scatterTriple_particleSwap,regularizedPreRate_particleSwap]

theorem integral_regularizedPostRate (μ : Measure X) [SFinite μ] (N : ℝ) (f : X × Velocity → ℝ) :
    (∫ z, regularizedPostRate N f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      ∫ z, regularizedPreRate N f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
  (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (regularizedPreRate N f)

theorem integral_regularizedPreRate_swap (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z)
  simp only [regularizedPreRate_particleSwap] at h
  exact h.symm

theorem integral_regularizedPostRate_swap (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
  simp only [regularizedPostRate_particleSwap] at h
  exact h.symm

theorem integral_regularizedPostRate_scatter (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
  simp only [regularizedPostRate_scatter] at h
  exact h.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Bounded measurable gain and loss in the symmetric approximation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def fiberMeasure (N : ℝ) : Measure (Velocity × Sphere) :=
  ((volume : Measure Velocity).restrict (Metric.closedBall 0 N)).prod sphereArea

instance fiberMeasure_finite (N : ℝ) : IsFiniteMeasure (fiberMeasure N) := by
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 N)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne
  unfold fiberMeasure
  infer_instance

def gain (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, regularizedPostRate N f (collisionGrouping.symm (p,q)) ∂fiberMeasure N

def loss (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, regularizedPreRate N f (collisionGrouping.symm (p,q)) ∂fiberMeasure N

def gainBound (N : ℝ) : ℝ := 2*N^3*(fiberMeasure N).real Set.univ

def lossBound (N : ℝ) : ℝ := 2*N^2*(fiberMeasure N).real Set.univ

theorem gain_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gain N f) :=
  ((regularizedPostRate_measurable N hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem loss_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (loss N f) :=
  ((regularizedPreRate_measurable N hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem pre_fiber_integrable {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    Integrable (fun q => regularizedPreRate N f (collisionGrouping.symm (p,q))) (fiberMeasure N) := by
  apply (integrable_const (2*N^3)).mono'
    (((regularizedPreRate_measurable N hfm).comp collisionGrouping.symm.measurable).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [] with q
  change ‖regularizedPreRate N f (collisionGrouping.symm (p,q))‖ ≤ _
  rw [Real.norm_of_nonneg (regularizedPreRate_bounds hN hf _).1]
  exact (regularizedPreRate_bounds hN hf _).2

theorem post_fiber_integrable {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    Integrable (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q))) (fiberMeasure N) := by
  apply (integrable_const (2*N^3)).mono'
    (((regularizedPostRate_measurable N hfm).comp collisionGrouping.symm.measurable).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [] with q
  change ‖regularizedPreRate N f (scatterTriple (collisionGrouping.symm (p,q)))‖ ≤ _
  rw [Real.norm_of_nonneg (regularizedPreRate_bounds hN hf _).1]
  exact (regularizedPreRate_bounds hN hf _).2

theorem gain_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ gain N f p ∧ gain N f p ≤ gainBound N := by
  constructor
  · exact integral_nonneg (fun _ => (regularizedPreRate_bounds hN hf _).1)
  · calc
      _ ≤ ∫ _q, 2*N^3 ∂fiberMeasure N := integral_mono (post_fiber_integrable hN hfm hf p)
        (integrable_const _) (fun _ => (regularizedPreRate_bounds hN hf _).2)
      _ = _ := by simp only [integral_const,smul_eq_mul,gainBound]; ring

theorem loss_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ loss N f p ∧ loss N f p ≤ lossBound N*f p := by
  constructor
  · exact integral_nonneg (fun _ => (regularizedPreRate_bounds hN hf _).1)
  · calc
      _ ≤ ∫ _q, 2*N^2*f p ∂fiberMeasure N := integral_mono (pre_fiber_integrable hN hfm hf p)
        (integrable_const _) (fun q => regularizedPreRate_linear hN hf (collisionGrouping.symm (p,q)))
      _ = _ := by simp only [integral_const,smul_eq_mul,lossBound]; ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
