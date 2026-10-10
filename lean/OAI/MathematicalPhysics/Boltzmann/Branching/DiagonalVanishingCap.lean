import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoefficientExtraction
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledMassAgreement
import OAI.MathematicalPhysics.Boltzmann.Branching.SeparationBoxContainment
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDilationIntegral
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

section

/-! # A diagonal selection controlling finitely many tests at each step -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness

theorem exists_diagonal_finite_tests {a : ℕ → ℕ → ℝ} {b : ℕ → ℕ → ℕ → ℝ}
    {c : ℕ → ℕ → ℝ} {δ : ℕ → ℝ}
    (ha : ∀ n, Tendsto (a n) atTop (𝓝 0))
    (hb : ∀ n j, j ≤ n → Tendsto (b n j) atTop (𝓝 (c n j))) (hδ : ∀ n, 0 < δ n) :
    ∃ M : ℕ → ℕ, ∀ n, n ≤ M n ∧ a n (M n) < δ n ∧
      ∀ j ≤ n, |b n j (M n)-c n j| < δ n := by
  have he (n : ℕ) : ∃ m, n ≤ m ∧ a n m < δ n ∧
      ∀ j ≤ n, |b n j m-c n j| < δ n := by
    have h1 := (ha n).eventually (gt_mem_nhds (hδ n))
    have h2 : ∀ᶠ m in atTop, ∀ j ∈ Finset.range (n+1), |b n j m-c n j| < δ n := by
      apply (eventually_all_finset _).mpr
      intro j hj
      simpa only [Real.dist_eq] using (hb n j (by simpa using hj)).eventually
        (Metric.ball_mem_nhds _ (hδ n))
    obtain ⟨m,hm,hma,hmb⟩ := ((eventually_ge_atTop n).and (h1.and h2)).exists
    exact ⟨m,hm,hma,fun j hj => hmb j (Finset.mem_range.mpr (by omega))⟩
  exact Classical.skolem.mp he

end BoltzmannNonuniqueness

end

end

section

/-! # Actual cap shots selected from prescribed-horizon limits -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.retime {s₀ η K α γ d₀ q T U : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (h : T = U) :
    CapApproximation s₀ η K α γ d₀ q U N := h ▸ F

theorem CapApproximation.retime_value {s₀ η K α γ d₀ q T U : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (h : T = U) :
    (F.retime h).solution.value = F.solution.value := by subst U; rfl

theorem exists_diagonal_cap_family {s₀ η K α γ d₀ q τ : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hτ : 0 < τ) (hτmax : τ ≤ 1/32)
    (A : ℕ → TightCapFamily s₀ η K α γ d₀ q)
    (htime : ∀ n, (A n).time = shrinkingHorizon τ n) (L : ∀ n, CapLocalLimit (A n)) :
    ∃ F : ShrinkingCapFamily s₀ η K α γ d₀ q, F.horizonScale = τ ∧
      ∀ n j, j ≤ n →
        |scaledBoxMass (shrinkingHorizon τ n)
          (EuclideanFlight.density q (F.approximation n).solution.value) j -
          scaledBoxMass (shrinkingHorizon τ n) (TorusKineticChart.liftDensity (L n).density) j| <
            shrinkingHorizon τ n := by
  let idx := fun n m => (L n).subsequence m
  let T := shrinkingHorizon τ
  let f := fun n m => EuclideanFlight.density q ((A n).approximation (idx n m)).solution.value
  let g := fun n => TorusKineticChart.liftDensity (L n).density
  have hpos (n) : 0 < T n := shrinkingHorizon_pos hτ n
  have ha (n) : Tendsto (fun m => DatumBounds.scale s₀ η (idx n m+1)/T n) atTop (𝓝 0) := by
    have hi := (tendsto_add_atTop_nat 1).comp (L n).strictMono.tendsto_atTop
    simpa only [zero_div,Function.comp_def,idx] using
      ((DatumBounds.scale_tendsto_zero s₀ hη).comp hi).div_const (T n)
  have hb (n j) (hj : j ≤ n) : Tendsto (fun m => scaledBoxMass (T n) (f n m) j) atTop
      (𝓝 (scaledBoxMass (T n) (g n) j)) := by
    have hw := TorusKineticChart.weak_density_transfer
      (fun m => ((A n).approximation (idx n m)).solution.measurable_value) (L n).weak_limit
    change Published.WeakL1Converges (TorusKineticChart.cellVolume (A n).time) (f n) (g n) at hw
    rw [htime n] at hw
    exact weak_scaled_setIntegral (hpos n) (measurableSet_separationBox j)
      (shrinking_separationBox_in_cell hτ hτmax hj) hw
  obtain ⟨M,hM⟩ := exists_diagonal_finite_tests ha hb hpos
  let N := fun n => idx n (M n)
  have hN (n) : n ≤ N n := (hM n).1.trans ((L n).strictMono.id_le _)
  have hr : Tendsto (fun n => DatumBounds.scale s₀ η (N n+1)/T n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (DatumBounds.scale_pos hs₀ _).le (hpos n).le)
      (fun n => (hM n).2.1.le) (shrinkingHorizon_tendsto_zero τ)
  let F : ShrinkingCapFamily s₀ η K α γ d₀ q :=
    ⟨τ,hτ,hτmax,N,hN,tendsto_atTop_mono hN tendsto_id,hr,
      fun n => ((A n).approximation (N n)).retime (htime n)⟩
  refine ⟨F,rfl,?_⟩
  intro n j hj
  change |scaledBoxMass (T n) (EuclideanFlight.density q
      (((A n).approximation (N n)).retime (htime n)).solution.value) j -
        scaledBoxMass (T n) (g n) j| < T n
  rw [CapApproximation.retime_value]
  exact (hM n).2.2 j hj

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Vanishing cap shots under agreement with the dormant solution -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_vanishing_cap_family {s₀ η K α γ d₀ q τ : ℝ}
    {B : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit B)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : 0 ≤ q) (hqmax : q < 2) (hτ : 0 < τ) (hτmax : τ ≤ 1/32)
    (A : ℕ → TightCapFamily s₀ η K α γ d₀ q)
    (htime : ∀ n, (A n).time = shrinkingHorizon τ n) (L : ∀ n, CapLocalLimit (A n))
    (he : ∀ n, (L n).density =ᵐ[(AnnularEnvelope.timePositionVolume (A n).time).prod volume]
      D.density) :
    ∃ F : ShrinkingCapFamily s₀ η K α γ d₀ q, F.horizonScale = τ ∧
      ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon τ n)
        (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0) := by
  obtain ⟨F,hF,hclose⟩ := exists_diagonal_cap_family hs₀ hη hτ hτmax A htime L
  refine ⟨F,hF,?_⟩
  intro j
  let u := fun n => scaledBoxMass (shrinkingHorizon τ n)
    (EuclideanFlight.density q (F.approximation n).solution.value) j
  let v := fun n => scaledBoxMass (shrinkingHorizon τ n) (TorusKineticChart.liftDensity D.density) j
  have hv : Tendsto v atTop (𝓝 0) := D.scaled_mass_tendsto hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq hqmax (shrinkingHorizon_pos hτ) (shrinkingHorizon_tendsto_zero τ) j
  have hdiff : Tendsto (fun n => u n-v n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (shrinkingHorizon_tendsto_zero τ)
    filter_upwards [eventually_ge_atTop j] with n hn
    have hc : kineticDilation (shrinkingHorizon τ n)⁻¹ ⁻¹' separationBox j ⊆
        TorusKineticChart.region (A n).time := by
      rw [htime n]
      exact shrinking_separationBox_in_cell hτ hτmax hn
    have hm := (L n).scaled_mass_congr D.mild.measurable (he n) (shrinkingHorizon_pos hτ n) j hc
    have hh := hclose n j hn
    rw [hm] at hh
    exact (show ‖u n-v n‖ < shrinkingHorizon τ n by simpa only [Real.norm_eq_abs] using hh).le
  simpa only [sub_add_cancel,zero_add] using hdiff.add hv

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
