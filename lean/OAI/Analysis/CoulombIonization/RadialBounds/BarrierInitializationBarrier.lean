import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Error
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialBoundsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
attribute [local instance] Classical.propDecidable

variable {Ω : Type*}

def initialCharge (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) : ℝ :=
  if sample ∈ A then (ball (0 : TFSpace) r).indicator (μ sample) x else 0

def initialError (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) : Ω → TFSpace → ℝ :=
  initialCharge Aᶜ r μ

lemma initialCharge_measurable [MeasurableSpace Ω] {A : Set Ω} (hA : MeasurableSet A) (r : ℝ)
    {μ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry μ)) :
    Measurable (Function.uncurry (initialCharge A r μ)) := by
  exact Measurable.ite (hA.preimage measurable_fst)
    (hm.indicator (measurableSet_ball.preimage measurable_snd)) measurable_const

lemma initialCharge_nonneg {A : Set Ω} {r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (sample : Ω) (x : TFSpace) : 0 ≤ initialCharge A r μ sample x := by
  unfold initialCharge
  split_ifs
  · exact indicator_nonneg (fun x _ => hn sample x) x
  · exact le_refl _

lemma initialCharge_le {A : Set Ω} {r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (sample : Ω) (x : TFSpace) : initialCharge A r μ sample x ≤ μ sample x := by
  unfold initialCharge
  split_ifs
  · by_cases hx : x ∈ ball (0 : TFSpace) r
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]; exact hn sample x
  · exact hn sample x

lemma initialCharge_support (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) :
    Function.support (initialCharge A r μ sample) ⊆ ball 0 r := by
  intro x hx
  by_contra h
  simp only [Function.mem_support,initialCharge,indicator_of_notMem h] at hx
  split_ifs at hx <;> exact hx rfl

lemma initialCharge_bound {A : Set Ω} {r M : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M) (sample : Ω) (x : TFSpace) :
    initialCharge A r μ sample x ≤ M := (initialCharge_le hn sample x).trans (hb sample x)

lemma initialCharge_deterministicBound {A : Set Ω} {r M : ℝ} {μ : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M) :
    DeterministicLocalBound (initialCharge A r μ) := by
  intro K _
  refine ⟨M,fun sample x _ => ?_⟩
  rw [Real.norm_of_nonneg (initialCharge_nonneg hn sample x)]
  exact initialCharge_bound hn hb sample x

lemma initialCharge_source (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) :
    4*Real.pi*initialCharge A r μ sample x = innerSource r (μ sample) (initialError A r μ sample) x := by
  simp only [innerSource,initialError,initialCharge,mem_compl_iff,mem_ball_zero_iff,
    indicator_apply]
  split_ifs <;> ring

lemma initialCharge_of_mem {A : Set Ω} {sample : Ω} (h : sample ∈ A) (r : ℝ) (μ : Ω → TFSpace → ℝ) :
    initialCharge A r μ sample = (ball (0 : TFSpace) r).indicator (μ sample) := by
  funext x
  exact ite_eq_left h

lemma initialCharge_of_notMem {A : Set Ω} {sample : Ω} (h : sample ∉ A) (r : ℝ) (μ : Ω → TFSpace → ℝ) :
    initialCharge A r μ sample = fun _ => 0 := by
  funext x
  exact ite_eq_right h

lemma initialCharge_potential (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) :
    tfPotential (initialCharge A r μ sample) x = if sample ∈ A then innerPotential r (μ sample) x else 0 := by
  by_cases h : sample ∈ A
  · rw [initialCharge_of_mem h,ite_eq_left h,innerPotential_eq_tfPotential]
  · rw [initialCharge_of_notMem h,ite_eq_right h]; simp only [tfPotential,zero_div,integral_zero]

lemma initialCharge_good {A : Set Ω} {Z r : ℝ} {μ : Ω → TFSpace → ℝ}
    (hZ : 0 ≤ Z) (hr : 0 ≤ r)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (sample : Ω) (x : TFSpace) (_hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    tfPotential (initialCharge A r μ sample) x ≤ Z/(10*r) := by
  rw [initialCharge_potential]
  split_ifs with hh
  · exact hgood sample hh x (by linarith)
  · positivity

theorem initialError_expected_mass [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {r M n : ℝ} {μ : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry μ)) (hn : ∀ sample x, 0 ≤ μ sample x)
    (hb : ∀ sample x, μ sample x ≤ M) (hi : ∀ sample, Integrable (μ sample))
    (hcount : ∀ sample, ∫ x, μ sample x ≤ n) :
    (∫ sample, (∫ x, initialError A r μ sample x) ∂P) ≤ n*P.real Aᶜ := by
  have hp := initialCharge_measurable hA.compl r hm
  have hb' := initialCharge_deterministicBound (A := Aᶜ) (r := r) hn hb
  have hs : ∀ sample x, r < ‖x‖ → initialCharge Aᶜ r μ sample x = 0 := by
    intro sample x hx
    exact truncated_density_exterior (initialCharge_support Aᶜ r μ sample) hx.le
  have hie := compactBound_integrable_prod (P := P) hp hb' hs
  have hconst : Integrable (Aᶜ.indicator (fun _ : Ω => n)) P :=
    (integrable_const n).indicator hA.compl
  have hle : ∀ sample, (∫ x, initialError A r μ sample x) ≤ Aᶜ.indicator (fun _ => n) sample := by
    intro sample
    by_cases hω : sample ∈ Aᶜ
    · rw [indicator_of_mem hω]
      apply le_trans _ (hcount sample)
      have hii : Integrable (initialError A r μ sample) :=
        bounded_support_integrable (hp.comp (measurable_const.prodMk measurable_id))
          (initialCharge_nonneg hn sample) (initialCharge_bound hn hb sample) (initialCharge_support Aᶜ r μ sample)
      exact integral_mono hii (hi sample) (initialCharge_le hn sample)
    · simp only [initialError,initialCharge,ite_eq_right hω,integral_zero,indicator_of_notMem hω,le_refl]
  calc
    _ ≤ ∫ sample, Aᶜ.indicator (fun _ : Ω => n) sample ∂P :=
      integral_mono hie.integral_prod_left hconst hle
    _ = n*P.real Aᶜ := by rw [integral_indicator hA.compl]; simp [mul_comm]

theorem initial_barrier_with_error {A : Set Ω} {Z B r a k M : ℝ}
    (hZ : 0 < Z) (hB : 0 < B) (hr : 0 < r) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    (hBsmall : B ≤ Z*r^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {μ : Ω → TFSpace → ℝ} (hm : ∀ sample, Measurable (μ sample))
    (hn : ∀ sample x, 0 ≤ μ sample x) (hb : ∀ sample x, μ sample x ≤ M)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (sample : Ω) :
    Continuous (initializedOffset Z B r a (initialCharge A r μ sample)) ∧
    WeakNuclearLowerOn univ Z (initializedBarrier Z B r a (initialCharge A r μ sample))
      (fun x => innerSource r (μ sample) (initialError A r μ sample) x+
        outerCoefficient r x*reaction k (initializedBarrier Z B r a (initialCharge A r μ sample) x)) := by
  have hm' : Measurable (initialCharge A r μ sample) := by
    by_cases hω : sample ∈ A
    · rw [initialCharge_of_mem hω]; exact (hm sample).indicator measurableSet_ball
    · rw [initialCharge_of_notMem hω]; exact measurable_const
  have hh := initialized_barrier_weak hZ hB hr ha hk hquad hreact hBsmall hsub hm'
    (initialCharge_nonneg hn sample) (initialCharge_bound hn hb sample)
    (initialCharge_support A r μ sample) (initialCharge_good hZ.le hr.le hgood sample)
  exact ⟨hh.1,hh.2.congr_source (fun x _ => by rw [initialCharge_source])⟩

end CoulombBarrier

end

end OAI
