import OAI.MathematicalPhysics.Boltzmann.Branching.CompactParameterConvergence
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace OAI

section

/-! # A locally integrable weakly time-constant function is constant on an interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem exists_normalized_test {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∫ t, ρ t) = 1 := by
  let c := (a+b)/2
  let β : ContDiffBump c := ⟨(b-a)/8,(b-a)/4,by linarith,by linarith⟩
  refine ⟨β.normed volume,β.contDiff_normed,β.hasCompactSupport_normed,?_,β.integral_normed⟩
  rw [β.tsupport_normed_eq]
  intro t ht
  rw [Metric.mem_closedBall,Real.dist_eq,abs_le] at ht
  dsimp [β,c] at ht
  constructor <;> linarith [ht.1,ht.2]

theorem weakly_constant_test_integral {a b : ℝ} {f ρ : ℝ → ℝ}
    (hf : LocallyIntegrable f)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioo a b) (hρi : (∫ t, ρ t) = 1)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*f t) = 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    (∫ t, φ t*f t) = (∫ t, φ t)*(∫ t, ρ t*f t) := by
  let k : ℝ → ℝ := fun t => φ t-(∫ s, φ s)*ρ t
  have hkc : HasCompactSupport k := hφc.sub (hρc.mul_left (f := fun _ => ∫ s, φ s))
  have hks : tsupport k ⊆ Ioo a b :=
    (tsupport_sub φ (fun t => (∫ s, φ s)*ρ t)).trans
      (union_subset hφs (tsupport_mul_subset_right.trans hρs))
  have hki : (∫ t, k t) = 0 := by
    change (∫ t, φ t-(∫ s, φ s)*ρ t) = 0
    rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hφc)
        ((hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul _)]
    rw [integral_const_mul,hρi,mul_one,sub_self]
  have hkd : ContDiff ℝ (⊤ : ℕ∞) k := by dsimp only [k]; fun_prop
  obtain ⟨ψ,hψ,hψc,hψs,hψd⟩ := exists_test_primitive hkd hkc hks hki
  have hz := hw ψ hψ hψc hψs
  rw [hψd] at hz
  have hiφ : Integrable (fun t => φ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have hiρ : Integrable (fun t => ρ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  have he : (∫ t, k t*f t) = (∫ t, φ t*f t)-(∫ s, φ s)*(∫ t, ρ t*f t) := by
    calc
      _ = ∫ t, φ t*f t-(∫ s, φ s)*(ρ t*f t) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun t => by dsimp only [k]; ring)
      _ = _ := by rw [integral_sub hiφ (hiρ.const_mul _),integral_const_mul]
  linarith

theorem ae_eq_const_of_weak_deriv_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*f t) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = c := by
  obtain ⟨ρ,hρ,hρc,hρs,hρi⟩ := exists_normalized_test hab
  let c := ∫ t, ρ t*f t
  have hcc : LocallyIntegrable (fun _ : ℝ => c) (volume : Measure ℝ) :=
    continuous_const.locallyIntegrable
  have hfc : LocallyIntegrableOn (fun t => f t-c) (Ioo a b) :=
    (hf.sub hcc).locallyIntegrableOn _
  have he := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc
    (fun φ hφ hφc hφs => ?_)
  · exact ⟨c,he.mono (fun t ht hmem => sub_eq_zero.mp (ht hmem))⟩
  have hiφ : Integrable (fun t => φ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have hiφc : Integrable (fun t => φ t*c) (volume : Measure ℝ) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).mul_const c
  have hh := weakly_constant_test_integral hf hρ hρc hρs hρi hw hφ hφc hφs
  change (∫ t, φ t*(f t-c)) = 0
  calc
    _ = (∫ t, φ t*f t)-(∫ t, φ t)*c := by
      simp_rw [mul_sub]
      rw [integral_sub hiφ hiφc,integral_mul_const]
    _ = 0 := by change (∫ t, φ t*f t)-(∫ t, φ t)*(∫ t, ρ t*f t) = 0; linarith

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # The characteristic primitive converges weakly at every fixed time -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.timePrimitive_slice {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {f : ℕ → ℝ × X → ℝ} {g : ℝ × X → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (t : ℝ) :
    WeakL1Converges ν (fun n x => Published.timePrimitive μ (f n) (t,x))
      (fun x => Published.timePrimitive μ g (t,x)) := by
  have hs : WeakL1Converges (ν.prod μ) (fun n p => f n p.swap) (fun p => g p.swap) := by
    apply WeakL1Converges.of_comp_measurePreserving
      (Measure.measurePreserving_swap (μ := μ) (ν := ν))
      (fun n => (hfm n).comp measurable_swap) (h.1.comp measurable_swap)
    exact h
  have hi n : Integrable (fun p : X × ℝ => f n p.swap) (ν.prod μ) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).integrable_comp_of_integrable (hfi n)
  let k : X × ℝ → ℝ := fun p => if p.2 ≤ t then 1 else 0
  have hk : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_const) measurable_const
  have hb : ∀ p, |k p| ≤ 1 := by intro p; dsimp [k]; split <;> norm_num
  have hh := hs.marginal hi hk 1 hb
  simpa only [k,Published.timePrimitive,ite_mul,one_mul,zero_mul,Prod.swap_prod_mk] using hh

theorem timePrimitive_slice_integrable {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {f : ℝ × X → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (μ.prod ν)) (t : ℝ) :
    Integrable (fun x => Published.timePrimitive μ f (t,x)) ν := by
  have h : WeakL1Converges (μ.prod ν) (fun _ : ℕ => f) f :=
    ⟨hfm,hfi,fun _ _ _ => tendsto_const_nhds⟩
  exact (h.timePrimitive_slice (fun _ => hfm) (fun _ => hfi) t).2.1

theorem WeakL1Converges.mild_slice {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {r : ℕ → ℝ × X → ℝ} {R : ℝ × X → ℝ}
    {a : ℕ → X → ℝ} {a₀ : X → ℝ}
    (ha : WeakL1Converges ν a a₀) (hai : ∀ n, Integrable (a n) ν)
    (hr : WeakL1Converges (μ.prod ν) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod ν)) (t : ℝ) :
    WeakL1Converges ν (fun n x => a n x+Published.timePrimitive μ (r n) (t,x))
      (fun x => a₀ x+Published.timePrimitive μ R (t,x)) :=
  ha.add (hr.timePrimitive_slice hrm hri t) hai
    (fun n => timePrimitive_slice_integrable (hrm n) (hri n) t)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # One weighted weak limit gives a compatible limit on all finite time windows -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

theorem weak_localize_time {f : ℕ → ℝ × X → ℝ} {g : ℝ × X → ℝ}
    (h : Published.WeakL1Converges (finiteTimeMeasure.prod ν) f g)
    {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges ((volume.restrict (Icc 0 T)).prod ν) f g := by
  have hw : Measurable (fun p : ℝ × X => windowInverseWeight T p.1) :=
    (windowInverseWeight_measurable T).comp measurable_fst
  have ht := h.withDensity_bounded hw
    (fun p => windowInverseWeight_nonneg T p.1)
    ⟨Real.exp (T^2),fun p => windowInverseWeight_bound hT p.1⟩
  rw [← prod_withDensity_left (windowInverseWeight_measurable T).ennreal_ofReal,
    finiteTimeMeasure_reweight] at ht
  exact ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
