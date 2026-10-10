import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTailRegions
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Metrizable.Basic

namespace OAI

section

/-! # Weak subsequences for the L² truncations used in weak L¹ compactness -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace.CountablyGenerated X] [SFinite μ]

theorem exists_weak_L2_subsequence (u : ℕ → Lp ℝ 2 μ) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℝ 2 μ), StrictMono φ ∧ ‖g‖ ≤ C ∧
      ∀ h : Lp ℝ 2 μ,
        Tendsto (fun n => inner ℝ (u (φ n)) h) atTop (𝓝 (inner ℝ g h)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let v : ℕ → WeakDual ℝ (Lp ℝ 2 μ) := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) (u n))
  have hv : ∀ n, v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    simpa [v,Metric.mem_closedBall,dist_zero_right] using hu n
  obtain ⟨l,hl,φ,hφ,hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ (Lp ℝ 2 μ) 0 C) hv
  let g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm l.toStrongDual
  refine ⟨φ,g,hφ,?_,?_⟩
  · simpa [g,Metric.mem_closedBall,dist_zero_right] using hl
  · intro h
    have ht := (WeakDual.eval_continuous h).continuousAt.tendsto.comp hconv
    simpa [v,g,InnerProductSpace.toDual_symm_apply,Function.comp_def] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A common weak subsequence for the countably many L² truncations -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace.CountablyGenerated X] [SFinite μ]

theorem exists_common_weak_L2_subsequence (u : ℕ → ℕ → Lp ℝ 2 μ) (C : ℕ → ℝ)
    (hu : ∀ m n, ‖u m n‖ ≤ C m) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℝ 2 μ), StrictMono φ ∧
      ∀ m, ‖g m‖ ≤ C m ∧ ∀ h : Lp ℝ 2 μ,
        Tendsto (fun n => inner ℝ (u m (φ n)) h) atTop (𝓝 (inner ℝ (g m) h)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let K (m : ℕ) : Set (WeakDual ℝ (Lp ℝ 2 μ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C m)
  have hK m : IsCompact (K m) := WeakDual.isCompact_closedBall 0 (C m)
  have : ∀ m, CompactSpace (K m) := fun m => isCompact_iff_compactSpace.mp (hK m)
  have : ∀ m, TopologicalSpace.MetrizableSpace (K m) :=
    fun m => WeakDual.metrizable_of_isCompact ℝ (Lp ℝ 2 μ) (K m) (hK m)
  let v : ℕ → ∀ m, K m := fun n m =>
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) (u m n)),by
      simpa [K,Metric.mem_closedBall,dist_zero_right] using hu m n⟩
  have hseq : IsSeqCompact (univ : Set (∀ m, K m)) := isCompact_univ.isSeqCompact
  obtain ⟨l,-,φ,hφ,hl⟩ := hseq (fun n => mem_univ (v n))
  let g : ℕ → Lp ℝ 2 μ := fun m =>
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (l m).val.toStrongDual
  refine ⟨φ,g,hφ,fun m => ⟨?_,fun h => ?_⟩⟩
  · have hnorm : ‖(l m).val.toStrongDual‖ ≤ C m := by
      have hp := (l m).property
      change dist (l m).val.toStrongDual 0 ≤ C m at hp
      simpa only [dist_zero_right] using hp
    simpa only [g,LinearIsometryEquiv.norm_map] using hnorm
  · have ht := ((WeakDual.eval_continuous h).comp
        (continuous_subtype_val.comp (continuous_apply m))).continuousAt.tendsto.comp hl
    simpa [v,g,InnerProductSpace.toDual_symm_apply,Function.comp_def] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Support and integrability of the weak limits of finite-window truncations -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def l2Restrict (S : Set X) (hS : MeasurableSet S) (g : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp g).indicator hS).toLp (S.indicator g)

theorem l2Restrict_ae (S : Set X) (hS : MeasurableSet S) (g : Lp ℝ 2 μ) :
    (l2Restrict S hS g : X → ℝ) =ᵐ[μ] S.indicator g :=
  MemLp.coeFn_toLp _

theorem weak_L2_limit_support {S : Set X} (hS : MeasurableSet S)
    {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∉ S → u n x = 0)
    (hc : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (u n) h) atTop (𝓝 (inner ℝ g h))) :
    ∀ᵐ x ∂μ, x ∉ S → g x = 0 := by
  let k := l2Restrict Sᶜ hS.compl g
  have hk : (k : X → ℝ) =ᵐ[μ] Sᶜ.indicator g := l2Restrict_ae _ _ _
  have hz n : inner ℝ (u n) k = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hs n,hk] with x hx hkx
    by_cases hxs : x ∈ S <;> simp [hkx,hxs,hx]
  have hgk : inner ℝ g k = 0 := by
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (inner ℝ g k)) := by
      simpa only [hz] using hc k
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have he : inner ℝ k k = inner ℝ g k := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk] with x hx
    by_cases hxs : x ∈ S <;> simp [hx,hxs]
  have hk0 : k = 0 := inner_self_eq_zero.mp (he.trans hgk)
  have hkzero : (k : X → ℝ) =ᵐ[μ] 0 := by
    rw [hk0]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hk,hkzero] with x hx hz
  intro hxs
  simpa [hxs] using hx.symm.trans hz

theorem L2_integrable_of_support {S : Set X} (hS : MeasurableSet S)
    (hμS : μ S < ∞) (g : Lp ℝ 2 μ)
    (hs : ∀ᵐ x ∂μ, x ∉ S → g x = 0) : Integrable g μ := by
  have : Fact (μ S < ∞) := ⟨hμS⟩
  have hgi : Integrable g (μ.restrict S) :=
    ((Lp.memLp g).restrict S).integrable (by norm_num)
  have hi := (integrable_indicator_iff hS).mpr hgi
  apply hi.congr
  filter_upwards [hs] with x hx
  by_cases hxs : x ∈ S <;> simp [hxs,hx]

theorem bounded_supported_L2 {S : Set X} (hS : MeasurableSet S) (hμS : μ S < ∞)
    {f : X → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, ‖f x‖ ≤ C) (hs : ∀ x, x ∉ S → f x = 0) :
    ∃ h : MemLp f 2 μ, ‖h.toLp f‖ ≤ ‖indicatorConstLp 2 hS hμS.ne (C : ℝ)‖ := by
  classical
  have hm : MemLp (S.indicator (fun _ : X => (C : ℝ))) 2 μ :=
    memLp_indicator_const _ hS _ (Or.inr hμS.ne)
  have hbound : ∀ x, ‖f x‖ ≤ ‖S.indicator (fun _ : X => (C : ℝ)) x‖ := by
    intro x
    by_cases hx : x ∈ S
    · simpa [hx,abs_of_nonneg C.coe_nonneg] using hb x
    · simp [hx,hs x hx]
  have h : MemLp f 2 μ := hm.of_le hf.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨h,?_⟩
  rw [Lp.norm_toLp,indicatorConstLp,Lp.norm_toLp]
  exact ENNReal.toReal_mono hm.eLpNorm_ne_top
    (eLpNorm_mono hf.aestronglyMeasurable hbound)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded tests and L¹ bounds for finite-window weak L² limits -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weak_L2_bounded_tests {S : Set X} (hS : MeasurableSet S) (hμS : μ S < ∞)
    {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∉ S → u n x = 0)
    (hc : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (u n) h) atTop (𝓝 (inner ℝ g h)))
    (ψ : X → ℝ) (hψ : Measurable ψ) (C : ℝ≥0) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun n => ∫ x, ψ x*u n x ∂μ) atTop (𝓝 (∫ x, ψ x*g x ∂μ)) := by
  classical
  have hm : MemLp (S.indicator ψ) 2 μ := by
    obtain ⟨h,-⟩ := bounded_supported_L2 hS hμS (hψ.indicator hS) C
      (fun x => by
        by_cases hx : x ∈ S
        · simpa only [indicator_of_mem hx] using hC x
        · simp [hx,C.coe_nonneg])
      (fun x hx => indicator_of_notMem hx _)
    exact h
  let k := hm.toLp (S.indicator ψ)
  have hk : (k : X → ℝ) =ᵐ[μ] S.indicator ψ := MemLp.coeFn_toLp hm
  have he (v : Lp ℝ 2 μ) (hv : ∀ᵐ x ∂μ, x ∉ S → v x = 0) :
      inner ℝ v k = ∫ x, ψ x*v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk,hv] with x hx hvx
    by_cases hxs : x ∈ S <;> simp [hx,hxs,hvx]
  have hg := weak_L2_limit_support hS hs hc
  simpa only [he _ hg,he _ (hs _)] using hc k

theorem weak_L2_L1_bound {S : Set X} (hS : MeasurableSet S) (hμS : μ S < ∞)
    {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∉ S → u n x = 0)
    (hc : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (u n) h) atTop (𝓝 (inner ℝ g h)))
    (B : ℝ) (hB : ∀ n, ∫ x, |u n x| ∂μ ≤ B) :
    Integrable g μ ∧ ∫ x, |g x| ∂μ ≤ B := by
  classical
  have hg := weak_L2_limit_support hS hs hc
  have hgi := L2_integrable_of_support hS hμS g hg
  let ψ : X → ℝ := fun x => if 0 ≤ g x then 1 else -1
  have hψ : Measurable ψ := Measurable.ite
    (measurableSet_le measurable_const (Lp.stronglyMeasurable g).measurable)
    measurable_const measurable_const
  have hψb : ∀ x, ‖ψ x‖ ≤ (1 : ℝ≥0) := by
    intro x
    dsimp [ψ]
    split_ifs <;> norm_num
  have he : (fun x => ψ x*g x) = fun x => |g x| := by
    funext x
    by_cases hx : 0 ≤ g x <;> simp [ψ,hx,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
  refine ⟨hgi,?_⟩
  have ht := weak_L2_bounded_tests hS hμS hs hc ψ hψ 1 hψb
  rw [he] at ht
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  apply le_trans _ (hB n)
  have hui := L2_integrable_of_support hS hμS (u n) (hs n)
  apply integral_mono (hui.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψb)) hui.abs
  intro x
  calc
    ψ x*u n x ≤ |ψ x*u n x| := le_abs_self _
    _ = |ψ x| * |u n x| := abs_mul _ _
    _ ≤ 1 * |u n x| := mul_le_mul_of_nonneg_right (hψb x) (abs_nonneg _)
    _ = |u n x| := one_mul _

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Published weak compactness input for the two kinetic measure spaces

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Transactions of the AMS 47 (1940), 323–392, Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.
Publisher: https://www.ams.org/journals/tran/1940-047-03/S0002-9947-1940-0002020-4/S0002-9947-1940-0002020-4.pdf

The hypothesis below is the sequential weak-compactness consequence for the
one- and two-velocity spaces used here. `UniformIntegrable` includes the common
L¹ bound; `UnifTight` supplies the necessary control at infinity. We require
both, including on the infinite velocity spaces. No Boltzmann equation,
nonlinear identification, or admissible solution is assumed by this input.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

def WeakL1Converges (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Measurable g ∧ Integrable g μ ∧
    ∀ ψ : X → ℝ, Measurable ψ → (∃ C : ℝ, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x*f n x ∂μ) atTop (𝓝 (∫ x, ψ x*g x ∂μ))

def L1WeakCompactnessInput (μ : Measure X) : Prop :=
  ∀ f : ℕ → X → ℝ, (∀ n, Measurable (f n)) →
    UniformIntegrable f 1 μ → UnifTight f 1 μ →
    ∃ (φ : ℕ → ℕ) (g : X → ℝ), StrictMono φ ∧
      WeakL1Converges μ (fun n => f (φ n)) g

/-- Only the two kinetic measure spaces needed in the limit construction. -/
def DunfordPettis1940Theorem321 : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    L1WeakCompactnessInput ((AnnularEnvelope.timePositionVolume T).prod
      (volume : Measure BoltzmannNonuniqueness.Velocity)) ∧
    L1WeakCompactnessInput ((AnnularEnvelope.timePositionVolume T).prod
      (volume : Measure (BoltzmannNonuniqueness.Velocity × BoltzmannNonuniqueness.Velocity)))

theorem WeakL1Converges.comp {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    WeakL1Converges μ (fun n => f (φ n)) g :=
  ⟨h.1,h.2.1,fun ψ hψ hB => (h.2.2 ψ hψ hB).comp hφ⟩

theorem WeakL1Converges.nonneg {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    ∀ᵐ x ∂μ, 0 ≤ g x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg h.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hψB : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have ht := h.2.2 ψ hψ hψB
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  simp_rw [he] at ht
  apply ge_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak limits are unchanged by a vanishing L1 error -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.of_integral_abs_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f h : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hh : ∀ n, Integrable (h n) μ)
    (herr : Tendsto (fun n => ∫ x, |h n x-f n x| ∂μ) atTop (𝓝 0)) :
    WeakL1Converges μ h g := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hC' (x) : |ψ x| ≤ |C| := (hC x).trans (le_abs_self C)
  have hi (n) : Integrable (fun x => ψ x*(h n x-f n x)) μ :=
    ((hh n).sub (hf n)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC')
  have he : Tendsto (fun n => ∫ x, ψ x*(h n x-f n x) ∂μ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_integral_le_of_norm_le (((hh n).sub (hf n)).abs.const_mul |C|)
        (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs,abs_mul]
          exact mul_le_mul_of_nonneg_right (hC' x) (abs_nonneg _))))
    simpa only [integral_const_mul,mul_zero,Pi.sub_apply] using herr.const_mul |C|
  have ht := he.add (hg.2.2 ψ hψ ⟨C,hC⟩)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [← integral_add (hi n) ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC'))]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A vanishing L1 norm error preserves the same weak limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.of_eLpNorm_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f h : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hh : ∀ n, Integrable (h n) μ)
    (herr : Tendsto (fun n => eLpNorm (fun x => h n x-f n x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ h g := by
  apply hg.of_integral_abs_sub hf hh
  have he n : (∫ x, |h n x-f n x| ∂μ) =
      (eLpNorm (fun x => h n x-f n x) 1 μ).toReal := by
    change (∫ x, ‖(h n-f n) x‖ ∂μ) = (eLpNorm (h n-f n) 1 μ).toReal
    rw [eLpNorm_one_eq_lintegral_enorm ((hh n).sub (hf n)).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm ((hh n).sub (hf n)).aestronglyMeasurable]
  simp only [he]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herr

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak velocity-average limits and their identification with strong limits -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem integral_test_marginal {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {u k : X × Y → ℝ} (hu : Integrable u (μ.prod ν))
    (hk : Measurable k) (C : ℝ) (hC : ∀ z, |k z| ≤ C)
    {ψ : X → ℝ} (hψ : Measurable ψ) (D : ℝ) (hD : ∀ x, |ψ x| ≤ D) :
    (∫ x, ψ x*(∫ y, k (x,y)*u (x,y) ∂ν) ∂μ) =
      ∫ z, (ψ z.1*k z)*u z ∂μ.prod ν := by
  have hku := hu.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)
  have hi := hku.bdd_mul (hψ.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hD z.1))
  change Integrable (fun z : X × Y => ψ z.1*(k z*u z)) (μ.prod ν) at hi
  calc
    _ = ∫ z, ψ z.1*(k z*u z) ∂μ.prod ν := by
      rw [integral_prod _ hi]
      simp_rw [integral_const_mul]
    _ = _ := by congr 1; ext z; ring

theorem WeakL1Converges.marginal {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hf : ∀ n, Integrable (f n) (μ.prod ν))
    {k : X × Y → ℝ} (hk : Measurable k) (C : ℝ) (hC : ∀ z, |k z| ≤ C) :
    WeakL1Converges μ (fun n x => ∫ y, k (x,y)*f n (x,y) ∂ν)
      (fun x => ∫ y, k (x,y)*g (x,y) ∂ν) := by
  have hkg := h.2.1.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hk.mul h.1).stronglyMeasurable.integral_prod_right'.measurable,
    hkg.integral_prod_left,?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have htest : Measurable (fun z : X × Y => ψ z.1*k z) :=
    (hψ.comp measurable_fst).mul hk
  have htestB : ∃ B : ℝ, ∀ z : X × Y, |ψ z.1*k z| ≤ B := by
    refine ⟨|D| * |C|,fun z => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hD z.1).trans (le_abs_self D)) ((hC z).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have ht := h.2.2 _ htest htestB
  simpa only [← integral_test_marginal (hf _) hk C hC hψ D hD,
    ← integral_test_marginal h.2.1 hk C hC hψ D hD] using ht

theorem WeakL1Converges.eq_of_strong {μ : Measure X} {f : ℕ → X → ℝ} {g A : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ) (hA : Integrable A μ)
    (hstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 μ) atTop (𝓝 0)) :
    A =ᵐ[μ] g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq A g hA h.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hB : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have hw := h.2.2 ψ hψ hB
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  simp_rw [he] at hw
  have hsstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 (μ.restrict s))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ha := tendsto_integral_of_L1' A (Eventually.of_forall (fun n => (hf n).restrict)) hsstrong
  exact tendsto_nhds_unique ha hw

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A common weak subsequence for countably many local measures -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem L1WeakCompactnessInput.countable (μ : ℕ → Measure X)
    (hc : ∀ j, L1WeakCompactnessInput (μ j)) {f : ℕ → X → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hui : ∀ j, UniformIntegrable f 1 (μ j)) (htight : ∀ j, UnifTight f 1 (μ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → X → ℝ), StrictMono φ ∧
      ∀ j, WeakL1Converges (μ j) (fun n => f (φ n)) (g j) := by
  have hex (j : ℕ) (a : ℕ → ℕ) := hc j (fun n => f (a n))
    (fun n => hfm (a n)) (Compactness.uniformIntegrable_comp (hui j) a) ((htight j).comp a)
  choose σ g hσ hg using hex
  let a : ℕ → ℕ → ℕ := fun n => Nat.rec id (fun j aj => aj ∘ σ j aj) n
  have has (j : ℕ) : a (j+1) = a j ∘ σ j (a j) := rfl
  have ha (j : ℕ) : StrictMono (a j) := by
    induction j with
    | zero => exact strictMono_id
    | succ j hj => rw [has]; exact hj.comp (hσ j (a j))
  have hnest (i j : ℕ) (hij : i ≤ j) : ∀ k, ∃ m, k ≤ m ∧ a i m = a j k := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact fun k => ⟨k,le_rfl,rfl⟩
    | succ j ih =>
      by_cases hi : i ≤ j
      · intro k
        obtain ⟨m,hm,he⟩ := ih hi (σ j (a j) k)
        exact ⟨m,((hσ j (a j)).id_le k).trans hm,he⟩
      · have he : i = j+1 := by omega
        subst i
        exact fun k => ⟨k,le_rfl,rfl⟩
  let φ : ℕ → ℕ := fun n => a (n+1) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change a (n+1) n < a (n+2) (n+1)
    rw [has (n+1)]
    exact (ha (n+1)) ((Nat.lt_succ_self n).trans_le ((hσ (n+1) (a (n+1))).id_le (n+1)))
  refine ⟨φ,fun j => g j (a j),hφ,?_⟩
  intro j
  have hj : WeakL1Converges (μ j) (fun n => f (a (j+1) n)) (g j (a j)) := hg j (a j)
  let ρ : ℕ → ℕ := fun n => if hn : j+1 ≤ n+1 then (hnest (j+1) (n+1) hn n).choose else n
  have hρ (n : ℕ) : n ≤ ρ n := by
    dsimp only [ρ]
    split_ifs with hn
    · exact (hnest (j+1) (n+1) hn n).choose_spec.1
    · exact le_rfl
  have hρtop : Tendsto ρ atTop atTop := tendsto_atTop_mono hρ tendsto_id
  have he : ∀ᶠ n in atTop, a (j+1) (ρ n) = φ n := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have hn' : j+1 ≤ n+1 := by omega
    dsimp only [ρ]
    rw [dite_eq_left hn']
    exact (hnest (j+1) (n+1) hn' n).choose_spec.2
  refine ⟨hj.1,hj.2.1,?_⟩
  intro ψ hψ hB
  apply ((hj.2.2 ψ hψ hB).comp hρtop).congr'
  filter_upwards [he] with n hn
  simp only [Function.comp_apply,hn]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded multipliers and uniqueness for weak L¹ limits -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.bounded_mul {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {a : X → ℝ} (ha : Measurable a)
    (C : ℝ) (hC : ∀ x, |a x| ≤ C) :
    WeakL1Converges μ (fun n x => a x*f n x) (fun x => a x*g x) := by
  refine ⟨ha.mul h.1,h.2.1.bdd_mul ha.aestronglyMeasurable (ae_of_all _ hC),?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have hm := hψ.mul ha
  have hb : ∃ B : ℝ, ∀ x, |ψ x*a x| ≤ B := by
    refine ⟨|D| * |C|,fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hD x).trans (le_abs_self D)) ((hC x).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  simpa only [mul_assoc] using h.2.2 (fun x => ψ x*a x) hm hb

theorem WeakL1Converges.unique {μ : Measure X} {f : ℕ → X → ℝ} {g h : X → ℝ}
    (hg : WeakL1Converges μ f g) (hh : WeakL1Converges μ f h) : g =ᵐ[μ] h := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq g h hg.2.1 hh.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hb : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have h1 := hg.2.2 ψ hψ hb
  have h2 := hh.2.2 ψ hψ hb
  simp_rw [he] at h1 h2
  exact tendsto_nhds_unique h1 h2

theorem WeakL1Converges.congr_limit {μ : Measure X} {f : ℕ → X → ℝ} {g h : X → ℝ}
    (hg : WeakL1Converges μ f g) (hh : Measurable h) (he : g =ᵐ[μ] h) :
    WeakL1Converges μ f h := by
  refine ⟨hh,hg.2.1.congr he,?_⟩
  intro ψ hψ hB
  have ht := hg.2.2 ψ hψ hB
  have hi : (∫ x, ψ x*g x ∂μ) = ∫ x, ψ x*h x ∂μ :=
    integral_congr_ae (he.mono (fun x hx => congrArg (fun y => ψ x*y) hx))
  rw [hi] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Linear operations on weak L¹ limits -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.sub {μ : Measure X} {f k : ℕ → X → ℝ} {g h : X → ℝ}
    (hf : WeakL1Converges μ f g) (hk : WeakL1Converges μ k h)
    (hfi : ∀ n, Integrable (f n) μ) (hki : ∀ n, Integrable (k n) μ) :
    WeakL1Converges μ (fun n x => f n x-k n x) (fun x => g x-h x) := by
  refine ⟨hf.1.sub hk.1,hf.2.1.sub hk.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hm (u : X → ℝ) (hu : Integrable u μ) : Integrable (fun x => ψ x*u x) μ :=
    hu.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he (u v : X → ℝ) (hu : Integrable u μ) (hv : Integrable v μ) :
      (∫ x, ψ x*(u x-v x) ∂μ) = (∫ x, ψ x*u x ∂μ)-(∫ x, ψ x*v x ∂μ) := by
    simp_rw [mul_sub]
    exact integral_sub (hm u hu) (hm v hv)
  simp_rw [he _ _ (hfi _) (hki _),he _ _ hf.2.1 hk.2.1]
  exact (hf.2.2 ψ hψ ⟨C,hC⟩).sub (hk.2.2 ψ hψ ⟨C,hC⟩)

theorem WeakL1Converges.congr_sequence {μ : Measure X} {f k : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (he : ∀ n, f n =ᵐ[μ] k n) :
    WeakL1Converges μ k g := by
  refine ⟨h.1,h.2.1,?_⟩
  intro ψ hψ hB
  have ht := h.2.2 ψ hψ hB
  have hi n : (∫ x, ψ x*f n x ∂μ) = ∫ x, ψ x*k n x ∂μ :=
    integral_congr_ae ((he n).mono (fun x hx => congrArg (fun y => ψ x*y) hx))
  simpa only [hi] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Removing a diverging cutoff from a nonnegative weak L¹ sequence -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

private theorem indicator_test_integral {μ : Measure X} (s : Set X) (u : X → ℝ) :
    (∫ x, s.indicator (fun _ => (1 : ℝ)) x*u x ∂μ) = ∫ x, s.indicator u x ∂μ := by
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem WeakL1Converges.moving_tail {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n x, 0 ≤ f n x) {r : X → ℝ} (hr : Measurable r)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun n => ∫ x, {x | b n ≤ r x}.indicator (f n) x ∂μ) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun m => {x | (m : ℝ) ≤ r x}
  have hs m : MeasurableSet (s m) := measurableSet_le measurable_const hr
  have hgTail : Tendsto (fun m => ∫ x, (s m).indicator g x ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ : X => (0 : ℝ)) (fun x => ‖g x‖)
      (fun m => (h.2.1.aestronglyMeasurable.indicator (hs m))) h.2.1.norm
      (fun m => ae_of_all _ (fun x => by
        by_cases hx : x ∈ s m <;> simp [hx]))
      (ae_of_all _ (fun x => by
        obtain ⟨N,hN⟩ := exists_nat_gt (r x)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with m hm
        have hx : x ∉ s m := not_le.mpr (hN.trans_le (by exact_mod_cast hm))
        simp [hx]))
    simpa using ht
  have hfixed (m : ℕ) : Tendsto (fun n => ∫ x, (s m).indicator (f n) x ∂μ)
      atTop (𝓝 (∫ x, (s m).indicator g x ∂μ)) := by
    have ht := h.2.2 ((s m).indicator (fun _ => 1)) (measurable_const.indicator (hs m))
      ⟨1,fun x => by by_cases hx : x ∈ s m <;> simp [hx]⟩
    simpa only [indicator_test_integral] using ht
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg
      (fun x => indicator_nonneg (fun x _ => hfn n x) x)))
  · intro ε hε
    obtain ⟨m,hm⟩ := (hgTail.eventually (gt_mem_nhds hε)).exists
    have hsmall := (hfixed m).eventually (gt_mem_nhds hm)
    filter_upwards [hsmall, hb.eventually (eventually_ge_atTop (m : ℝ))] with n hn hbn
    refine lt_of_le_of_lt ?_ hn
    apply integral_mono ((hf n).indicator (measurableSet_le measurable_const hr))
      ((hf n).indicator (hs m))
    intro x
    by_cases hx : b n ≤ r x
    · have hy : x ∈ s m := hbn.trans hx
      simp [hx,hy]
    · rw [indicator_of_notMem (show x ∉ {x | b n ≤ r x} from hx)]
      exact indicator_nonneg (fun x _ => hfn n x) x

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Combining weak limits of time slices on finite windows -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.prod_of_fibers
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {f : ℕ → T × X → ℝ} {g : T × X → ℝ}
    (hf : ∀ n, Integrable (f n) (ν.prod μ)) (hgm : Measurable g) (hgi : Integrable g (ν.prod μ))
    {C : ℝ} (hbound : ∀ᶠ n in atTop, ∀ᵐ z ∂ν.prod μ, |f n z| ≤ C)
    (hlim : ∀ᵐ t ∂ν, WeakL1Converges μ (fun n x => f n (t,x)) (fun x => g (t,x))) :
    WeakL1Converges (ν.prod μ) f g := by
  refine ⟨hgm,hgi,?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have hD' (z) : |ψ z| ≤ |D| := (hD z).trans (le_abs_self D)
  have hi (n) := (hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hD')
  have hli := hgi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hD')
  have htest := tendsto_integral_filter_of_norm_le_const
    (μ := ν) (l := (atTop : Filter ℕ)) (F := fun n t => ∫ x, ψ (t,x)*f n (t,x) ∂μ)
    (f := fun t => ∫ x, ψ (t,x)*g (t,x) ∂μ)
    (Eventually.of_forall (fun n => (hi n).integral_prod_left.aestronglyMeasurable))
    ?_ ?_
  · have heq (n) := integral_prod (fun z => ψ z*f n z) (hi n)
    have hgeq := integral_prod (fun z => ψ z*g z) hli
    simpa only [← heq,← hgeq] using htest
  · refine ⟨(|D| * C)*μ.real Set.univ,?_⟩
    filter_upwards [hbound] with n hn
    filter_upwards [Measure.ae_ae_of_ae_prod hn] with t ht
    have h := norm_integral_le_of_norm_le (f := fun x => ψ (t,x)*f n (t,x)) (integrable_const (μ := μ) (|D| * C)) ?_
    · simpa only [integral_const,smul_eq_mul,mul_comm] using h
    · filter_upwards [ht] with x hx
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hD' (t,x)) hx (abs_nonneg _) (abs_nonneg D)
  · filter_upwards [hlim] with t ht
    exact ht.2.2 (fun x => ψ (t,x)) (hψ.comp (measurable_const.prodMk measurable_id))
      ⟨D,fun x => hD (t,x)⟩

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A nonnegative weakly vanishing sequence vanishes in L1 -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.nonnegative_zero_L1 {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hg : g =ᵐ[μ] 0)
    (hi : ∀ᶠ n in atTop, Integrable (f n) μ)
    (hn : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  have ht := h.2.2 (fun _ => 1) measurable_const ⟨1,fun _ => by norm_num⟩
  have hz : (∫ x, g x ∂μ) = 0 := by
    simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hg
  simp only [one_mul,hz] at ht
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [ENNReal.ofReal_zero] at hh
  apply hh.congr'
  filter_upwards [hi,hn] with n hni hnn
  dsimp only [Function.comp_def]
  rw [eLpNorm_one_eq_lintegral_enorm hni.aestronglyMeasurable,
    ofReal_integral_eq_lintegral_ofReal hni hnn]
  apply lintegral_congr_ae
  filter_upwards [hnn] with x hx
  exact (Real.enorm_eq_ofReal hx).symm

theorem WeakL1Converges.nonnegative_zero_inMeasure {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hg : g =ᵐ[μ] 0)
    (hi : ∀ᶠ n in atTop, Integrable (f n) μ)
    (hn : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    TendstoInMeasure μ f atTop 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  simpa only [sub_zero] using h.nonnegative_zero_L1 hg hi hn

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Localizing weak L¹ convergence on measurable sets -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.restrict {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {s : Set X} (hs : MeasurableSet s) :
    WeakL1Converges (μ.restrict s) f g := by
  refine ⟨h.1,h.2.1.restrict,?_⟩
  intro ψ hψ hB
  have hm : Measurable (s.indicator ψ) := hψ.indicator hs
  obtain ⟨C,hC⟩ := hB
  have hb : ∃ D : ℝ, ∀ x, |s.indicator ψ x| ≤ D := by
    refine ⟨max C 0,fun x => ?_⟩
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using (hC x).trans (le_max_left C 0)
    · simp only [indicator_of_notMem hx,abs_zero]
      exact le_max_right C 0
  have ht := h.2.2 _ hm hb
  have he (u : X → ℝ) : (∫ x, s.indicator ψ x*u x ∂μ) = ∫ x in s, ψ x*u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [he] using ht

theorem WeakL1Converges.restrict_base {Y : Type*} [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) {s : Set X} (hs : MeasurableSet s) :
    WeakL1Converges ((μ.restrict s).prod ν) f g := by
  have ht := h.restrict (hs.prod MeasurableSet.univ)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A vanishing scalar times a nonnegative weakly convergent density -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.vanishing_scalar
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (h : WeakL1Converges μ f g)
    (hf : ∀ᶠ n in atTop, Integrable (f n) μ)
    (hfn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => c n*f n x) 1 μ) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
    simpa only [one_mul] using h.2.2 (fun _ => 1) measurable_const
      ⟨1,fun _ => by norm_num⟩
  have he : ∀ᶠ n in atTop,
      eLpNorm (fun x => c n*f n x) 1 μ =
        ENNReal.ofReal (|c n| *(∫ x, f n x ∂μ)) := by
    filter_upwards [hf] with n hn
    rw [eLpNorm_one_eq_lintegral_enorm (hn.const_mul _).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hn.const_mul _)]
    congr 1
    calc
      (∫ x, ‖c n*f n x‖ ∂μ) = ∫ x, |c n| *f n x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfn n] with x hx
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx]
      _ = _ := integral_const_mul _ _
  apply Tendsto.congr' (he.mono (fun _ hn => hn.symm))
  simpa only [Function.comp_def,abs_zero,zero_mul,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hc.abs.mul hi)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded changes of measure for weak L1 limits -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.withDensity_bounded {μ : Measure X}
    {f : ℕ → X → ℝ} {g w : X → ℝ} (h : WeakL1Converges μ f g)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwB : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    WeakL1Converges (μ.withDensity (fun x => ENNReal.ofReal (w x))) f g := by
  obtain ⟨B,hB⟩ := hwB
  have hi : Integrable (fun x => w x*g x) μ :=
    h.2.1.bdd_mul hw.aestronglyMeasurable (ae_of_all _ hB)
  refine ⟨h.1,?_,?_⟩
  · apply (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (hw0 _),smul_eq_mul] using hi
  · intro ψ hψ hψB
    obtain ⟨C,hC⟩ := hψB
    have hb : ∃ D : ℝ, ∀ x, |w x*ψ x| ≤ D := by
      refine ⟨max B 0 * max C 0,fun x => ?_⟩
      rw [abs_mul]
      exact mul_le_mul ((hB x).trans (le_max_left _ _))
        ((hC x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    have ht := h.2.2 (fun x => w x*ψ x) (hw.mul hψ) hb
    have he (u : X → ℝ) :
        (∫ x, ψ x*u x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
          ∫ x, (w x*ψ x)*u x ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (hw0 _),smul_eq_mul,mul_assoc]
    simpa only [he] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Transfer of weak L¹ convergence through a measure-preserving chart -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integral_comp_measurePreserving {μ : Measure X} {ν : Measure Y}
    {φ : X → Y} (hφ : MeasurePreserving φ μ ν) {f : Y → ℝ} (hf : Measurable f) :
    (∫ x, f (φ x) ∂μ) = ∫ y, f y ∂ν := by
  have h := integral_map (μ := μ) hφ.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hφ.map_eq] at h
  exact h.symm

theorem WeakL1Converges.of_comp_measurePreserving {μ : Measure X} {ν : Measure Y}
    {φ : X → Y} (hφ : MeasurePreserving φ μ ν) {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (h : WeakL1Converges μ (fun n => f n ∘ φ) (g ∘ φ)) :
    WeakL1Converges ν f g := by
  refine ⟨hg,(hφ.integrable_comp hg.aestronglyMeasurable).mp h.2.1,?_⟩
  intro ψ hψ hB
  have ht := h.2.2 (ψ ∘ φ) (hψ.comp hφ.measurable)
    (by obtain ⟨C,hC⟩ := hB; exact ⟨C,fun x => hC (φ x)⟩)
  have he (u : Y → ℝ) (hu : Measurable u) :
      (∫ x, (ψ ∘ φ) x*(u ∘ φ) x ∂μ) = ∫ y, ψ y*u y ∂ν :=
    integral_comp_measurePreserving hφ (hψ.mul hu)
  simp_rw [he _ (hf _)] at ht
  rw [he _ hg] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Marginals and uniqueness need integrability only along a sequence tail -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem WeakL1Converges.marginal_eventually {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g)
    (hf : ∀ᶠ n in atTop, Integrable (f n) (μ.prod ν))
    {k : X × Y → ℝ} (hk : Measurable k) (C : ℝ) (hC : ∀ z, |k z| ≤ C) :
    WeakL1Converges μ (fun n x => ∫ y, k (x,y)*f n (x,y) ∂ν)
      (fun x => ∫ y, k (x,y)*g (x,y) ∂ν) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hf
  have ht := (h.comp (tendsto_add_atTop_nat N)).marginal
    (fun n => hN (n+N) (Nat.le_add_left N n)) hk C hC
  exact ⟨ht.1,ht.2.1,fun ψ hψ hB => (tendsto_add_atTop_iff_nat N).mp (ht.2.2 ψ hψ hB)⟩

theorem WeakL1Converges.eq_of_strong_eventually {μ : Measure X}
    {f : ℕ → X → ℝ} {g A : X → ℝ} (h : WeakL1Converges μ f g)
    (hf : ∀ᶠ n in atTop, Integrable (f n) μ) (hA : Integrable A μ)
    (hstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 μ) atTop (𝓝 0)) :
    A =ᵐ[μ] g := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hf
  exact (h.comp (tendsto_add_atTop_nat N)).eq_of_strong
    (fun n => hN (n+N) (Nat.le_add_left N n)) hA
    (hstrong.comp (tendsto_add_atTop_nat N))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Extending a weak L¹ sequence by a finite angular measure -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem WeakL1Converges.prod_constant {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [IsFiniteMeasure ν] {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ) :
    WeakL1Converges (μ.prod ν) (fun n z => f n z.1) (fun z => g z.1) := by
  refine ⟨h.1.comp measurable_fst,h.2.1.comp_fst ν,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hbound : ∀ x, |∫ y, ψ (x,y) ∂ν| ≤ max C 0*ν.real Set.univ := by
    intro x
    have hi : Integrable (fun _ : Y => max C 0) ν := integrable_const _
    have hb := norm_integral_le_of_norm_le hi (ae_of_all _ (fun y =>
      (show ‖ψ (x,y)‖ ≤ C from hC (x,y)).trans (le_max_left C 0)))
    simpa only [integral_const,smul_eq_mul,Real.norm_eq_abs,mul_comm] using hb
  have ht := h.2.2 (fun x => ∫ y, ψ (x,y) ∂ν)
    hψ.stronglyMeasurable.integral_prod_right'.measurable ⟨_,hbound⟩
  have he (u : X → ℝ) (hu : Integrable u μ) :
      (∫ z, ψ z*u z.1 ∂μ.prod ν) = ∫ x, (∫ y, ψ (x,y) ∂ν)*u x ∂μ := by
    have hi := (hu.comp_fst ν).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
    rw [integral_prod _ hi]
    simp_rw [integral_mul_const]
  simpa only [he _ (hf _),he _ h.2.1] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The time primitive is weakly continuous on a finite time interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

def timeExchange : ((ℝ × P) × ℝ) ≃ᵐ ((ℝ × P) × ℝ) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

theorem timeExchange_apply (z : (ℝ × P) × ℝ) :
    timeExchange z = ((z.2,z.1.2),z.1.1) := rfl

theorem timeExchange_involutive (z : (ℝ × P) × ℝ) : timeExchange (timeExchange z) = z := rfl

theorem timeExchange_measurePreserving (μ : Measure ℝ) (ν : Measure P) [SFinite μ] [SFinite ν] :
    MeasurePreserving (timeExchange (P := P)) ((μ.prod ν).prod μ) ((μ.prod ν).prod μ) := by
  exact (measurePreserving_prodAssoc μ ν μ).symm.comp
    (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := μ) (ν := ν))).comp
      (Measure.measurePreserving_swap (μ := μ.prod ν) (ν := μ)))

def timePrimitive (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  ∫ s, if s ≤ z.1 then f (s,z.2) else 0 ∂μ

theorem WeakL1Converges.timePrimitive {μ : Measure ℝ} {ν : Measure P}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) :
    WeakL1Converges (μ.prod ν) (fun n => timePrimitive μ (f n)) (timePrimitive μ g) := by
  have hex := h.prod_constant (ν := μ) hfi
  have htrans : WeakL1Converges ((μ.prod ν).prod μ)
      (fun n z => f n (z.2,z.1.2)) (fun z => g (z.2,z.1.2)) := by
    apply WeakL1Converges.of_comp_measurePreserving (timeExchange_measurePreserving μ ν)
      (fun n => (hfm n).comp (measurable_snd.prodMk measurable_fst.snd))
      (h.1.comp (measurable_snd.prodMk measurable_fst.snd))
    exact hex
  have hint n : Integrable (fun z : (ℝ × P) × ℝ => f n (z.2,z.1.2)) ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable ((hfi n).comp_fst μ)
  let k : (ℝ × P) × ℝ → ℝ := fun z => if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb : ∀ z, |k z| ≤ 1 := by intro z; dsimp [k]; split <;> norm_num
  have ht := htrans.marginal hint hkm 1 hkb
  have he (u : ℝ × P → ℝ) :
      (fun z : ℝ × P => ∫ s, k (z,s)*u (s,z.2) ∂μ) = Published.timePrimitive μ u := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [k,Published.timePrimitive]
    split <;> simp
  have hseq : (fun n z => ∫ s, k (z,s)*f n (s,z.2) ∂μ) =
      (fun n => Published.timePrimitive μ (f n)) := funext (fun n => he (f n))
  rw [hseq,he g] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Restricting a kinetic weak limit to any earlier time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem timePositionVolume_restrict {t T : ℝ} (ht : t ≤ T) :
    (AnnularEnvelope.timePositionVolume T).restrict (Icc 0 t ×ˢ (univ : Set Position)) =
      AnnularEnvelope.timePositionVolume t := by
  rw [AnnularEnvelope.timePositionVolume,← Measure.prod_restrict,Measure.restrict_univ,
    Measure.restrict_restrict_of_subset (Icc_subset_Icc le_rfl ht)]
  rfl

theorem timePositionVolume_mono {t T : ℝ} (ht : t ≤ T) :
    AnnularEnvelope.timePositionVolume t ≤ AnnularEnvelope.timePositionVolume T := by
  rw [AnnularEnvelope.timePositionVolume,AnnularEnvelope.timePositionVolume]
  exact Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl ht) le_rfl) le_rfl

namespace Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.restrict_time {ν : Measure X} [SFinite ν] {t T : ℝ}
    {f : ℕ → (ℝ × Position) × X → ℝ} {g : (ℝ × Position) × X → ℝ}
    (h : WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod ν) f g) (ht : t ≤ T) :
    WeakL1Converges ((AnnularEnvelope.timePositionVolume t).prod ν) f g := by
  have hs := h.restrict_base (s := Icc 0 t ×ˢ (univ : Set Position)) (measurableSet_Icc.prod (MeasurableSet.univ : MeasurableSet (univ : Set Position)))
  rw [timePositionVolume_restrict ht] at hs
  exact hs

end Published
end BoltzmannNonuniqueness

end

end

section

/-! # Fixed majorants pass to weak L¹ limits -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.le {μ : Measure X} {f : ℕ → X → ℝ} {g u : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hum : Measurable u) (hui : Integrable u μ)
    (hle : ∀ n, f n ≤ᵐ[μ] u) : g ≤ᵐ[μ] u := by
  have hu : WeakL1Converges μ (fun _ : ℕ => u) u :=
    ⟨hum,hui,fun _ _ _ => tendsto_const_nhds⟩
  have hn := (hu.sub h (fun _ => hui) hfi).nonneg
    (fun n => (hle n).mono (fun x hx => sub_nonneg.mpr hx))
  exact hn.mono (fun x hx => sub_nonneg.mp hx)

theorem WeakL1Converges.le_on {μ : Measure X} {f : ℕ → X → ℝ} {g u : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    {s : Set X} (hs : MeasurableSet s) (hum : Measurable u) (hui : IntegrableOn u s μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, x ∈ s → f n x ≤ u x) :
    ∀ᵐ x ∂μ, x ∈ s → g x ≤ u x := by
  have hr : ∀ n, f n ≤ᵐ[μ.restrict s] u := by
    intro n
    exact (ae_restrict_iff' hs).mpr (hle n)
  exact (ae_restrict_iff' hs).mp ((h.restrict hs).le (fun n => (hfi n).restrict) hum hui hr)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # An eventual fixed lower bound passes to a weak L¹ limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.ge_eventually {μ : Measure X} {f : ℕ → X → ℝ} {g u : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hum : Measurable u) (hun : ∀ x, 0 ≤ u x)
    (hle : ∀ᶠ n in atTop, u ≤ᵐ[μ] f n) : u ≤ᵐ[μ] g := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hle
  have hui : Integrable u μ := (hfi N).mono' hum.aestronglyMeasurable
    ((hN N le_rfl).mono (fun x hx => by
      rw [Real.norm_of_nonneg (hun x)]
      exact hx))
  have ht := h.comp (Filter.tendsto_add_atTop_nat N)
  have hu : WeakL1Converges μ (fun _ : ℕ => u) u :=
    ⟨hum,hui,fun _ _ _ => tendsto_const_nhds⟩
  have hh := (ht.sub hu (fun n => hfi (n+N)) (fun _ => hui)).nonneg
    (fun n => (hN (n+N) (Nat.le_add_left _ _)).mono (fun x hx => sub_nonneg.mpr hx))
  exact hh.mono (fun x hx => sub_nonneg.mp hx)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak L1 convergence extended by zero from a fixed measurable window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.zeroExtension {μ : Measure X} {s : Set X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hs : MeasurableSet s)
    (h : WeakL1Converges (μ.restrict s) f g) :
    WeakL1Converges μ (fun n => s.indicator (f n)) (s.indicator g) := by
  refine ⟨h.1.indicator hs,(integrable_indicator_iff hs).mpr h.2.1,?_⟩
  intro ψ hψ hB
  have he (u : X → ℝ) : (∫ x, ψ x*s.indicator u x ∂μ) = ∫ x in s, ψ x*u x ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [he] using h.2.2 ψ hψ hB

end BoltzmannNonuniqueness.Published

end

end

end OAI
