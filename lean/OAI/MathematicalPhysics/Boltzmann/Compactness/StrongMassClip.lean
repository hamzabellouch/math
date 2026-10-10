import OAI.MathematicalPhysics.Boltzmann.Branching.PairwiseSubsequenceCauchy
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Measure.Continuity

namespace OAI

section

/-! # Strong L¹ convergence implies the bounded-test weak convergence used here -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem weakL1_of_integral_norm_sub {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hg : Integrable g μ)
    (h : Tendsto (fun n => ∫ x, ‖f n x-g x‖ ∂μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  refine ⟨hgm,hg,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have he n : (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*g x ∂μ) =
      ∫ x, ψ x*(f n x-g x) ∂μ := by
    rw [← integral_sub ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
      (hg.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))]
    congr 1
    funext x
    ring
  have hzero : Tendsto (fun n => (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*g x ∂μ))
      atTop (𝓝 0) := by
    simp_rw [he]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro n
      calc
        _ ≤ ∫ x, |C| * ‖f n x-g x‖ ∂μ := by
          apply norm_integral_le_of_norm_le (((hf n).sub hg).norm.const_mul |C|)
          filter_upwards [] with x
          rw [norm_mul,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (norm_nonneg _)
        _ = |C| * (∫ x, ‖f n x-g x‖ ∂μ) := integral_const_mul _ _
    · simpa using h.const_mul |C|
  have hplus := hzero.add (tendsto_const_nhds (x := ∫ x, ψ x*g x ∂μ))
  simpa only [sub_add_cancel,zero_add] using hplus

theorem WeakL1Converges.add {μ : Measure X} {f k : ℕ → X → ℝ} {g h : X → ℝ}
    (hf : WeakL1Converges μ f g) (hk : WeakL1Converges μ k h)
    (hfi : ∀ n, Integrable (f n) μ) (hki : ∀ n, Integrable (k n) μ) :
    WeakL1Converges μ (fun n x => f n x+k n x) (fun x => g x+h x) := by
  refine ⟨hf.1.add hk.1,hf.2.1.add hk.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hm (u : X → ℝ) (hu : Integrable u μ) : Integrable (fun x => ψ x*u x) μ :=
    hu.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he (u v : X → ℝ) (hu : Integrable u μ) (hv : Integrable v μ) :
      (∫ x, ψ x*(u x+v x) ∂μ) = (∫ x, ψ x*u x ∂μ)+(∫ x, ψ x*v x ∂μ) := by
    simp_rw [mul_add]
    exact integral_add (hm u hu) (hm v hv)
  simp_rw [he _ _ (hfi _) (hki _),he _ _ hf.2.1 hk.2.1]
  exact (hf.2.2 ψ hψ ⟨C,hC⟩).add (hk.2.2 ψ hψ ⟨C,hC⟩)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong L1 convergence implies convergence against bounded measurable tests -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem weakL1_of_strong {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hgm : Measurable g)
    (hgi : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  have hc : WeakL1Converges μ (fun _ : ℕ => g) g :=
    ⟨hgm,hgi,fun _ _ _ => tendsto_const_nhds⟩
  exact hc.of_eLpNorm_sub (fun _ => hgi) hfi h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong L1 convergence from weak convergence and second moments -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem integral_abs_tendsto_zero_of_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {d : ℕ → X → ℝ}
    (hi : ∀ᶠ n in atTop, Integrable (d n) μ)
    (hsq : ∀ᶠ n in atTop, Integrable (fun x => (d n x)^2) μ)
    (hlim : Tendsto (fun n => ∫ x, (d n x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |d n x| ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun _ => abs_nonneg _)))
  · intro ε hε
    let r := ε/(2*(μ.real univ+1))
    have hm : 0 ≤ μ.real univ := measureReal_nonneg
    have hr : 0 < r := div_pos hε (by positivity)
    have hre : r*(2*(μ.real univ+1)) = ε := div_mul_cancel₀ ε (by positivity)
    have hs := hlim.eventually (gt_mem_nhds (show 0 < r*(ε/2) by positivity))
    filter_upwards [hi,hsq,hs] with n hin hsn hn
    have hb : r*(∫ x, |d n x| ∂μ) ≤ r^2*μ.real univ+(∫ x, (d n x)^2 ∂μ) := by
      calc
        _ = ∫ x, r*|d n x| ∂μ := (integral_const_mul _ _).symm
        _ ≤ ∫ x, r^2+(d n x)^2 ∂μ := integral_mono (hin.abs.const_mul r)
          ((integrable_const _).add hsn) (fun x => by
            nlinarith [sq_nonneg (|d n x|-r),sq_abs (d n x)])
        _ = _ := by rw [integral_add (integrable_const _) hsn,integral_const,smul_eq_mul]; ring
    nlinarith

theorem strong_L1_of_weak_and_squares
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] [μ.Regular]
    {f : ℕ → X → ℝ} {g : X → ℝ} (hw : Published.WeakL1Converges μ f g)
    (hfm : ∀ n, Measurable (f n)) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |f n x| ≤ C) (hgC : ∀ᵐ x ∂μ, |g x| ≤ C)
    (hsq : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ))) :
    Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0) := by
  have hg2 : Integrable (fun x => (g x)^2) μ := Integrable.of_bound
    (hw.1.pow_const 2).aestronglyMeasurable (C^2) (hgC.mono (fun x hx => by
      simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hx 2))
  have hcross := (hw.weakStar hfm hC hfC hgC).2 g hw.2.1
  have hd : ∀ᶠ n in atTop, Integrable (fun x => f n x-g x) μ := by
    filter_upwards [hfC] with n hn
    exact (Integrable.of_bound (hfm n).aestronglyMeasurable C hn).sub hw.2.1
  have hdi : ∀ᶠ n in atTop, Integrable (fun x => (f n x-g x)^2) μ := by
    filter_upwards [hfC] with n hn
    apply Integrable.of_bound ((hfm n).sub hw.1 |>.pow_const 2).aestronglyMeasurable ((2*C)^2)
    filter_upwards [hn,hgC] with x hfx hgx
    rw [Real.norm_eq_abs,abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith)) 2
  have hdsq : Tendsto (fun n => ∫ x, (f n x-g x)^2 ∂μ) atTop (𝓝 0) := by
    have ht := (hsq.sub (hcross.const_mul 2)).add_const (∫ x, (g x)^2 ∂μ)
    simp only [show (fun x => g x*g x) = (fun x => (g x)^2) by ext x; ring] at ht
    have hz : (∫ x, (g x)^2 ∂μ)-2*(∫ x, (g x)^2 ∂μ)+(∫ x, (g x)^2 ∂μ) = 0 := by ring
    rw [hz] at ht
    apply ht.congr'
    filter_upwards [hfC] with n hn
    have hf := Integrable.of_bound (hfm n).aestronglyMeasurable C hn
    have hf2 : Integrable (fun x => (f n x)^2) μ := Integrable.of_bound
      ((hfm n).pow_const 2).aestronglyMeasurable (C^2) (hn.mono (fun x hx => by
        simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hx 2))
    have hfg := hf.bdd_mul hw.1.aestronglyMeasurable hgC
    rw [← integral_const_mul,← integral_sub hf2 (hfg.const_mul 2),← integral_add _ hg2]
    · apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    · exact hf2.sub (hfg.const_mul 2)
  have hl := integral_abs_tendsto_zero_of_sq hd hdi hdsq
  have ht := ENNReal.continuous_ofReal.tendsto 0 |>.comp hl
  simp only [ENNReal.ofReal_zero] at ht
  apply ht.congr'
  filter_upwards [hd] with n hn
  rw [eLpNorm_one_eq_lintegral_enorm hn.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hn]
  rfl

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong L1 convergence from local convergence and uniform integrability -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_small_complements {f : ℕ → X → ℝ}
    (hu : UnifIntegrable f 1 μ) (s : ℕ → Set X)
    (hs : ∀ m, MeasurableSet (s m))
    (htail : Tendsto (fun m => μ (s m)ᶜ) atTop (𝓝 0))
    (hlocal : ∀ m, Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict (s m)))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have he : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ,hδ,hsmall⟩ := unifIntegrable_iff.mp hu (ε/2) he
  obtain ⟨m,hm⟩ := (ENNReal.tendsto_nhds_zero.mp htail δ hδ).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hlocal m) (ε/2) he] with n hn
  calc
    eLpNorm (f n) 1 μ = eLpNorm (f n) 1 (μ.restrict (s m)) +
        eLpNorm (f n) 1 (μ.restrict (s m)ᶜ) := by
      rw [← eLpNorm_one_add_measure,Measure.restrict_add_restrict_compl (hs m)]
    _ ≤ ε/2+ε/2 := add_le_add hn (hsmall n (s m)ᶜ hm)
    _ = ε := ε.add_halves

theorem strongL1_of_exhaustion [IsFiniteMeasure μ] {f : ℕ → X → ℝ}
    (hu : UnifIntegrable f 1 μ) (s : ℕ → Set X)
    (hs : ∀ m, MeasurableSet (s m)) (hmono : Monotone s)
    (hcover : ∀ᵐ x ∂μ, ∃ m, x ∈ s m)
    (hlocal : ∀ m, Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict (s m)))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  apply strongL1_of_small_complements hu s hs _ hlocal
  have hz : μ (⋂ m, (s m)ᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with x hx
    simpa only [mem_iInter,mem_compl_iff,not_forall,not_not] using hx
  have ht := tendsto_measure_iInter_atTop
    (fun m => (hs m).compl.nullMeasurableSet)
    (show Antitone (fun m => (s m)ᶜ) from fun i j hij => compl_subset_compl.mpr (hmono hij))
    ⟨0,measure_ne_top μ _⟩
  simpa only [Function.comp_def,hz] using ht

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Pairwise strong convergence identifies the existing weak L1 limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open Published
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_pairwise_subsequences {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hw : WeakL1Converges μ f g)
    (hp : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => eLpNorm (fun x => f (i n) x-f (j n) x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0) := by
  let u n : Lp ℝ 1 μ := (hfi n).toL1 (f n)
  have hc : CauchySeq u := by
    apply cauchySeq_of_pairwise_subsequences
    intro i j hi hj
    have ht := hp i j hi hj
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    exact (Lp.edist_toLp_toLp (f (i n)) (f (j n))
      (memLp_one_iff_integrable.mpr (hfi (i n))) (memLp_one_iff_integrable.mpr (hfi (j n)))).symm
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete hc
  let v : X → ℝ := (Lp.aestronglyMeasurable q).mk q
  have hvm : Measurable v := (Lp.aestronglyMeasurable q).stronglyMeasurable_mk.measurable
  have hqv : (q : X → ℝ) =ᵐ[μ] v := (Lp.aestronglyMeasurable q).ae_eq_mk
  have hvi : Integrable v μ := (L1.integrable_coeFn q).congr hqv
  have hs : Tendsto (fun n => eLpNorm (fun x => f n x-v x) 1 μ) atTop (𝓝 0) := by
    have ht := hq.edist (tendsto_const_nhds (x := q))
    simp only [edist_self] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    change edist ((memLp_one_iff_integrable.mpr (hfi n)).toLp (f n)) q = _
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    filter_upwards [(hfi n).coeFn_toL1,hqv] with x hx hqx
    exact congrArg₂ (fun a b : ℝ => a-b) hx hqx
  have hvw : WeakL1Converges μ f v := by
    apply weakL1_of_integral_norm_sub hfi hvm hvi
    have he n : (∫ x, ‖f n x-v x‖ ∂μ) =
        (eLpNorm (fun x => f n x-v x) 1 μ).toReal := by
      change (∫ x, ‖(f n-v) x‖ ∂μ) = (eLpNorm (f n-v) 1 μ).toReal
      rw [eLpNorm_one_eq_lintegral_enorm ((hfi n).sub hvi).aestronglyMeasurable,
        integral_norm_eq_lintegral_enorm ((hfi n).sub hvi).aestronglyMeasurable]
    simp only [he]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
  have hvg : v =ᵐ[μ] g := hvw.unique hw
  apply hs.congr'
  exact Eventually.of_forall (fun n => eLpNorm_congr_ae
    (hvg.mono (fun x hx => congrArg (fun y : ℝ => f n x-y) hx)))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Removing a countable nonzero family of spatial patch multipliers -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem strong_on_union {f : ℕ → X → ℝ} {s t : Set X}
    (hs : Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict s)) atTop (𝓝 0))
    (ht : Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict t)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict (s ∪ t))) atTop (𝓝 0) := by
  have hsum := hs.add ht
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  exact (eLpNorm_mono_measure (f n) (Measure.restrict_union_le s t)).trans_eq
    (eLpNorm_one_add_measure _ _ _)

theorem strongL1_of_countable_cover [IsFiniteMeasure μ] {f : ℕ → X → ℝ}
    (hu : UnifIntegrable f 1 μ) (s : ℕ → Set X)
    (hs : ∀ m, MeasurableSet (s m)) (hcover : ∀ᵐ x ∂μ, ∃ m, x ∈ s m)
    (hlocal : ∀ m, Tendsto (fun n => eLpNorm (f n) 1 (μ.restrict (s m)))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  have hfin (I : Finset ℕ) : Tendsto
      (fun n => eLpNorm (f n) 1 (μ.restrict (⋃ i ∈ I, s i))) atTop (𝓝 0) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using strong_on_union (hlocal i) ih
  apply strongL1_of_exhaustion hu (fun m => ⋃ i ∈ Finset.range m, s i)
  · exact fun m => MeasurableSet.biUnion (Finset.range m).countable_toSet (fun i _ => hs i)
  · intro m n hmn x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i,Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn),hx⟩
  · filter_upwards [hcover] with x hx
    obtain ⟨i,hi⟩ := hx
    exact ⟨i+1,mem_iUnion₂.mpr ⟨i,Finset.mem_range.mpr (Nat.lt_succ_self i),hi⟩⟩
  · exact fun m => hfin (Finset.range m)

theorem strongL1_of_nonzero_patches [IsFiniteMeasure μ]
    {a : ℕ → X → ℝ} {b : X → ℝ} {χ : ℕ → X → ℝ}
    (ha : ∀ n, Measurable (a n)) (hb : Measurable b)
    (hu : UniformIntegrable a 1 μ) (hbi : Integrable b μ)
    (hχ : ∀ j, Measurable (χ j))
    (hcover : ∀ᵐ x ∂μ, ∃ j, χ j x ≠ 0)
    (hlocal : ∀ j, Tendsto (fun n => eLpNorm
      (fun x => χ j x*a n x-χ j x*b x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-b x) 1 μ) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun m =>
    {x | 1/(((Nat.unpair m).2:ℝ)+1) ≤ |χ (Nat.unpair m).1 x|}
  have hs m : MeasurableSet (s m) := by
    dsimp only [s]
    simpa only [Real.norm_eq_abs] using
      measurableSet_le measurable_const (hχ (Nat.unpair m).1).norm
  have hbc : UniformIntegrable (fun _ : ℕ => b) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hbi)
  apply strongL1_of_countable_cover (uniformIntegrable_sub hu hbc).1 s hs
  · filter_upwards [hcover] with x hx
    obtain ⟨j,hj⟩ := hx
    obtain ⟨k,hk⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds (abs_pos.mpr hj))).exists
    refine ⟨Nat.pair j k,?_⟩
    simpa only [s,mem_ofPred_eq,Nat.unpair_pair] using hk.le
  · intro m
    exact strong_on_patch_of_weighted ha hb (hs m) (by positivity)
      (fun _ hx => hx) (hlocal (Nat.unpair m).1)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Identified pair limits imply strong convergence of bounded velocity averages -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem strong_average_of_weak_pairs
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.Regular] {ν : Measure Y} [SFinite ν]
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hw : Published.WeakL1Converges (μ.prod ν) f g)
    (hp : Published.WeakL1Converges (μ.prod (ν.prod ν))
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2))
      (fun z => g (z.1,z.2.1)*g (z.1,z.2.2)))
    (hfm : ∀ n, Measurable (f n))
    (hi : ∀ᶠ n in atTop, Integrable (f n) (μ.prod ν))
    (hpi : ∀ᶠ n in atTop, Integrable
      (fun z : X × (Y × Y) => f n (z.1,z.2.1)*f n (z.1,z.2.2)) (μ.prod (ν.prod ν)))
    {ψ : Y → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ y, |ψ y| ≤ B)
    {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |∫ y, ψ y*f n (x,y) ∂ν| ≤ C)
    (hb : ∀ᵐ x ∂μ, |∫ y, ψ y*g (x,y) ∂ν| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ y, ψ y*f n (x,y) ∂ν)-(∫ y, ψ y*g (x,y) ∂ν)) 1 μ) atTop (𝓝 0) := by
  have hw' := hw.marginal_eventually hi (hψ.comp measurable_snd) B (fun z => hB z.2)
  have hψp : Measurable (fun z : X × (Y × Y) => ψ z.2.1*ψ z.2.2) :=
    (hψ.comp measurable_snd.fst).mul (hψ.comp measurable_snd.snd)
  have hBp (z : X × (Y × Y)) : |ψ z.2.1*ψ z.2.2| ≤ |B| * |B| := by
    rw [abs_mul]
    exact mul_le_mul ((hB _).trans (le_abs_self B)) ((hB _).trans (le_abs_self B))
      (abs_nonneg _) (abs_nonneg _)
  have hp' := hp.marginal_eventually hpi hψp (|B| * |B|) hBp
  have he (u : X × Y → ℝ) (x : X) :
      (∫ y : Y × Y, (ψ y.1*ψ y.2)*(u (x,y.1)*u (x,y.2)) ∂ν.prod ν) =
        (∫ y, ψ y*u (x,y) ∂ν)^2 := by
    rw [pow_two,← integral_prod_mul]
    congr 1
    funext y
    ring
  have hs := hp'.2.2 (fun _ => 1) measurable_const ⟨1,fun _ => by norm_num⟩
  simp only [one_mul,he] at hs
  apply strong_L1_of_weak_and_squares hw' _ hC ha hb hs
  intro n
  exact ((hψ.comp measurable_snd).mul (hfm n)).stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Bounded mass coefficients preserve strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def massClip (K r : ℝ) : ℝ := min K (1+r)

theorem massClip_measurable (K : ℝ) {r : X → ℝ} (hr : Measurable r) :
    Measurable (fun x => massClip K (r x)) :=
  measurable_const.min (measurable_const.add hr)

theorem massClip_bounds {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    0 ≤ massClip K r ∧ massClip K r ≤ K :=
  ⟨le_min hK (by linarith),min_le_left _ _⟩

theorem massClip_lipschitz (K r s : ℝ) :
    |massClip K r-massClip K s| ≤ |r-s| := by
  simpa only [massClip,sub_self,abs_zero,add_sub_add_left_eq_sub,max_eq_right (abs_nonneg (r-s))]
    using abs_min_sub_min_le_max K (1+r) K (1+s)

theorem strong_massClip {r : ℕ → X → ℝ} {s : X → ℝ}
    (hr : ∀ n, Measurable (r n)) (hs : Measurable s) (K : ℝ)
    (h : Tendsto (fun n => eLpNorm (fun x => r n x-s x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => massClip K (r n x)-massClip K (s x)) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
  intro n
  apply eLpNorm_mono ((massClip_measurable K (hr n)).sub (massClip_measurable K hs)).aestronglyMeasurable
  intro x
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using massClip_lipschitz K (r n x) (s x)

theorem strongL1_comp_fst {Y : Type*} [MeasurableSpace Y]
    [SFinite μ] {ν : Measure Y} [IsFiniteMeasure ν] {f : ℕ → X → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (h : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p : X × Y => f n p.1) 1 (μ.prod ν)) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.mul_const h
    (Or.inr (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ) : Integrable _ ν)).eLpNorm_ne_top)
  simp only [zero_mul] at ht
  simpa only [← eLpNorm_mul_prod_one (hfm _) measurable_const,mul_one] using ht

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
