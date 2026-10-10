import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace OAI

section

/-! # Compact time primitives for the characteristic weak equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def primitive (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in a..t, f s

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (primitive a f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem primitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    deriv (primitive a f) = f := by
  funext t
  exact (primitive_hasDerivAt hf a t).deriv

theorem primitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (primitive a f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (primitive_hasDerivAt hf.continuous a t).differentiableAt,?_⟩
  rw [primitive_deriv hf.continuous]
  exact hf

theorem primitive_eq_zero_left {f : ℝ → ℝ} {a b t : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (ht : t ≤ a) : primitive a f t = 0 := by
  rw [primitive,intervalIntegral.integral_symm]
  have hz : (∫ s in t..a, f s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with s hs'
    rw [uIoc_of_le ht] at hs'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge hs'.2) (hs h).1
  rw [hz,neg_zero]

theorem primitive_eq_zero_right {f : ℝ → ℝ} {a b t : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (ht : b ≤ t) (hi : (∫ s, f s) = 0) :
    primitive a f t = 0 := by
  rw [primitive,intervalIntegral.integral_eq_integral_of_support_subset]
  · exact hi
  · intro s hs'
    have h := hs (subset_tsupport _ hs')
    exact ⟨h.1,h.2.le.trans ht⟩

theorem primitive_support {f : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    tsupport (primitive a f) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  simp only [mem_Icc,not_and_or,not_le] at h
  obtain ht' | ht' := h
  · exact ht (primitive_eq_zero_left hs ht'.le)
  · exact ht (primitive_eq_zero_right hs ht'.le hi)

theorem primitive_compact {f : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    HasCompactSupport (primitive a f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (primitive_support hs hi)

theorem exists_test_primitive {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioo a b ∧ deriv g = f := by
  obtain ⟨a₀,haa₀,ha₀⟩ := hc.isCompact.exists_forall_le' continuous_id.continuousOn
    (fun x hx => (hs hx).1)
  obtain ⟨b₀,hb₀b,hb₀⟩ := hc.isCompact.exists_forall_le' (α := ℝᵒᵈ)
    continuous_id.continuousOn (fun x hx => (hs hx).2)
  let b₁ : ℝ := OrderDual.ofDual b₀
  change b₁ < b at hb₀b
  change ∀ x ∈ tsupport f, x ≤ b₁ at hb₀
  let c := (a+a₀)/2
  let d := (b₁+b)/2
  have hs' : tsupport f ⊆ Ioo c d := by
    intro x hx
    have h₁ := ha₀ x hx
    have h₂ := hb₀ x hx
    change a₀ ≤ x at h₁
    constructor <;> dsimp [c,d] <;> linarith
  refine ⟨primitive c f,primitive_contDiff hf c,primitive_compact hs' hi,?_,
    primitive_deriv hf.continuous c⟩
  intro x hx
  have hx' := primitive_support hs' hi hx
  dsimp [c,d] at hx'
  constructor <;> linarith [hx'.1,hx'.2]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Finite separated approximations of compact velocity tests

The approximating algebra consists of finite linear combinations of products
of one-variable continuous tests. This is the compact velocity approximation
used in the cold--hot product passage.
-/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def tensorTest (f : C(X, ℝ)) (g : C(Y, ℝ)) : C(X × Y, ℝ) :=
  ⟨fun p => f p.1*g p.2,(f.continuous.comp continuous_fst).mul
    (g.continuous.comp continuous_snd)⟩

inductive IsTensorSum : C(X × Y, ℝ) → Prop
  | zero : IsTensorSum 0
  | tensor (f : C(X, ℝ)) (g : C(Y, ℝ)) : IsTensorSum (tensorTest f g)
  | add {f g} : IsTensorSum f → IsTensorSum g → IsTensorSum (f+g)
  | smul (r : ℝ) {f} : IsTensorSum f → IsTensorSum (r • f)

theorem IsTensorSum.mul {f g : C(X × Y, ℝ)} (hf : IsTensorSum f) (hg : IsTensorSum g) :
    IsTensorSum (f*g) := by
  induction hf with
  | zero => simpa only [zero_mul] using (IsTensorSum.zero : IsTensorSum (0 : C(X × Y, ℝ)))
  | tensor a b =>
    induction hg with
    | zero => simpa only [mul_zero] using (IsTensorSum.zero : IsTensorSum (0 : C(X × Y, ℝ)))
    | tensor c d =>
      have he : tensorTest a b*tensorTest c d = tensorTest (a*c) (b*d) := by
        ext p
        change (a p.1*b p.2)*(c p.1*d p.2) = (a p.1*c p.1)*(b p.2*d p.2)
        ring
      rw [he]
      exact IsTensorSum.tensor _ _
    | add _ _ ih₁ ih₂ => simpa only [mul_add] using IsTensorSum.add ih₁ ih₂
    | smul r _ ih => simpa only [mul_smul_comm] using IsTensorSum.smul r ih
  | add _ _ ih₁ ih₂ => simpa only [add_mul] using IsTensorSum.add ih₁ ih₂
  | smul r _ ih => simpa only [smul_mul_assoc] using IsTensorSum.smul r ih

def tensorAlgebra (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    Subalgebra ℝ C(X × Y, ℝ) where
  carrier := {f | IsTensorSum f}
  zero_mem' := IsTensorSum.zero
  add_mem' := IsTensorSum.add
  mul_mem' := IsTensorSum.mul
  one_mem' := by
    change IsTensorSum (1 : C(X × Y, ℝ))
    convert IsTensorSum.tensor (1 : C(X, ℝ)) (1 : C(Y, ℝ)) using 1
    ext p
    simp [tensorTest]
  algebraMap_mem' r := by
    change IsTensorSum ((algebraMap ℝ C(X × Y, ℝ)) r)
    convert IsTensorSum.tensor (ContinuousMap.const X r) (1 : C(Y, ℝ)) using 1
    ext p
    simp [tensorTest]

theorem tensorAlgebra_separates : (tensorAlgebra X Y).SeparatesPoints := by
  intro p q hpq
  by_cases hx : p.1 = q.1
  · have hy : p.2 ≠ q.2 := fun h => hpq (Prod.ext hx h)
    let g : C(Y, ℝ) := ⟨fun y => dist y p.2,continuous_id.dist continuous_const⟩
    refine ⟨tensorTest 1 g,⟨tensorTest 1 g,IsTensorSum.tensor _ _,rfl⟩,?_⟩
    simpa [tensorTest,g] using (dist_pos.mpr (Ne.symm hy)).ne.symm
  · let f : C(X, ℝ) := ⟨fun x => dist x p.1,continuous_id.dist continuous_const⟩
    refine ⟨tensorTest f 1,⟨tensorTest f 1,IsTensorSum.tensor _ _,rfl⟩,?_⟩
    simpa [tensorTest,f] using (dist_pos.mpr (Ne.symm hx)).ne.symm

theorem exists_tensorSum_near_compact (f : C(X × Y, ℝ)) {K : Set (X × Y)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X × Y, ℝ), IsTensorSum g ∧ ∀ p ∈ K, |g p-f p| < ε := by
  obtain ⟨g,hg,happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (tensorAlgebra_separates (X := X) (Y := Y)) f hK hε
  exact ⟨g,hg,by simpa only [Real.norm_eq_abs] using happrox⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Compact mixed measures are determined by separated velocity tests -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

private theorem test_integrable (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (f : C(X × Y, ℝ)) : Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

theorem IsTensorSum.integral_tendsto
    {μ : ℕ → Measure (X × Y)} {ν : Measure (X × Y)}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (h : ∀ f : C(X, ℝ), ∀ g : C(Y, ℝ),
      Tendsto (fun n => ∫ p, f p.1*g p.2 ∂μ n) atTop
        (𝓝 (∫ p, f p.1*g p.2 ∂ν)))
    {k : C(X × Y, ℝ)} (hk : IsTensorSum k) :
    Tendsto (fun n => ∫ p, k p ∂μ n) atTop (𝓝 (∫ p, k p ∂ν)) := by
  induction hk with
  | zero => simpa only [ContinuousMap.zero_apply,integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | tensor f g => exact h f g
  | @add f g _ _ ih₁ ih₂ =>
    simpa only [ContinuousMap.add_apply,integral_add (test_integrable _ f) (test_integrable _ g)]
      using ih₁.add ih₂
  | smul r _ ih =>
    simpa only [ContinuousMap.smul_apply,smul_eq_mul,integral_const_mul] using ih.const_mul r

private theorem integral_test_error (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (f g : C(X × Y, ℝ)) {δ : ℝ} (hδ : ∀ p, |f p-g p| ≤ δ) :
    |(∫ p, f p ∂μ)-(∫ p, g p ∂μ)| ≤ δ*μ.real univ := by
  rw [← integral_sub (test_integrable _ f) (test_integrable _ g),← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ (fun p => by
    simpa only [Real.norm_eq_abs] using hδ p))

theorem integral_tendsto_of_tensor_tests
    {μ : ℕ → Measure (X × Y)} {ν : Measure (X × Y)}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ᶠ n in atTop, (μ n).real univ ≤ C)
    (h : ∀ f : C(X, ℝ), ∀ g : C(Y, ℝ),
      Tendsto (fun n => ∫ p, f p.1*g p.2 ∂μ n) atTop
        (𝓝 (∫ p, f p.1*g p.2 ∂ν)))
    (f : C(X × Y, ℝ)) :
    Tendsto (fun n => ∫ p, f p ∂μ n) atTop (𝓝 (∫ p, f p ∂ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let D := ν.real univ
  have hD : 0 ≤ D := measureReal_nonneg
  let δ := ε/(3*(C+D+1))
  have hden : 0 < 3*(C+D+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(3*(C+D+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hg,happrox⟩ := exists_tensorSum_near_compact f isCompact_univ hδ
  have hfg (p) : |f p-g p| ≤ δ := by
    rw [abs_sub_comm]
    exact (happrox p (mem_univ p)).le
  have hgf (p) : |g p-f p| ≤ δ := (happrox p (mem_univ p)).le
  have hlim := hg.integral_tendsto h
  have hmid := (Metric.tendsto_nhds.mp hlim) (ε/3) (by positivity)
  filter_upwards [hμ,hmid] with n hn hgn
  rw [Real.dist_eq] at hgn ⊢
  have hleft := (integral_test_error (μ n) f g hfg).trans
    (mul_le_mul_of_nonneg_left hn hδ.le)
  have hright := integral_test_error ν g f hgf
  have htri := (abs_sub_le (∫ p, f p ∂μ n) (∫ p, g p ∂μ n) (∫ p, f p ∂ν)).trans
    (add_le_add le_rfl (abs_sub_le (∫ p, g p ∂μ n) (∫ p, g p ∂ν) (∫ p, f p ∂ν)))
  change |(∫ p, g p ∂ν)-(∫ p, f p ∂ν)| ≤ δ*D at hright
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Compact-open convergence of tests with one common compact support -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

theorem tendsto_integral_mul_common_support {μ : Measure E} {u : E → ℝ} (hu : Integrable u μ)
    {F : ℕ → C(E,ℝ)} {f : C(E,ℝ)} {K : Set E} (hK : IsCompact K)
    (hF : ∀ n, tsupport (F n) ⊆ K) (hf : tsupport f ⊆ K)
    (h : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, F n x*u x ∂μ) atTop (𝓝 (∫ x, f x*u x ∂μ)) := by
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hf
  obtain ⟨C,hC⟩ := f.continuous.bounded_above_of_compact_support hfc
  have hU := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp h K hK
  have hb : ∀ᶠ n in atTop, ∀ x, ‖F n x‖ ≤ max C 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 (by norm_num)] with n hn x
    by_cases hx : x ∈ K
    · have hd := hn x hx
      have hfbound := (hC x).trans (le_max_left C 0)
      have he : ‖F n x‖ ≤ ‖F n x-f x‖+‖f x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F n x-f x) (f x)
      have hdist : ‖F n x-f x‖ < 1 := by
        rw [dist_eq_norm, norm_sub_rev] at hd
        exact hd
      linarith
    · have hz : F n x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hF n hs))
      rw [hz,norm_zero]
      positivity
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (max C 0+1)*‖u x‖)
  · exact Eventually.of_forall (fun n => (F n).continuous.measurable.aestronglyMeasurable.mul hu.1)
  · filter_upwards [hb] with n hn
    exact ae_of_all _ (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hn x) (norm_nonneg _))
  · exact hu.norm.const_mul _
  · filter_upwards [] with x
    have ht : Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
      (continuous_eval_const x).continuousAt.tendsto.comp h
    exact ht.mul_const (u x)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Compact uniform convergence of a jointly continuous parameter family -/

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.GainPullback

theorem uniform_on_compact_of_joint_continuous
    {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [T2Space Q]
    [UniformSpace R] {F : P × Q → R} (hF : Continuous F)
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {K : Set Q} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n q => F (p n,q)) (fun q => F (p₀,q)) atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : C(P × K,R) := ⟨fun x => F (x.1,x.2),
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have ht := (G.curry.continuous.tendsto p₀).comp hp
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp ht
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact hu

theorem uniform_on_compact_of_joint_restriction
    {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [T2Space Q]
    [UniformSpace R] {F : P × Q → R} {K : Set Q} (hK : IsCompact K)
    (hF : Continuous (fun p : P × K => F (p.1,p.2.val)))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀)) :
    TendstoUniformlyOn (fun n q => F (p n,q)) (fun q => F (p₀,q)) atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu := uniform_on_compact_of_joint_continuous hF hp (K := Set.univ) isCompact_univ
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (tendstoUniformlyOn_univ.mp hu)

end BoltzmannNonuniqueness.GainPullback


end

end OAI
