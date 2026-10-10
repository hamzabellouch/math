import OAI.MeasureTheory.CompactFactors.Kernels

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable (X : Type*) [MeasurableSpace X]

def algebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨measurable_const, ⟨0, by simp⟩⟩
  one_mem' := ⟨measurable_const, ⟨1, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    exact ⟨hf.add hg, C+D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  mul_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    refine ⟨hf.mul hg, C*D, fun x => ?_⟩
    simpa only [Pi.mul_apply, norm_mul, NNReal.coe_mul] using
      mul_le_mul (hC x) (hD x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨measurable_const, ‖c‖₊, fun _ => le_rfl⟩

abbrev Func := ↥(algebra X)
variable {X}
instance : CoeFun (Func X) (fun _ => X → ℂ) := ⟨Subtype.val⟩

lemma measurable (f : Func X) : Measurable (f : X → ℂ) := f.property.1

def bound (f : Func X) : ℝ≥0 := f.property.2.choose
lemma norm_le_bound (f : Func X) (x : X) : ‖f x‖ ≤ bound f := f.property.2.choose_spec x

@[ext] lemma ext {f g : Func X} (h : ∀ x, f x = g x) : f = g := Subtype.ext (funext h)
@[simp] lemma add_apply (f g : Func X) (x : X) : (f+g) x = f x + g x := rfl
@[simp] lemma mul_apply (f g : Func X) (x : X) : (f*g) x = f x * g x := rfl
@[simp] lemma sub_apply (f g : Func X) (x : X) : (f-g) x = f x - g x := rfl
@[simp] lemma zero_apply (x : X) : (0 : Func X) x = 0 := rfl
@[simp] lemma one_apply (x : X) : (1 : Func X) x = 1 := rfl
@[simp] lemma smul_apply (c : ℂ) (f : Func X) (x : X) : (c • f) x = c * f x := rfl
@[simp] lemma real_smul_apply (c : ℝ) (f : Func X) (x : X) : (c • f) x = c • f x := rfl

def bmConj (f : Func X) : Func X :=
  ⟨fun x => star (f x), continuous_star.measurable.comp (measurable f), bound f, fun x => by simpa using norm_le_bound f x⟩
@[simp] lemma conj_apply (f : Func X) (x : X) : bmConj f x = star (f x) := rfl

def comp {Y : Type*} [MeasurableSpace Y] (f : Func Y) (q : X → Y) (hq : Measurable q) : Func X :=
  ⟨fun x => f (q x), (measurable f).comp hq, bound f, fun x => norm_le_bound f (q x)⟩
@[simp] lemma comp_apply {Y : Type*} [MeasurableSpace Y]
    (f : Func Y) (q : X → Y) (hq : Measurable q) (x : X) : comp f q hq x = f (q x) := rfl

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma memLp (f : Func X) (p : ℝ≥0∞) : MemLp (f : X → ℂ) p μ :=
  MemLp.of_bound (measurable f).aestronglyMeasurable (bound f) (.of_forall (norm_le_bound f))

def lp (p : ℝ≥0∞) (f : Func X) : Lp ℂ p μ := (memLp μ f p).toLp f
lemma coe_lp (p : ℝ≥0∞) (f : Func X) : lp μ p f =ᵐ[μ] f := MemLp.coeFn_toLp _

lemma lp_congr (p : ℝ≥0∞) {f g : Func X} (h : f =ᵐ[μ] g) : lp μ p f = lp μ p g :=
  MemLp.toLp_congr _ _ h

lemma lp_add (p : ℝ≥0∞) (f g : Func X) : lp μ p (f+g) = lp μ p f + lp μ p g :=
  (MemLp.toLp_add (memLp μ f p) (memLp μ g p)).symm

lemma lp_smul (p : ℝ≥0∞) (c : ℝ) (f : Func X) : lp μ p (c • f) = c • lp μ p f := rfl

@[simps] def l2 : Func X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun := lp μ 2
  map_add' := lp_add μ 2
  map_smul' := lp_smul μ 2

lemma l2_ae (f : Func X) : l2 μ f =ᵐ[μ] f := coe_lp μ 2 f

lemma l2_eq_iff (f g : Func X) : l2 μ f = l2 μ g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact (l2_ae μ f).symm.trans (h ▸ l2_ae μ g)
  · exact lp_congr μ 2

lemma integral_l2 (f : Func X) : ∫ x, l2 μ f x ∂μ = ∫ x, f x ∂μ :=
  integral_congr_ae (l2_ae μ f)

lemma inner_l2 (f g : Func X) :
    inner ℝ (l2 μ f) (l2 μ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae μ f, l2_ae μ g] with x hx hy
  rw [hx, hy]

lemma l2_norm_mul_le (f g : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ (f*g)‖ ≤ C * ‖l2 μ g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2_ae μ (f*g), l2_ae μ g] with x hx hy
  rw [hx, hy, mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)

lemma l2_norm_le [IsProbabilityMeasure μ] (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ f‖ ≤ C := by
  have hn : ∀ᵐ x ∂μ, ‖l2 μ f x‖ ≤ C := (l2_ae μ f).mono (fun x hx => by rw [hx]; exact hf x)
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hn.exists
    exact (norm_nonneg _).trans hx
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hn

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integrable (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) : Integrable (f : X → ℂ) μ :=
  (memLp μ f 1).integrable le_rfl

lemma integrable_norm_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    Integrable (fun x => ‖f x‖^2) μ :=
  Integrable.of_bound ((measurable f).norm.pow_const 2).aestronglyMeasurable ((bound f : ℝ)^2)
    (.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_sq] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_bound f x) 2)))

lemma norm_l2_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    ‖l2 μ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_l2]
  simp only [real_inner_self_eq_norm_sq]

def expect (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) : Func Y :=
  ⟨fun y => ∫ x, f x ∂κ y, (measurable f).stronglyMeasurable.integral_kernel.measurable,
    bound f, fun y => by
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall (norm_le_bound f))⟩

@[simp] lemma expect_apply (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) (y : Y) :
    expect κ f y = ∫ x, f x ∂κ y := rfl

lemma expect_bound (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X)
    {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖expect κ f y‖ ≤ C := by
  simpa only [expect_apply, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall hf)

lemma expect_add (κ : Kernel Y X) [IsMarkovKernel κ] (f g : Func X) :
    expect κ (f+g) = expect κ f + expect κ g := by
  ext y; exact integral_add (integrable (κ y) f) (integrable (κ y) g)

lemma expect_smul (κ : Kernel Y X) [IsMarkovKernel κ] (c : ℝ) (f : Func X) :
    expect κ (c • f) = c • expect κ f := by
  ext y; exact integral_smul c f

@[simps] def expectLinear (κ : Kernel Y X) [IsMarkovKernel κ] : Func X →ₗ[ℝ] Func Y where
  toFun := expect κ
  map_add' := expect_add κ
  map_smul' := expect_smul κ

lemma expect_conj (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) :
    expect κ (bmConj f) = bmConj (expect κ f) := by
  ext y; exact integral_conj

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

abbrev conditional (f : Func X) : Func Y := expect (condDistrib id q μ) f

def project (f : Func X) : Func X := comp (conditional μ q f) q hq

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma project_apply (f : Func X) (x : X) :
    project μ q hq f x = conditional μ q f (q x) := rfl

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_integral (f : Func X) : ∫ y, conditional μ q f y ∂μ.map q = ∫ x, f x ∂μ :=
  ConditionalFiber.integral_fiber μ q hq f (integrable μ f)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_integral (f : Func X) : ∫ x, project μ q hq f x ∂μ = ∫ x, f x ∂μ := by
  rw [← conditional_integral μ q hq f]
  exact (integral_map hq.aemeasurable (measurable (conditional μ q f)).aestronglyMeasurable).symm

lemma conditional_pullout (f : Func X) (b : Func Y) :
    conditional μ q (f * comp b q hq) =ᵐ[μ.map q] (conditional μ q f * b) := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, f x * b (q x) ∂condDistrib id q μ y) =
    (∫ x, f x ∂condDistrib id q μ y) * b y
  rw [← integral_mul_const]
  exact integral_congr_ae (hy.mono (fun x hx => by dsimp; rw [hx]))

lemma conditional_lift (b : Func Y) :
    conditional μ q (comp b q hq) =ᵐ[μ.map q] b := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, b (q x) ∂condDistrib id q μ y) = b y
  rw [integral_congr_ae (hy.mono (fun x hx => congrArg b hx))]
  simp

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_congr {f g : Func X} (h : f =ᵐ[μ] g) :
    conditional μ q f =ᵐ[μ.map q] conditional μ q g :=
  (ConditionalFiber.ae_fiber_of_ae μ q hq h).mono (fun _ hy => integral_congr_ae hy)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_norm_l2_le (f : Func X) :
    ‖l2 (μ.map q) (conditional μ q f)‖ ≤ ‖l2 μ f‖ := by
  have hs : ‖l2 (μ.map q) (conditional μ q f)‖^2 ≤ ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← ConditionalFiber.integral_fiber μ q hq
      (fun x => ‖f x‖^2) (integrable_norm_sq μ f)]
    apply integral_mono
    · exact integrable_norm_sq _ _
    · exact ConditionalFiber.integrable_fiber_integral μ q hq _ (integrable_norm_sq μ f)
    · intro y
      exact KernelCompact.norm_integral_sq _ f (integrable _ f) (integrable_norm_sq _ f)
  nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q f)), norm_nonneg (l2 μ f)]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_eq_condexp (f : Func X) :
    project μ q hq f =ᵐ[μ] μ[(f : X → ℂ) | MeasurableSpace.comap q ‹MeasurableSpace Y›] :=
  (condExp_ae_eq_integral_condDistrib_id hq (integrable μ f)).symm

end EuclideanFiveColor.BoundedMeasurable

end

end OAI
