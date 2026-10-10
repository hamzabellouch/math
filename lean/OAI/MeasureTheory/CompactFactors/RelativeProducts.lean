import OAI.MeasureTheory.CompactFactors.Amenability
import OAI.MeasureTheory.CompactFactors.BoundedFunctions

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [AddGroup K] [AddAction K X] [AddAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstVAdd K X] [MeasurableConstVAdd K Y]

instance law_probability_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k +ᵥ y) =
      (condDistrib id q μ y).map (fun x => k +ᵥ x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.vadd k) (MeasurableEquiv.vadd k) (fun x => k +ᵥ x)
    (measurable_const_vadd k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k +ᵥ z.1,k +ᵥ z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_vadd (M := K) (α := X) k
  have hR := measurable_const_vadd (M := K) (α := Y) k
  have hν : ν.map (fun y => k +ᵥ y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k +ᵥ x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance_add μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k +ᵥ x) (fun x => k +ᵥ x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k +ᵥ x)).prod (κ.map (fun x => k +ᵥ x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k +ᵥ y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k +ᵥ y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) :
    VAddInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving_add μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

def projectCLM : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (lpMeas ℂ ℝ (MeasurableSpace.comap q ‹MeasurableSpace Y›) 2 μ).subtypeL.comp
    (condExpL2 ℂ ℝ hq.comap_le)

lemma projectCLM_l2 (f : Func X) : projectCLM μ q hq (l2 μ f) = l2 μ (project μ q hq f) := by
  apply Lp.ext
  exact ((memLp μ f 2).condExpL2_ae_eq_condExp (𝕜 := ℝ) hq.comap_le).trans
    ((project_eq_condexp μ q hq f).symm.trans (l2_ae μ (project μ q hq f)).symm)

lemma norm_project_l2 (f : Func X) :
    ‖l2 μ (project μ q hq f)‖ = ‖l2 (μ.map q) (conditional μ q f)‖ := by
  have : ‖l2 μ (project μ q hq f)‖^2 = ‖l2 (μ.map q) (conditional μ q f)‖^2 := by
    rw [norm_l2_sq, norm_l2_sq]
    exact (integral_map hq.aemeasurable
      ((measurable (conditional μ q f)).norm.pow_const 2).aestronglyMeasurable).symm
  nlinarith [norm_nonneg (l2 μ (project μ q hq f)),
    norm_nonneg (l2 (μ.map q) (conditional μ q f))]

end
section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

def act (g : G) (f : Func X) : Func X := comp f (fun x => g +ᵥ x) (measurable_const_vadd g)
@[simp] lemma act_apply (g : G) (f : Func X) (x : X) : act g f x = f (g +ᵥ x) := rfl
lemma act_add (g h : G) (f : Func X) : act (g+h) f = act g (act h f) := by
  ext x
  simp only [act_apply, ← add_vadd, add_comm g h]
lemma act_mul (g : G) (f h : Func X) : act g (f*h) = act g f * act g h := rfl
lemma act_conj (g : G) (f : Func X) : act g (bmConj f) = bmConj (act g f) := rfl
lemma act_sub (g : G) (f h : Func X) : act g (f-h) = act g f - act g h := rfl

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_act (g : G) (f : Func X) :
    l2 μ (act g f) = Amenable.Koopman.action μ g (l2 μ f) := by
  apply Lp.ext
  exact (l2_ae μ (act g f)).trans ((MeasureTheory.measurePreserving_vadd g μ).quasiMeasurePreserving.ae_eq_comp
    (l2_ae μ f)).symm |>.trans (Amenable.Koopman.coe_action μ g (l2 μ f)).symm

end
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_sub (f g : Func X) : project μ q hq (f-g) = project μ q hq f - project μ q hq g := by
  ext x
  exact integral_sub (integrable _ f) (integrable _ g)
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_bound (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (x : X) :
    ‖project μ q hq f x‖ ≤ C := expect_bound _ f hf (q x)
lemma project_comp (b : Func Y) : project μ q hq (comp b q hq) =ᵐ[μ] comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_lift μ q hq b)
lemma project_project (f : Func X) : project μ q hq (project μ q hq f) =ᵐ[μ] project μ q hq f :=
  project_comp μ q hq _
lemma center_project_l2 (f : Func X) : l2 μ (project μ q hq (f-project μ q hq f)) = 0 := by
  rw [project_sub, map_sub]
  have : l2 μ (project μ q hq (project μ q hq f)) = l2 μ (project μ q hq f) :=
    (l2_eq_iff μ _ _).mpr (project_project μ q hq f)
  rw [this, sub_self]

lemma project_pullout (f : Func X) (b : Func Y) :
    project μ q hq (f * comp b q hq) =ᵐ[μ] project μ q hq f * comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_pullout μ q hq f b)

lemma integral_mul_lift (f : Func X) (b : Func Y) :
    ∫ x, (f * comp b q hq) x ∂μ = ∫ x, (project μ q hq f * comp b q hq) x ∂μ := by
  rw [← project_integral μ q hq (f * comp b q hq)]
  exact integral_congr_ae (project_pullout μ q hq f b)

variable {G : Type*} [AddCommGroup G] [AddAction G X] [AddAction G Y]
  [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, ∀ᵐ x ∂μ, q (g +ᵥ x) = g +ᵥ q x)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma conditional_act (g : G) (f : Func X) :
    conditional μ q (act g f) =ᵐ[μ.map q] act g (conditional μ q f) := by
  filter_upwards [RelativeProduct.conditional_covariance_add μ q hq
    (fun k => measurePreserving_vadd k μ) hqcov g] with y hy
  change (∫ x, f (g +ᵥ x) ∂condDistrib id q μ y) = ∫ x, f x ∂condDistrib id q μ (g +ᵥ y)
  rw [hy]
  exact (integral_map (measurable_const_vadd g).aemeasurable (measurable f).aestronglyMeasurable).symm

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ] in
include hqcov in
lemma act_lift (g : G) (b : Func Y) :
    act g (comp b q hq) =ᵐ[μ] comp (act g b) q hq := by
  filter_upwards [hqcov g] with x hx
  simp only [act_apply, comp_apply, hx]

omit [StandardBorelSpace Y] [Nonempty Y] in
include hqcov in
lemma project_act (g : G) (f : Func X) :
    project μ q hq (act g f) =ᵐ[μ] act g (project μ q hq f) := by
  have he : project μ q hq (act g f) =ᵐ[μ] comp (act g (conditional μ q f)) q hq :=
    ae_of_ae_map hq.aemeasurable (conditional_act μ q hq hqcov g f)
  exact he.trans (act_lift μ q hq hqcov g _).symm

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable (G X : Type*) [MeasurableSpace X]
def familyAlgebra : Subalgebra ℂ (G → Func X) where
  carrier := {F | ∃ C : ℝ≥0, ∀ g x, ‖F g x‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    exact ⟨C+D, fun g x => (norm_add_le _ _).trans (add_le_add (hC g x) (hD g x))⟩
  mul_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    refine ⟨C*D, fun g x => ?_⟩
    change ‖F g x * H g x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hC g x) (hD g x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨‖c‖₊, fun _ _ => le_rfl⟩
abbrev Family := ↥(familyAlgebra G X)
variable {G X}
instance : CoeFun (Family G X) (fun _ => G → Func X) := ⟨Subtype.val⟩
instance familyRealModule : Module ℝ (Family G X) := Module.complexToReal (Family G X)

namespace Family
def bound (F : Family G X) : ℝ≥0 := F.property.choose
lemma norm_le_bound (F : Family G X) (g : G) (x : X) : ‖F g x‖ ≤ F.bound := F.property.choose_spec g x
@[ext] lemma ext {F H : Family G X} (h : ∀ g, F g = H g) : F = H := Subtype.ext (funext h)
@[simp] lemma add_apply (F H : Family G X) (g : G) : (F+H) g = F g + H g := rfl
@[simp] lemma mul_apply (F H : Family G X) (g : G) : (F*H) g = F g * H g := rfl
@[simp] lemma sub_apply (F H : Family G X) (g : G) : (F-H) g = F g - H g := rfl
@[simp] lemma zero_apply (g : G) : (0 : Family G X) g = 0 := rfl
@[simp] lemma one_apply (g : G) : (1 : Family G X) g = 1 := rfl
@[simp] lemma real_smul_apply (c : ℝ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma complex_smul_apply (c : ℂ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma prod_apply {ι : Type*} (s : Finset ι) (F : ι → Family G X) (g : G) :
    (∏ i ∈ s, F i) g = ∏ i ∈ s, F i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

def const (f : Func X) : Family G X := ⟨fun _ => f, BoundedMeasurable.bound f,
  fun _ => BoundedMeasurable.norm_le_bound f⟩
@[simp] lemma const_apply (f : Func X) (g : G) : const f g = f := rfl

def bmConj (F : Family G X) : Family G X := ⟨fun g => BoundedMeasurable.bmConj (F g), F.bound,
  fun g x => by simpa using F.norm_le_bound g x⟩
@[simp] lemma conj_apply (F : Family G X) (g : G) : bmConj F g = BoundedMeasurable.bmConj (F g) := rfl

variable [TopologicalSpace G] [DiscreteTopology G]
variable (μ : Measure X) [IsProbabilityMeasure μ]

def toL2 (F : Family G X) : G →ᵇ Lp ℂ 2 μ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => l2 μ (F g))
    continuous_of_discreteTopology F.bound (fun g => l2_norm_le μ (F g) (F.norm_le_bound g))
@[simp] lemma toL2_apply (F : Family G X) (g : G) : toL2 μ F g = l2 μ (F g) := rfl

@[simps] def l2Linear : Family G X →ₗ[ℝ] (G →ᵇ Lp ℂ 2 μ) where
  toFun := toL2 μ
  map_add' F H := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_add (F g) (H g)
  map_smul' c F := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_smul c (F g)

variable [AddCommGroup G] (M : Amenable.Mean G)
def avg : Family G X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun F := M.vector (toL2 μ F)
  map_add' F H := by rw [← l2Linear_apply, map_add]; exact M.vector_add _ _
  map_smul' c F := by rw [← l2Linear_apply, map_smul]; exact M.vector_smul _ _

lemma avg_pair (F : Family G X) (h : Lp ℂ 2 μ) :
    inner ℝ (avg μ M F) h = M.map (Amenable.Mean.pairing (toL2 μ F) h) := M.vector_pair _ _

lemma avg_congr_ae {F H : Family G X} (he : ∀ g, F g =ᵐ[μ] H g) : avg μ M F = avg μ M H := by
  change M.vector (toL2 μ F) = M.vector (toL2 μ H)
  congr 1
  apply BoundedContinuousFunction.ext
  intro g
  exact (l2_eq_iff μ _ _).mpr (he g)

omit [TopologicalSpace G] [DiscreteTopology G]
variable [AddAction G X] [MeasurableConstVAdd G X]
def orbit (φ : G →+ G) (f : Func X) : Family G X :=
  ⟨fun g => act (φ g) f, BoundedMeasurable.bound f,
    fun g x => BoundedMeasurable.norm_le_bound f (φ g +ᵥ x)⟩
@[simp] lemma orbit_apply (φ : G →+ G) (f : Func X) (g : G) : orbit φ f g = act (φ g) f := rfl
lemma orbit_add (φ : G →+ G) (f h : Func X) : orbit φ (f+h) = orbit φ f + orbit φ h := rfl
lemma orbit_sub (φ : G →+ G) (f h : Func X) : orbit φ (f-h) = orbit φ f - orbit φ h := rfl

end Family
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def tensor (f : Func X) (g : Func Y) : Func (X×Y) :=
  comp f Prod.fst measurable_fst * comp g Prod.snd measurable_snd
@[simp] lemma tensor_apply (f : Func X) (g : Func Y) (z : X×Y) : tensor f g z = f z.1 * g z.2 := rfl
lemma tensor_mul (f h : Func X) (g k : Func Y) : tensor (f*h) (g*k) = tensor f g * tensor h k := by
  ext z; simp only [tensor_apply, mul_apply]; ring
lemma tensor_conj (f : Func X) (g : Func Y) : tensor (bmConj f) (bmConj g) = bmConj (tensor f g) := by
  ext z; simp only [tensor_apply, conj_apply, star_mul']

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

lemma integral_law (f : Func (X×X)) :
    ∫ z, f z ∂(RelativeProduct.law μ q hq) =
      ∫ y, (∫ z, f z ∂(condDistrib id q μ y).prod (condDistrib id q μ y)) ∂μ.map q := by
  have hi := integrable (RelativeProduct.law μ q hq) f
  rw [RelativeProduct.law_eq_mixture, Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa only [Kernel.const_apply, Kernel.prod_apply, ← Measure.comp_eq_comp_const_apply,
    ← RelativeProduct.law_eq_mixture μ q hq] using he

lemma integral_tensor (f g : Func X) :
    ∫ z, tensor f g z ∂(RelativeProduct.law μ q hq) =
      ∫ y, conditional μ q f y * conditional μ q g y ∂μ.map q := by
  rw [integral_law]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => integral_prod_mul f g)

lemma integral_tensor_self (f : Func X) :
    ∫ z, tensor f (bmConj f) z ∂(RelativeProduct.law μ q hq) =
      (‖l2 (μ.map q) (conditional μ q f)‖^2 : ℝ) := by
  rw [integral_tensor, norm_l2_sq]
  simp only [conditional, expect_conj, conj_apply]
  change (∫ y, conditional μ q f y * star (conditional μ q f y) ∂μ.map q) = _
  calc
    _ = ∫ y, ((‖conditional μ q f y‖^2 : ℝ) : ℂ) ∂μ.map q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => (Complex.mul_conj _).trans
        (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq _))
    _ = _ := integral_complex_ofReal

lemma inner_tensor (v w : Func X) :
    inner ℝ (l2 (RelativeProduct.law μ q hq) (tensor w (bmConj w)))
      (l2 (RelativeProduct.law μ q hq) (tensor (bmConj v) v)) =
      ‖l2 (μ.map q) (conditional μ q (v*w))‖^2 := by
  rw [real_inner_comm, inner_l2]
  have he : (fun z : X×X => inner ℝ (tensor (bmConj v) v z) (tensor w (bmConj w) z)) =
      (fun z => (tensor (v*w) (bmConj (v*w)) z).re) := by
    funext z
    simp only [Complex.inner, tensor_apply, conj_apply, mul_apply, starRingEnd_apply, star_mul', star_star]
    congr 1
    ring
  rw [he]
  change (∫ z, RCLike.re (tensor (v*w) (bmConj (v*w)) z) ∂(RelativeProduct.law μ q hq)) = _
  rw [integral_re (integrable _ (tensor (v*w) (bmConj (v*w)))), integral_tensor_self]
  rfl

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable.Koopman
variable {G X E : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

lemma vector_orbit_hom_zero (M : Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v : Lp E 2 μ) (hv : ∫ x, v x ∂μ = 0) :
    M.vector (Mean.orbit (fun g => action (E := E) μ (φ g)) v) = 0 := by
  apply M.vector_orbit_eq_zero _ (fun g h v => by rw [map_add, action_add]) v
  intro w hw
  apply inner_fixed_zero (G := G) (E := E) μ v hv w
  intro g
  obtain ⟨h, rfl⟩ := hs g
  exact hw h
end EuclideanFiveColor.Amenable.Koopman
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
instance product_measurable_vadd : MeasurableConstVAdd G (X×X) where
  measurable_const_vadd g := (measurable_const_vadd (α := X) g).prodMap (measurable_const_vadd g)
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

def pairSequence (φ : G →+ G) (v w : Func X) : G →ᵇ Lp ℂ 2 (μ.map q) :=
  letI : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => l2 (μ.map q) (conditional μ q (v * act (φ g) w)))
    continuous_of_discreteTopology (bound v * bound w) (fun g => by
      apply l2_norm_le
      intro y
      apply expect_bound
      intro x
      dsimp only [mul_apply, act_apply]
      rw [norm_mul]
      exact mul_le_mul (norm_le_bound v x) (norm_le_bound w _) (norm_nonneg _) (bound v).coe_nonneg)

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma pairSequence_apply (φ : G →+ G) (v w : Func X) (g : G) :
    pairSequence μ q hq φ v w g = l2 (μ.map q) (conditional μ q (v*act (φ g) w)) := rfl

omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X] in
lemma tensor_act (g : G) (v w : Func X) :
    tensor (act g v) (act g w) = act g (tensor v w) := rfl

variable [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]

include hq in
lemma pair_mean_sq_zero (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v w : Func X) (hw : l2 (μ.map q) (conditional μ q w) = 0) :
    M.map (Amenable.Mean.squareNorm (pairSequence μ q hq φ v w)) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  let t := tensor w (bmConj w)
  have iw : ∫ z, l2 ρ t z ∂ρ = 0 := by
    rw [integral_l2, integral_tensor_self, hw]
    simp
  let U := fun g : G => Amenable.Koopman.action (E := ℂ) ρ (φ g)
  have hv := Amenable.Koopman.vector_orbit_hom_zero ρ M φ hs (l2 ρ t) iw
  let a := l2 ρ (tensor (bmConj v) v)
  have he : Amenable.Mean.squareNorm (pairSequence μ q hq φ v w) =
      Amenable.Mean.pairing (Amenable.Mean.orbit U (l2 ρ t)) a := by
    ext g
    rw [Amenable.Mean.squareNorm_apply]
    change ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖^2 =
      inner ℝ (Amenable.Koopman.action ρ (φ g) (l2 ρ t)) a
    dsimp only [t, a]
    rw [← l2_act, ← tensor_act, act_conj]
    exact (inner_tensor μ q hq v (act (φ g) w)).symm
  rw [he, ← M.vector_pair]
  change inner ℝ (M.vector (Amenable.Mean.orbit U (l2 ρ t))) a = 0
  rw [hv, inner_zero_left]

end EuclideanFiveColor.BoundedMeasurable

namespace EuclideanFiveColor.AlgebraReplacement

section
variable {ι R A H : Type*} [DecidableEq ι] [Semiring R] [CommRing A]
  [Module R A] [AddCommMonoid H] [Module R H]

lemma mixed_prod (s t : Finset ι) (ht : t ⊆ s) (f g : ι → A) :
    (∏ i ∈ t, f i) * (∏ i ∈ s\t, g i) = ∏ i ∈ s, if i∈t then f i else g i := by
  have he : s.filter (fun i => i ∈ t) = t := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨ht h,h⟩⟩
  have hn : s.filter (fun i => ¬ i∈t) = s\t := by ext i; simp
  rw [Finset.prod_ite, he, hn]

lemma linear_prod_replace (L : A →ₗ[R] H) (s : Finset ι) (f g : ι → A)
    (h : ∀ t ∈ s.powerset, t ≠ ∅ →
      L ((∏ i ∈ t, (f i - g i)) * ∏ i ∈ s\t, g i) = 0) :
    L (∏ i ∈ s, f i) = L (∏ i ∈ s, g i) := by
  have he := Finset.prod_add (fun i => f i - g i) g s
  simp only [sub_add_cancel] at he
  rw [he, map_sum]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro t ht hn
    exact h t ht hn
  · simp
end
variable {ι A H : Type*} [DecidableEq ι] [CommRing A] [AddCommMonoid H]
lemma add_prod_replace (L : A →+ H) (s : Finset ι) (f g : ι → A)
    (h : ∀ t ∈ s.powerset, t ≠ ∅ →
      L ((∏ i ∈ t, (f i - g i)) * ∏ i ∈ s\t, g i) = 0) :
    L (∏ i ∈ s, f i) = L (∏ i ∈ s, g i) := by
  have he := Finset.prod_add (fun i => f i - g i) g s
  simp only [sub_add_cancel] at he
  rw [he, map_sum]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro t ht hn
    exact h t ht hn
  · simp
end EuclideanFiveColor.AlgebraReplacement

end

end OAI
