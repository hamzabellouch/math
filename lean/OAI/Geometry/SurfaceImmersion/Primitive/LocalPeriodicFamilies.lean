import OAI.Geometry.SurfaceImmersion.Correction.LocalFullPeriodicCorrector

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def smoothFamilies : Submodule ℝ (A → C(Period, E)) where
  carrier := {F | ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))
    ((O : Set A) ×ˢ Set.univ) ∧ ∀ p, p ∉ O → F p = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    exact ⟨hF.add hG, fun p hp => by change F p + G p = 0; rw [hF0 p hp, hG0 p hp, add_zero]⟩
  smul_mem' := by
    rintro c F ⟨hF, hF0⟩
    exact ⟨contDiffOn_const.smul hF, fun p hp => by change c • F p = 0; rw [hF0 p hp, smul_zero]⟩

def Family := ↥(smoothFamilies O E)
instance : AddCommGroup (Family O E) := inferInstanceAs (AddCommGroup ↥(smoothFamilies O E))
instance : Module ℝ (Family O E) := inferInstanceAs (Module ℝ ↥(smoothFamilies O E))

variable {O E}
namespace Family

def val (F : Family O E) : A → C(Period, E) := F.1
lemma smooth (F : Family O E) :
    ContDiffOn ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period))
      ((O : Set A) ×ˢ Set.univ) := F.2.1
lemma outside (F : Family O E) {p : A} (hp : p ∉ O) : F.val p = 0 := F.2.2 p hp

@[ext] lemma ext {F G : Family O E} (h : ∀ p ∈ O, ∀ t, F.val p t = G.val p t) : F = G := by
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ O
  · exact ContinuousMap.ext (h p hp)
  · exact (F.outside hp).trans (G.outside hp).symm

@[simp] lemma zero_apply (p : A) (t : Period) : (0 : Family O E).val p t = 0 := rfl
@[simp] lemma add_apply (F G : Family O E) (p : A) (t : Period) :
    (F + G).val p t = F.val p t + G.val p t := rfl
@[simp] lemma sub_apply (F G : Family O E) (p : A) (t : Period) :
    (F - G).val p t = F.val p t - G.val p t := rfl
@[simp] lemma neg_apply (F : Family O E) (p : A) (t : Period) :
    (-F).val p t = -F.val p t := rfl
@[simp] lemma smul_apply (c : ℝ) (F : Family O E) (p : A) (t : Period) :
    (c • F).val p t = c • F.val p t := rfl
@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (F : ι → Family O E)
    (p : A) (t : Period) : (∑ i ∈ s, F i).val p t = ∑ i ∈ s, (F i).val p t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- Restrict a locally smooth family to the admissible domain. -/
def ofLocal (F : A → C(Period, E))
    (hF : ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) ((O : Set A) ×ˢ Set.univ)) :
    Family O E :=
  ⟨bundleOn (fun z : A × ℝ => F z.1 (z.2 : Period)) O O.isOpen hF
      (fun p _ => SmoothPeriodicCalculus.periodic_lift F p),
    bundleOn_smooth _ _ _ _ _, fun p hp => by simp [bundleOn, hp]⟩

@[simp] lemma ofLocal_apply (F : A → C(Period, E))
    (hF : ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) ((O : Set A) ×ˢ Set.univ))
    {p : A} (hp : p ∈ O) (t : Period) : (ofLocal F hF).val p t = F p t := by
  refine Quotient.inductionOn' t ?_
  intro x
  exact bundleOn_apply _ _ _ _ _ hp x

def angle (F : Family O E) : Family O E :=
  ofLocal (angleOn F.val O O.isOpen F.smooth) (angleOn_smooth _ _ _ _)

def slow (F : Family O E) (v : A) : Family O E :=
  ofLocal (slowOn F.val O O.isOpen F.smooth v) (slowOn_smooth _ _ _ _ _)

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

def inner (F G : Family O E) : Family O ℝ :=
  ⟨fun p => ⟨fun t => Inner.inner ℝ (F.val p t) (G.val p t),
      (F.val p).continuous.inner (G.val p).continuous⟩,
    F.smooth.inner ℝ G.smooth, fun p hp => by ext t; simp [F.outside hp, G.outside hp]⟩

@[simp] lemma inner_apply (F G : Family O E) (p : A) (t : Period) :
    (F.inner G).val p t = Inner.inner ℝ (F.val p t) (G.val p t) := rfl

def constant (f : A → E) (hf : ContDiffOn ℝ ∞ f O) : Family O E :=
  ofLocal (fun p => ContinuousMap.const Period (f p))
    (hf.comp contDiffOn_fst (fun _ hz => hz.1))

@[simp] lemma constant_apply (f : A → E) (hf : ContDiffOn ℝ ∞ f O)
    {p : A} (hp : p ∈ O) (t : Period) : (constant f hf).val p t = f p :=
  ofLocal_apply _ _ hp t

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def primitive (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) : Family O E :=
  ofLocal (primitiveOn F.val O O.isOpen F.smooth hm) (primitiveOn_smooth _ _ _ _ _)

lemma primitive_angle (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) :
    (F.primitive hm).angle = F := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := (F.primitive hm).angle_hasDerivAt hp x
  have he : (fun s : ℝ => (F.primitive hm).val p (s : Period)) =
      fun s : ℝ => primitiveOn F.val O O.isOpen F.smooth hm p (s : Period) := by
    funext s
    exact ofLocal_apply _ _ hp _
  rw [he] at hd
  exact hd.unique (primitiveOn_hasDerivAt _ _ _ _ _ hp x)

lemma primitive_mean_zero (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    {p : A} (hp : p ∈ O) : average ((F.primitive hm).val p) = 0 := by
  have he : (F.primitive hm).val p = primitiveOn F.val O O.isOpen F.smooth hm p := by
    ext t
    exact ofLocal_apply _ _ hp t
  rw [he]
  exact primitiveOn_mean_zero _ _ _ _ _ hp

omit [CompleteSpace E] in
lemma slow_mean_zero (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    (v : A) {p : A} (hp : p ∈ O) : average ((F.slow v).val p) = 0 := by
  have he : (F.slow v).val p = slowOn F.val O O.isOpen F.smooth v p := by
    ext t
    exact ofLocal_apply _ _ hp t
  rw [he]
  exact slowOn_mean_zero _ _ _ _ hm v hp

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
