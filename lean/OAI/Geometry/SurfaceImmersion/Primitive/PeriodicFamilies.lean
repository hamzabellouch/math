import OAI.Geometry.SurfaceImmersion.Correction.FullPeriodicCorrector

namespace OAI

/-! Smooth periodic families used in the finite metric expansion. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable (A E : Type) [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def smoothFamilies : Submodule ℝ (A → C(Period, E)) where
  carrier := {F | ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : A × ℝ => (0 : E)); exact contDiff_const
  add_mem' := by
    intro F G hF hG
    change ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) at hF
    change ContDiff ℝ ∞ (fun z : A × ℝ => G z.1 (z.2 : Period)) at hG
    change ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period) + G z.1 (z.2 : Period))
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    change ContDiff ℝ ∞ (fun z : A × ℝ => c • F z.1 (z.2 : Period))
    exact contDiff_const.smul hF

def Family := ↥(smoothFamilies A E)

instance : AddCommGroup (Family A E) :=
  inferInstanceAs (AddCommGroup ↥(smoothFamilies A E))
instance : Module ℝ (Family A E) :=
  inferInstanceAs (Module ℝ ↥(smoothFamilies A E))

variable {A E}

namespace Family

def val (F : Family A E) : A → C(Period, E) := F.1

lemma smooth (F : Family A E) :
    ContDiff ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period)) := F.2

@[ext] lemma ext {F G : Family A E} (h : ∀ p t, F.val p t = G.val p t) : F = G := by
  apply Subtype.ext
  funext p
  exact ContinuousMap.ext (h p)

@[simp] lemma zero_apply (p : A) (t : Period) : (0 : Family A E).val p t = 0 := rfl
@[simp] lemma add_apply (F G : Family A E) (p : A) (t : Period) :
    (F + G).val p t = F.val p t + G.val p t := rfl
@[simp] lemma neg_apply (F : Family A E) (p : A) (t : Period) :
    (-F).val p t = -F.val p t := rfl
@[simp] lemma sub_apply (F G : Family A E) (p : A) (t : Period) :
    (F - G).val p t = F.val p t - G.val p t := rfl
@[simp] lemma smul_apply (c : ℝ) (F : Family A E) (p : A) (t : Period) :
    (c • F).val p t = c • F.val p t := rfl

@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (F : ι → Family A E)
    (p : A) (t : Period) : (∑ i ∈ s, F i).val p t = ∑ i ∈ s, (F i).val p t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

def slow (F : Family A E) (v : A) : Family A E :=
  ⟨slowDerivativeFamily F.val F.smooth v, slowDerivativeFamily_smooth F.val F.smooth v⟩

def angle (F : Family A E) : Family A E :=
  ⟨derivativeFamily F.val F.smooth, derivativeFamily_smooth F.val F.smooth⟩

@[simp] lemma slow_apply (F : Family A E) (v p : A) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := rfl

@[simp] lemma angle_apply (F : Family A E) (p : A) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := rfl

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def primitive (F : Family A E) (hm : ∀ p, average (F.val p) = 0) : Family A E :=
  ⟨primitiveFamily F.val F.smooth hm, primitiveFamily_smooth F.val F.smooth hm⟩

lemma primitive_angle (F : Family A E) (hm : ∀ p, average (F.val p) = 0) :
    (F.primitive hm).angle = F := by
  apply Subtype.ext
  exact derivativeFamily_primitiveFamily F.val F.smooth hm

lemma primitive_mean_zero (F : Family A E) (hm : ∀ p, average (F.val p) = 0) (p : A) :
    average ((F.primitive hm).val p) = 0 := primitiveFamily_mean_zero F.val F.smooth hm p

omit [CompleteSpace E] in
lemma slow_mean_zero (F : Family A E) (hm : ∀ p, average (F.val p) = 0) (v p : A) :
    average ((F.slow v).val p) = 0 := slowDerivativeFamily_mean_zero F.val F.smooth hm v p

def inner (F G : Family A E) : Family A ℝ :=
  ⟨fun p => ⟨fun t => Inner.inner ℝ (F.val p t) (G.val p t),
    (F.val p).continuous.inner (G.val p).continuous⟩, F.smooth.inner ℝ G.smooth⟩

omit [FiniteDimensional ℝ A] [CompleteSpace E] in
@[simp] lemma inner_apply (F G : Family A E) (p : A) (t : Period) :
    (F.inner G).val p t = Inner.inner ℝ (F.val p t) (G.val p t) := rfl

end Family

namespace Family

def constant (f : A → E) (hf : ContDiff ℝ ∞ f) : Family A E :=
  ⟨fun p => ContinuousMap.const Period (f p), hf.comp contDiff_fst⟩

@[simp] lemma constant_apply (f : A → E) (hf : ContDiff ℝ ∞ f) (p : A) (t : Period) :
    (constant f hf).val p t = f p := rfl

variable [FiniteDimensional ℝ A]

def mean (F : Family A ℝ) : Family A ℝ :=
  constant (fun p => average (F.val p)) (contDiff_average_joint F.smooth)

def fluct (F : Family A ℝ) : Family A ℝ := F - F.mean

@[simp] lemma mean_apply (F : Family A ℝ) (p : A) (t : Period) :
    F.mean.val p t = average (F.val p) := rfl

@[simp] lemma fluct_apply (F : Family A ℝ) (p : A) (t : Period) :
    F.fluct.val p t = fluctuation (F.val p) t := rfl

lemma fluct_mean_zero (F : Family A ℝ) (p : A) : average (F.fluct.val p) = 0 :=
  PeriodicCorrector.average_fluctuation (F.val p).continuous

lemma fluct_eq_zero_iff (F : Family A ℝ) : F.fluct = 0 ↔ F = F.mean := by
  exact sub_eq_zero

lemma mean_add (F G : Family A ℝ) : (F + G).mean = F.mean + G.mean := by
  ext p t
  exact average_add (F.val p).continuous (G.val p).continuous

lemma mean_smul (c : ℝ) (F : Family A ℝ) : (c • F).mean = c • F.mean := by
  ext p t
  exact average_const_smul c (F.val p)

lemma mean_mean (F : Family A ℝ) : F.mean.mean = F.mean := by
  ext p t
  exact average_const _

lemma fluct_add (F G : Family A ℝ) : (F + G).fluct = F.fluct + G.fluct := by
  simp only [fluct, mean_add]
  abel

lemma fluct_smul (c : ℝ) (F : Family A ℝ) : (c • F).fluct = c • F.fluct := by
  simp only [fluct, mean_smul, smul_sub]

lemma fluct_fluct (F : Family A ℝ) : F.fluct.fluct = F.fluct := by
  have hm : F.fluct.mean = 0 := by
    ext p t
    exact F.fluct_mean_zero p
  rw [fluct, hm, sub_zero]

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
