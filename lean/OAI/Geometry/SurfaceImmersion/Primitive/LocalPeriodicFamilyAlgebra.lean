import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFamilies

namespace OAI

/-! Algebra and support preservation for periodic families on an open domain. -/
noncomputable section

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {O : TopologicalSpace.Opens A} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_add_left (F G H : Family O E) : (F + G).inner H = F.inner H + G.inner H := by
  ext p hp t
  simp only [inner_apply, add_apply, _root_.inner_add_left]
lemma inner_add_right (F G H : Family O E) : F.inner (G + H) = F.inner G + F.inner H := by
  ext p hp t
  simp only [inner_apply, add_apply, _root_.inner_add_right]

lemma angle_zero_at (F : Family O E) {p : A} (hp : p ∈ O) (hz : F.val p = 0) :
    F.angle.val p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := F.angle_hasDerivAt hp x
  rw [hz] at hd
  exact hd.unique (hasDerivAt_const x 0)

lemma slow_zero_on (F : Family O E) {Z : Set A} (hZ : IsOpen Z)
    (hz : ∀ p ∈ Z, F.val p = 0) (v : A) {p : A} (hp : p ∈ O) (hpZ : p ∈ Z) :
    (F.slow v).val p = 0 := by
  have he : (F.slow v).val p = slowOn F.val O O.isOpen F.smooth v p := by
    ext t
    exact ofLocal_apply _ _ hp _
  rw [he]
  exact slowOn_zero_on _ _ _ _ hZ hz v hp hpZ

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def vectorMean (F : Family O E) : Family O E :=
  constant (fun p => average (F.val p)) (contDiffOn_average_joint O.isOpen F.smooth)

@[simp] lemma vectorMean_apply (F : Family O E) (p : A) (t : Period) :
    F.vectorMean.val p t = average (F.val p) := by
  by_cases hp : p ∈ O
  · exact constant_apply _ _ hp t
  · rw [F.vectorMean.outside hp, F.outside hp]
    change (0 : E) = average (fun _ => (0 : E))
    rw [average_const]

lemma centered_mean_zero (F : Family O E) (p : A) :
    average ((F - F.vectorMean).val p) = 0 := by
  change average (fun t => F.val p t - F.vectorMean.val p t) = 0
  simp only [vectorMean_apply]
  rw [average_sub (F.val p).continuous continuous_const, average_const, sub_self]

lemma primitive_zero_at (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    {p : A} (hp : p ∈ O) (hz : F.val p = 0) : (F.primitive hm).val p = 0 := by
  have he : (F.primitive hm).val p = primitiveOn F.val O O.isOpen F.smooth hm p := by
    ext t
    exact ofLocal_apply _ _ hp _
  rw [he]
  exact primitiveOn_zero_at _ _ _ _ _ hp hz

lemma primitive_mem (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    [FiniteDimensional ℝ E] (S : A → Submodule ℝ E)
    (hS : ∀ p ∈ O, ∀ t, F.val p t ∈ S p) {p : A} (hp : p ∈ O) (t : Period) :
    (F.primitive hm).val p t ∈ S p := by
  rw [primitive, ofLocal_apply _ _ hp]
  refine Quotient.inductionOn' t ?_
  intro x
  rw [primitiveOn_apply _ _ _ _ _ hp]
  exact PeriodicPrimitive.primitive_mem_submodule (S p)
    ((F.val p).continuous.comp (AddCircle.continuous_mk' 1)) (fun s => hS p hp (s : Period)) x

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] {O : TopologicalSpace.Opens A}

def mean (F : Family O ℝ) : Family O ℝ := F.vectorMean

def fluct (F : Family O ℝ) : Family O ℝ := F - F.mean

@[simp] lemma mean_apply (F : Family O ℝ) (p : A) (t : Period) :
    F.mean.val p t = average (F.val p) := vectorMean_apply F p t
@[simp] lemma fluct_apply (F : Family O ℝ) (p : A) (t : Period) :
    F.fluct.val p t = fluctuation (F.val p) t := by
  simp only [fluct, sub_apply, mean_apply, fluctuation]

lemma fluct_mean_zero (F : Family O ℝ) (p : A) : average (F.fluct.val p) = 0 := by
  change average (fun t => F.fluct.val p t) = 0
  simp only [fluct_apply]
  exact PeriodicCorrector.average_fluctuation (F.val p).continuous

lemma mean_add (F G : Family O ℝ) : (F + G).mean = F.mean + G.mean := by
  ext p hp t
  simp only [mean_apply, add_apply]
  exact average_add (F.val p).continuous (G.val p).continuous
lemma mean_smul (c : ℝ) (F : Family O ℝ) : (c • F).mean = c • F.mean := by
  ext p hp t
  simp only [mean_apply, smul_apply]
  exact average_const_smul c (F.val p)
lemma mean_mean (F : Family O ℝ) : F.mean.mean = F.mean := by
  ext p hp t
  simp only [mean_apply]
  change average (fun s => F.mean.val p s) = average (F.val p)
  simp only [mean_apply]
  exact average_const (average (F.val p))
lemma fluct_add (F G : Family O ℝ) : (F + G).fluct = F.fluct + G.fluct := by
  simp only [fluct, mean_add]
  abel
lemma fluct_smul (c : ℝ) (F : Family O ℝ) : (c • F).fluct = c • F.fluct := by
  simp only [fluct, mean_smul, smul_sub]
lemma fluct_fluct (F : Family O ℝ) : F.fluct.fluct = F.fluct := by
  have hm : F.fluct.mean = 0 := by
    ext p hp t
    simpa only [mean_apply, zero_apply] using F.fluct_mean_zero p
  rw [fluct, hm, sub_zero]
lemma fluct_zero_at (F : Family O ℝ) {p : A} (hz : F.val p = 0) : F.fluct.val p = 0 := by
  ext t
  simp only [fluct_apply, fluctuation, hz]
  change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
  rw [average_const, sub_self]

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
