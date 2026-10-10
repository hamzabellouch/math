import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport
import OAI.Geometry.Immersion.ClosedSurface.CoordinateBounds

namespace OAI

/-! Transport smooth compactly supported fields through an actual local
coordinate homeomorphism. Extension by zero preserves the original support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The image compact set for the local coordinate system. -/
def chartSupport (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) : Compacts B :=
  ⟨e '' K, K.isCompact.image_of_continuousOn (e.continuousOn.mono hK)⟩

omit [NormedSpace ℝ A] [NormedSpace ℝ B] in
lemma chartSupport_subset (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) : (chartSupport e K hK : Set B) ⊆ e.target := by
  rintro _ ⟨x,hx,rfl⟩
  exact e.map_source (hK hx)

omit [NormedSpace ℝ B] in
lemma chartPush_zero (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    ∀ y ∈ e.target, y ∉ (chartSupport e K hK : Set B) → f (e.symm y) = 0 := by
  intro y hy hn
  apply f.zero_on_compl
  intro hx
  exact hn ⟨e.symm y,hx,e.right_inv hy⟩

def chartPush (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    SupportedField (F := F) (chartSupport e K hK) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
      (chartSupport_subset e K hK) (f.contDiff.comp_contDiffOn he) (chartPush_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset (chartSupport e K hK).isCompact.isClosed
      (chartPush_zero e K hK f)))

@[simp] lemma chartPush_apply (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) (y : B) :
    chartPush e he K hK f y = e.target.indicator (f ∘ e.symm) y := rfl

def chartPushLM (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) (chartSupport e K hK) where
  toFun := chartPush e he K hK
  map_add' f g := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;> simp [chartPush_apply, hy]
  map_smul' c f := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;> simp [chartPush_apply, hy]

lemma chartPush_eval_source (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K)
    {x : A} (hx : x ∈ e.source) : chartPush e he K hK f (e x) = f x := by
  rw [chartPush_apply, Set.indicator_of_mem (e.map_source hx)]
  simp only [Function.comp_apply, e.left_inv hx]

lemma chartPush_bound (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) {s : ℝ≥0} {J : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (f : SupportedField (F := F) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (chartPush e he K hK f) ≤
      (m.factorial : ℝ) * supportedWeightedSeminorm K s m f * J ^ m := by
  have hf := (weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source
  have hb := hf.comp_coordinates e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ
    (apply_nonneg _ _) he f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  apply supportedSeminorm_le_of_weightedBound hs (by positivity)
  exact hb.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (chartPush_zero e K hK f)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
