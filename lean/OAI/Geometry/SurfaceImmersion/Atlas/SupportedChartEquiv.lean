import OAI.Geometry.SurfaceImmersion.Atlas.SupportedChartTransport

namespace OAI

/-! Invertible local-chart transport on supported fields and their linear
operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ A] in
lemma chartPull_zero (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set A) → f (e x) = 0 := by
  intro x hx hn
  apply f.zero_on_compl
  rintro ⟨z,hz,hez⟩
  have hzx : z = x := by
    have hh := congrArg e.symm hez
    simpa only [e.left_inv (hK hz), e.left_inv hx] using hh
  exact hn (hzx ▸ hz)

def chartPull (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    SupportedField (F := F) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (f.contDiff.comp_contDiffOn he) (chartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed (chartPull_zero e K hK f)))

@[simp] lemma chartPull_apply (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) (x : A) :
    chartPull e he K hK f x = e.source.indicator (f ∘ e) x := rfl

lemma chartPull_push (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    chartPull e he K hK (chartPush e hi K hK f) = f := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ e.source
  · rw [chartPull_apply, Set.indicator_of_mem hx]
    exact chartPush_eval_source e hi K hK f hx
  · rw [chartPull_apply, Set.indicator_of_notMem hx]
    exact (f.zero_on_compl (fun hk => hx (hK hk))).symm

lemma chartPush_pull (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    chartPush e hi K hK (chartPull e he K hK f) = f := by
  apply DFunLike.ext
  intro y
  by_cases hy : y ∈ e.target
  · rw [chartPush_apply, Set.indicator_of_mem hy]
    change chartPull e he K hK f (e.symm y) = f y
    rw [chartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    simp only [Function.comp_apply, e.right_inv hy]
  · rw [chartPush_apply, Set.indicator_of_notMem hy]
    exact (f.zero_on_compl (fun hk => hy (chartSupport_subset e K hK hk))).symm

def chartEquiv (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) :
    SupportedField (F := F) K ≃ₗ[ℝ] SupportedField (F := F) (chartSupport e K hK) where
  toFun := chartPush e hi K hK
  invFun := chartPull e he K hK
  left_inv := chartPull_push e he hi K hK
  right_inv := chartPush_pull e he hi K hK
  map_add' := (chartPushLM e hi K hK).map_add
  map_smul' := (chartPushLM e hi K hK).map_smul

lemma chartPull_bound (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) {s : ℝ≥0} {J : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (f : SupportedField (F := F) (chartSupport e K hK)) :
    supportedWeightedSeminorm K s m (chartPull e he K hK f) ≤
      (m.factorial : ℝ) * supportedWeightedSeminorm (chartSupport e K hK) s m f * J ^ m := by
  have hf := (weightedBound_of_supportedSeminorm s m f).restrict_open e.open_target
  have hb := hf.comp_coordinates e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hs hs1 hJ
    (apply_nonneg _ _) he f.contDiff.contDiffOn (fun _ hx => e.map_source hx) hderiv
  apply supportedSeminorm_le_of_weightedBound hs (by positivity)
  exact hb.indicator_of_support e.open_source K.isCompact.isClosed hK (by positivity)
    (chartPull_zero e K hK f)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
