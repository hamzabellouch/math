import OAI.Analysis.RotationWeights.FieldExtraction

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
 [NormedAddCommGroup E] [InnerProductSpace ℂ E]
lemma fieldMulL2_indicator (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    fieldMulL2 μ T hT C hC (indicatorV2 μ s hs f) =
      indicatorV2 μ s hs (fieldMulL2 μ T hT C hC f) := by
  apply Lp.ext
  filter_upwards [fieldMulL2_coe μ T hT C hC (indicatorV2 μ s hs f),
    indicatorV2_coe μ s hs f, indicatorV2_coe μ s hs (fieldMulL2 μ T hT C hC f),
    fieldMulL2_coe μ T hT C hC f] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simpa only [indicator_of_mem hx] using h4.symm
  · simp only [indicator_of_notMem hx, map_zero]

variable [IsFiniteMeasure μ]

lemma indicatorConstLp_eq_indicatorV2 (c : E) (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    indicatorConstLp 2 hs hμs c = indicatorV2 μ s hs (Lp.const 2 μ c) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c),
    indicatorV2_coe μ s hs (Lp.const 2 μ c), Lp.coeFn_const 2 μ c] with x h1 h2 h3
  rw [h1,h2]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx, h3, Function.const_apply]
  · simp only [indicator_of_notMem hx]

theorem commutes_indicators_decomposable [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) :
    ∃ T : X → (E →L[ℂ] E), (∀ x, ‖T x‖ ≤ ‖A‖) ∧
      (∀ u : E, AEStronglyMeasurable (fun x ↦ T x u) μ) ∧
      (∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  obtain ⟨T,hT,heq⟩ := extract_bounded_field μ A
    (commutes_indicator_pointwise_bound μ A hA) v hv
  have hm (u : E) : AEStronglyMeasurable (fun x ↦ T x u) μ :=
    (Lp.aestronglyMeasurable (A (Lp.const 2 μ u))).congr (EventuallyEq.symm (heq u))
  let B := fieldMulL2 μ T hm ‖A‖ (Eventually.of_forall hT)
  have hconst (u : E) : B (Lp.const 2 μ u) = A (Lp.const 2 μ u) := by
    apply Lp.ext
    filter_upwards [fieldMulL2_coe μ T hm ‖A‖ (Eventually.of_forall hT) (Lp.const 2 μ u),
      Lp.coeFn_const 2 μ u, heq u] with x h1 h2 h3
    rw [h1,h2]
    exact h3
  have hAB : A = B := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.induction (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun f ↦ A f = B f) _ _ _ f
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_indicatorV2 μ c s hs]
      change A _ = fieldMulL2 μ T hm ‖A‖ (Eventually.of_forall hT) _
      rw [fieldMulL2_indicator]
      change A _ = indicatorV2 μ s hs (B (Lp.const 2 μ c))
      rw [hconst]
      exact congrArg (fun F : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ F (Lp.const 2 μ c)) (hA s hs)
    · intro f g _ _ _ hf hg
      simp only [map_add,hf,hg]
    · exact isClosed_eq A.continuous B.continuous
  refine ⟨T,hT,hm,fun f ↦ ?_⟩
  rw [hAB]
  exact fieldMulL2_coe μ T hm ‖A‖ (Eventually.of_forall hT) f
end

section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_indicatorV2 (s : Set X) (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    inner ℂ f (indicatorV2 μ s hs g) = ∫ x in s, inner ℂ (f x) (g x) ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorV2_coe μ s hs g] with x hx
  rw [hx]
  by_cases hxs : x∈s <;> simp [hxs]

variable [IsFiniteMeasure μ]

lemma decomposable_const (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (T : X → (E →L[ℂ] E))
    (hA : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) (u : E) :
    ∀ᵐ x ∂μ, (A (Lp.const 2 μ u)) x = T x u := by
  filter_upwards [hA (Lp.const 2 μ u), Lp.coeFn_const 2 μ u] with x h1 h2
  simpa only [h2,Function.const_apply] using h1

omit [IsFiniteMeasure μ] in
lemma ae_field_eq_of_dense [TopologicalSpace.SeparableSpace E]
    (T R : X → (E →L[ℂ] E)) (h : ∀ u, ∀ᵐ x ∂μ, T x u = R x u) :
    ∀ᵐ x ∂μ, T x = R x := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  have hh : ∀ᵐ x ∂μ, ∀ n : ℕ, T x (v n) = R x (v n) := ae_all_iff.mpr (fun n ↦ h (v n))
  filter_upwards [hh] with x hx
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (T x).continuous (R x).continuous (funext hx))

omit [IsFiniteMeasure μ] in
lemma decomposable_mul (A B : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (T R : X → (E →L[ℂ] E))
    (hA : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hB : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (B f) x = R x (f x))
    (f : Lp E 2 μ) : ∀ᵐ x ∂μ, ((A*B) f) x = (T x*R x) (f x) := by
  filter_upwards [hA (B f),hB f] with x h1 h2
  simpa only [mul_apply_eq_comp,h2] using h1

lemma decomposable_eq [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T R : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hR : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = R x (f x)) :
    ∀ᵐ x ∂μ, T x = R x := by
  apply ae_field_eq_of_dense μ T R
  intro u
  exact EventuallyEq.trans (EventuallyEq.symm (decomposable_const μ A T hT u))
    (decomposable_const μ A R hR u)

lemma decomposable_idempotent [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) (hA : A*A=A) :
    ∀ᵐ x ∂μ, T x*T x=T x := by
  apply decomposable_eq μ A (fun x ↦ T x*T x) T _ hT
  intro f
  simpa only [hA] using decomposable_mul μ A A T T hT hT f

lemma decomposable_selfAdjoint [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hc : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) (hA : IsSelfAdjoint A) :
    ∀ᵐ x ∂μ, IsSelfAdjoint (T x) := by
  have hsymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hinner (u v : E) : ∀ᵐ x ∂μ, inner ℂ (T x u) v = inner ℂ u (T x v) := by
    let fu := Lp.const 2 μ u
    let fv := Lp.const 2 μ v
    have he : (fun x ↦ inner ℂ ((A fu) x) (fv x)) =ᵐ[μ]
        (fun x ↦ inner ℂ (fu x) ((A fv) x)) := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L2.integrable_inner _ _)
        (L2.integrable_inner _ _)
      intro s hs _
      rw [← inner_indicatorV2 μ s hs, ← inner_indicatorV2 μ s hs]
      change inner ℂ (A.toLinearMap fu) _ = _
      rw [hsymmetric]
      have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ B fv) (hc s hs)
      exact congrArg (inner ℂ fu) hcomm
    filter_upwards [he,decomposable_const μ A T hT u,decomposable_const μ A T hT v,
      Lp.coeFn_const 2 μ u,Lp.coeFn_const 2 μ v] with x h1 h2 h3 h4 h5
    change inner ℂ ((A fu) x) (fv x) = inner ℂ (fu x) ((A fv) x) at h1
    simpa only [fu,fv,h2,h3,h4,h5,Function.const_apply] using h1
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  have hh : ∀ᵐ x ∂μ, ∀ n m : ℕ, inner ℂ (T x (v n)) (v m) = inner ℂ (v n) (T x (v m)) :=
    ae_all_iff.mpr (fun n ↦ ae_all_iff.mpr (fun m ↦ hinner (v n) (v m)))
  filter_upwards [hh] with x hx
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u w
  change inner ℂ (T x u) w = inner ℂ u (T x w)
  refine hv.induction_on₂ ?_ hx u w
  exact isClosed_eq (by fun_prop) (by fun_prop)
end

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def shiftedL2 (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E) :
    Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (S.compLpL 2 μ).comp (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap

lemma shiftedL2_coe (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (f : Lp E 2 μ) : shiftedL2 μ σ hσ S f =ᵐ[μ] fun x ↦ S (f (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ f),
    Lp.coeFn_compMeasurePreserving f hσ] with x h1 h2
  exact h1.trans (congrArg S h2)

variable [IsFiniteMeasure μ]
lemma shiftedL2_const (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (u : E) : shiftedL2 μ σ hσ S (Lp.const 2 μ u) = Lp.const 2 μ (S u) := by
  apply Lp.ext
  filter_upwards [shiftedL2_coe μ σ hσ S (Lp.const 2 μ u),
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ u),
    Lp.coeFn_const 2 μ (S u)] with x h1 h2 h3
  simp only [h1,h2,h3,Function.const_apply]

lemma decomposable_covariance [TopologicalSpace.SeparableSpace E]
    (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hAS : A * shiftedL2 μ σ hσ S = shiftedL2 μ σ hσ S * A) :
    ∀ᵐ x ∂μ, T x * S = S * T (σ x) := by
  apply ae_field_eq_of_dense μ
  intro u
  have he : A (Lp.const 2 μ (S u)) = shiftedL2 μ σ hσ S (A (Lp.const 2 μ u)) := by
    have := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ B (Lp.const 2 μ u)) hAS
    simpa only [mul_apply_eq_comp,shiftedL2_const] using this
  filter_upwards [decomposable_const μ A T hT (S u),
    shiftedL2_coe μ σ hσ S (A (Lp.const 2 μ u)),
    hσ.quasiMeasurePreserving.ae (decomposable_const μ A T hT u)] with x h1 h2 h3
  change T x (S u) = S (T (σ x) u)
  rw [← h1,he,h2,h3]



end ContinuousCircleWeight

end

end OAI
