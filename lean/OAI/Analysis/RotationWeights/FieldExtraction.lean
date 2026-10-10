import OAI.Analysis.RotationWeights.TracialAction

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
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
abbrev VectorL2 := Lp E 2 μ

def indicatorV2 (s : Set X) (hs : MeasurableSet s) : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).indicator hs).toLp (s.indicator f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [((Lp.memLp (f+g)).indicator hs).coeFn_toLp,
          ((Lp.memLp f).indicator hs).coeFn_toLp, ((Lp.memLp g).indicator hs).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add (((Lp.memLp f).indicator hs).toLp _)
            (((Lp.memLp g).indicator hs).toLp _)] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1,h5,h2,h3]
        by_cases hx : x∈s
        · simp only [indicator_of_mem hx, h4]
        · simp only [indicator_of_notMem hx, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [((Lp.memLp (c•f)).indicator hs).coeFn_toLp,
          ((Lp.memLp f).indicator hs).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).indicator hs).toLp _)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply] at h3 h4
        simp only [RingHom.id_apply]
        rw [h1,h4,h2]
        by_cases hx : x∈s
        · simp only [indicator_of_mem hx, h3]
        · simp only [indicator_of_notMem hx, smul_zero] }
    1 (by
      intro f
      change ‖((Lp.memLp f).indicator hs).toLp (s.indicator f)‖ ≤ 1*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [((Lp.memLp f).indicator hs).coeFn_toLp] with x hx
      rw [hx, one_mul]
      by_cases hxs : x∈s
      · simp only [indicator_of_mem hxs, le_refl]
      · simp only [indicator_of_notMem hxs, norm_zero, norm_nonneg])

lemma indicatorV2_coe (s : Set X) (hs : MeasurableSet s) (f : VectorL2 (E := E) μ) :
    indicatorV2 μ s hs f =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

lemma vectorL2_norm_sq_integral (f : VectorL2 (E := E) μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

lemma indicatorV2_norm_sq (s : Set X) (hs : MeasurableSet s) (f : VectorL2 (E := E) μ) :
    ‖indicatorV2 μ s hs f‖^2 = ∫ x in s, ‖f x‖^2 ∂μ := by
  rw [vectorL2_norm_sq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorV2_coe μ s hs f] with x hx
  rw [hx]
  by_cases hxs : x∈s <;> simp [hxs]

variable [IsFiniteMeasure μ]

lemma commutes_indicator_pointwise_bound (A : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ)
    (hA : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) (v : E) :
    ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖ ≤ ‖A‖*‖v‖ := by
  have hi : Integrable (fun x ↦ ‖(A (Lp.const 2 μ v)) x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have he : ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖^2 ≤ (‖A‖*‖v‖)^2 := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro s hs _
    rw [← indicatorV2_norm_sq μ s hs]
    have hc : indicatorV2 μ s hs (A (Lp.const 2 μ v)) =
        A (indicatorV2 μ s hs (Lp.const 2 μ v)) :=
      (congrArg (fun B : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ ↦ B (Lp.const 2 μ v)) (hA s hs)).symm
    rw [hc]
    calc
      _ ≤ (‖A‖ * ‖indicatorV2 μ s hs (Lp.const 2 μ v)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) _
      _ = ‖A‖^2 * ∫ x in s, ‖(Lp.const 2 μ v) x‖^2 ∂μ := by
        rw [mul_pow, indicatorV2_norm_sq]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_const 2 μ v)] with x hx
        rw [hx]
        simp only [Function.const_apply, mul_pow]
  filter_upwards [he] with x hx
  nlinarith [norm_nonneg ((A (Lp.const 2 μ v)) x), mul_nonneg (norm_nonneg A) (norm_nonneg v)]

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance rationalNormedSpace : NormedSpace ℚ E := NormedSpace.restrictScalars ℚ ℂ E
local instance rationalTower : IsScalarTower ℚ ℂ E := IsScalarTower.restrictScalars ℚ ℂ E

def complexOfRat (T : E →L[ℚ] E) (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) : E →L[ℂ] E where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro c v
    have hr : ∀ a : ℝ, T ((a : ℂ) • v) = (a : ℂ) • T v := by
      intro a
      refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on a ?_ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · intro q
        simp only [Complex.ofReal_ratCast, Rat.cast_smul_eq_qsmul ℂ q]
        exact T.map_smul q v
    have hrI : T ((c.im : ℂ) • (Complex.I • v)) = (c.im : ℂ) • T (Complex.I • v) := by
      refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on c.im ?_ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · intro q
        simp only [Complex.ofReal_ratCast, Rat.cast_smul_eq_qsmul ℂ q]
        exact T.map_smul q (Complex.I • v)
    rw [← Complex.re_add_im c, add_smul, map_add, mul_smul, hr, hrI, hI]
    simp only [RingHom.id_apply, add_smul, mul_smul]
  cont := T.continuous

lemma complexOfRat_apply (T : E →L[ℚ] E) (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) (v : E) :
    complexOfRat T hI v = T v := rfl

lemma complexOfRat_norm_le (T : E →L[ℚ] E) (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) :
    ‖complexOfRat T hI‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact T.le_opNorm

def rationalCore (v : ℕ → E) : Submodule ℚ E :=
  Submodule.span ℚ (range v ∪ range (fun n ↦ Complex.I • v n))

instance rationalCore_countable (v : ℕ → E) : Countable (rationalCore v) := by
  unfold rationalCore
  have heq : range v ∪ range (fun n ↦ Complex.I • v n) =
      range (Sum.elim v (fun n ↦ Complex.I • v n)) := by
    ext x
    simp
  rw [heq]
  infer_instance

lemma rationalCore_I (v : ℕ → E) (u : rationalCore v) :
    Complex.I • (u : E) ∈ rationalCore v := by
  apply Submodule.span_induction (p := fun x _ ↦ Complex.I • x ∈ rationalCore v)
    _ _ _ _ u.property
  · intro x hx
    rcases hx with ⟨n,rfl⟩ | ⟨n,rfl⟩
    · exact Submodule.subset_span (Or.inr ⟨n,rfl⟩)
    · rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
      exact (rationalCore v).neg_mem (Submodule.subset_span (Or.inl ⟨n,rfl⟩))
  · simp only [smul_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy
    simpa only [smul_add] using (rationalCore v).add_mem hx hy
  · intro a x _ hx
    rw [smul_comm]
    exact (rationalCore v).smul_mem a hx

lemma rationalCore_dense (v : ℕ → E) (hv : DenseRange v) :
    DenseRange (rationalCore v).subtypeL := by
  intro x
  apply closure_mono (s := range v) _ (hv x)
  rintro _ ⟨n,rfl⟩
  exact ⟨⟨v n, Submodule.subset_span (Or.inl ⟨n,rfl⟩)⟩,rfl⟩

variable {X : Type uX} [MeasurableSpace X] (μ : Measure X)
  [CompleteSpace E] [IsFiniteMeasure μ]

theorem extract_bounded_field (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hb : ∀ v : E, ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖ ≤ ‖A‖ * ‖v‖)
    (v : ℕ → E) (hv : DenseRange v) :
    ∃ T : X → (E →L[ℂ] E), (∀ x, ‖T x‖ ≤ ‖A‖) ∧
      (∀ u : E, ∀ᵐ x ∂μ, T x u = (A (Lp.const 2 μ u)) x) := by
  classical
  let D := rationalCore v
  let G : E →L[ℂ] Lp E 2 μ := A.comp (Lp.constL 2 μ ℂ)
  have hG (u : E) : G u = A (Lp.const 2 μ u) := rfl
  have hgadd (u w : E) : (G (u+w) : X → E) =ᵐ[μ] fun x ↦ G u x + G w x := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hgsmul (a : ℂ) (u : E) : (G (a•u) : X → E) =ᵐ[μ] fun x ↦ a • G u x := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hgqsmul (a : ℚ) (u : E) : (G (a•u) : X → E) =ᵐ[μ] fun x ↦ a • G u x := by
    simpa only [Rat.cast_smul_eq_qsmul] using hgsmul (a : ℂ) u
  let Good : X → Prop := fun x ↦
    (∀ u w : D, G ((u:E)+(w:E)) x = G u x + G w x) ∧
    (∀ a : ℚ, ∀ u : D, G (a • (u:E)) x = a • G u x) ∧
    (∀ u : D, ‖G u x‖ ≤ ‖A‖ * ‖(u:E)‖) ∧
    (∀ u : D, G (Complex.I • (u:E)) x = Complex.I • G u x)
  have hGood : ∀ᵐ x ∂μ, Good x := by
    have h1 := ae_all_iff.mpr (fun u : D ↦ ae_all_iff.mpr (fun w : D ↦ hgadd u w))
    have h2 := ae_all_iff.mpr (fun a : ℚ ↦ ae_all_iff.mpr (fun u : D ↦ hgqsmul a u))
    have h3 := ae_all_iff.mpr (fun u : D ↦ hb (u:E))
    have h4 := ae_all_iff.mpr (fun u : D ↦ hgsmul Complex.I u)
    filter_upwards [h1,h2,h3,h4] with x h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  let TD : X → (D →L[ℚ] E) := fun x ↦ if hx : Good x then
    LinearMap.mkContinuous
      { toFun := fun u ↦ G (u:E) x
        map_add' := fun u w ↦ hx.1 u w
        map_smul' := fun a u ↦ hx.2.1 a u }
      ‖A‖ hx.2.2.1
    else 0
  let R : X → (E →L[ℚ] E) := fun x ↦ (TD x).extend D.subtypeL
  have hd : DenseRange D.subtypeL := rationalCore_dense v hv
  have hu : IsUniformInducing D.subtypeL := isometry_subtype_coe.isUniformInducing
  have hTDnorm (x : X) : ‖TD x‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    dsimp only [TD]
    split_ifs with hx
    · exact hx.2.2.1 u
    · simp only [zero_apply, norm_zero]
      positivity
  have hRnorm (x : X) : ‖R x‖ ≤ ‖A‖ := by
    have h := ContinuousLinearMap.opNorm_extend_le (TD x) (N := 1) hd
      (fun u : D ↦ by simp)
    have h' : ‖R x‖ ≤ ‖TD x‖ := by simpa only [NNReal.coe_one, one_mul] using h
    exact h'.trans (hTDnorm x)
  have hReq (x : X) (hx : Good x) (u : D) : R x (u:E) = G u x := by
    change (TD x).extend D.subtypeL (D.subtypeL u) = _
    rw [ContinuousLinearMap.extend_eq _ hd hu]
    simp only [TD, dite_eq_left hx]
    rfl
  have hRI (x : X) (u : E) : R x (Complex.I • u) = Complex.I • R x u := by
    refine hd.induction_on u ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro w
      by_cases hx : Good x
      · rw [show D.subtypeL w = (w:E) from rfl]
        let iw : D := ⟨Complex.I • (w:E), rationalCore_I v w⟩
        rw [show Complex.I • (w:E) = (iw:E) from rfl, hReq x hx iw, hReq x hx w]
        exact hx.2.2.2 w
      · have hz : TD x = 0 := by simp only [TD, dite_eq_right hx]
        simp only [R, hz, ContinuousLinearMap.extend_zero hd hu,
          zero_apply, smul_zero]
  let T : X → (E →L[ℂ] E) := fun x ↦ complexOfRat (R x) (hRI x)
  refine ⟨T, fun x ↦ (complexOfRat_norm_le _ _).trans (hRnorm x), ?_⟩
  intro u
  have hdelta (w : D) : ∀ᵐ x ∂μ, ‖G w x - G u x‖ ≤ ‖A‖ * ‖(w:E)-u‖ := by
    have he : (G ((w:E)-u) : X → E) =ᵐ[μ] fun x ↦ G w x - G u x := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [he, hb ((w:E)-u)] with x hx hb
    rw [← hx]
    exact hb
  filter_upwards [hGood, ae_all_iff.mpr hdelta] with x hx hdelta
  change R x u = G u x
  have hbound : ∀ z : E, ‖R x z - G u x‖ ≤ ‖A‖ * ‖z-u‖ := by
    intro z
    refine hd.induction_on z ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro w
      rw [show D.subtypeL w = (w:E) from rfl, hReq x hx w]
      exact hdelta w
  have hzero := hbound u
  simpa only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] using hzero



end ContinuousCircleWeight

end

end OAI
