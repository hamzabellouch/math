import OAI.Analysis.KadisonKastler.RegularCoreRepresentation
import OAI.Analysis.KadisonKastler.RegularCoreInvariant
import OAI.Analysis.KadisonKastler.DirectIntegralConjugacy

namespace OAI

/-! # Bounded field multiplication and constant translation-fixed fields

Bounded measurable operator fields act on the actual vector-valued `L²`
space. Finite-measure indicator tests recover their coefficients, so this
action is faithful modulo almost-everywhere equality. A decomposable
operator commuting with every real translation is a constant operator.
No decomposability assertion for an arbitrary operator is assumed here.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem regularField_memLp (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    MemLp (fun t => F t (f t)) 2 μ := by
  apply ((Lp.memLp f).norm.const_mul C).mono'
    (aestronglyMeasurable_field_apply F hF f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with t ht
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

def regularFieldApply (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) : Lp H 2 μ :=
  (regularField_memLp μ F hF C hC f).toLp _

omit [CompleteSpace H] in
theorem regularFieldApply_ae (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    regularFieldApply μ F hF C hC f =ᵐ[μ] fun t => F t (f t) :=
  MemLp.coeFn_toLp _

omit [CompleteSpace H] in
theorem norm_regularFieldApply_le (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (f : Lp H 2 μ) :
    ‖regularFieldApply μ F hF C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [regularFieldApply_ae μ F hF C hC f, hC] with t ht hnorm
  rw [ht]
  exact ((F t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Multiplication by an essentially bounded, strongly measurable
operator field, as a genuine bounded operator. -/
def regularFieldOperator (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  LinearMap.mkContinuous
    { toFun := regularFieldApply μ F hF C hC
      map_add' f g := by
        apply Lp.ext
        filter_upwards [regularFieldApply_ae μ F hF C hC (f + g),
          regularFieldApply_ae μ F hF C hC f, regularFieldApply_ae μ F hF C hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (regularFieldApply μ F hF C hC f)
            (regularFieldApply μ F hF C hC g)] with t hfg hf hg ha hb
        rw [hfg, hb, ha]
        simp only [Pi.add_apply]
        rw [hf, hg, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [regularFieldApply_ae μ F hF C hC (c • f),
          regularFieldApply_ae μ F hF C hC f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (regularFieldApply μ F hF C hC f)] with t hc hf ha hb
        rw [hc, hb, ha]
        simp only [Pi.smul_apply]
        rw [hf, map_smul] }
    C (norm_regularFieldApply_le μ F hF C hC)

omit [CompleteSpace H] in
theorem regularFieldOperator_represents (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    (C : ℝ) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) :
    RepresentsOperatorField μ F (regularFieldOperator μ F hF C hC) :=
  regularFieldApply_ae μ F hF C hC

omit [CompleteSpace H] in
theorem norm_regularFieldOperator_le (μ : Measure X) (F : X → H →L[ℂ] H)
    (hF : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) μ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) :
    ‖regularFieldOperator μ F hF C hC‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (norm_regularFieldApply_le μ F hF C hC)

omit [CompleteSpace H] in
/-- Indicator tests recover each vector coefficient of an operator field
on a finite-measure set. -/
theorem RepresentsOperatorField.eval_eq_ae_on {μ : Measure X}
    {F G : X → H →L[ℂ] H} {T : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hF : RepresentsOperatorField μ F T) (hG : RepresentsOperatorField μ G T)
    {s : Set X} (hs : MeasurableSet s) (hfinite : μ s ≠ ∞) (ξ : H) :
    ∀ᵐ t ∂μ, t ∈ s → F t ξ = G t ξ := by
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfinite ξ
  filter_upwards [hF f, hG f,
    (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfinite) (c := ξ))]
    with t hf hg hξ
  intro ht
  rw [hξ ht] at hf hg
  exact hf.symm.trans hg

omit [CompleteSpace H] in
/-- Equality of actual real-line multiplication operators recovers each
vector value almost everywhere. -/
theorem RepresentsOperatorField.eval_eq_ae_real
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T)
    (ξ : H) : (fun t => F t ξ) =ᵐ[volume] fun t => G t ξ := by
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) → F t ξ = G t ξ := by
    apply ae_all_iff.mpr
    intro n
    exact hF.eval_eq_ae_on hG measurableSet_Icc (by simp) ξ
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  exact ht n (Set.mem_Icc.mpr (abs_le.mp hn.le))

omit [CompleteSpace H] in
/-- On a separable Hilbert space, equality of multiplication operators
recovers the entire field almost everywhere. -/
theorem RepresentsOperatorField.field_eq_ae_real [TopologicalSpace.SeparableSpace H]
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T) :
    F =ᵐ[volume] G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ, F t (v n) = G t (v n) :=
    ae_all_iff.mpr fun n => hF.eval_eq_ae_real hG (v n)
  filter_upwards [hall] with t ht
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (F t).continuous (G t).continuous (funext ht))

/-- Translation conjugates an actual multiplication operator by shifting
its field. -/
theorem RepresentsOperatorField.real_translate
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (s : Multiplicative ℝ) :
    RepresentsOperatorField volume (fun t => F (t + s.toAdd))
      (unitaryConj (regularRightTranslation (H := H) s) T) := by
  intro f
  have hstar : (star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [map_inv]
    rfl
  unfold unitaryConj
  rw [hstar]
  filter_upwards [regularRightTranslation_apply_ae s
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (hF ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae s⁻¹ f)] with t hρ hFshift hback
  simp only [Function.comp_def] at hFshift hback
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hρ, hFshift, hback]
  simp

/-- An actually decomposable operator fixed by every translation is a
constant operator. Decomposability itself is not posited for arbitrary
operators. -/
theorem constant_of_regularField_translation_fixed [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (hfixed : ∀ s, unitaryConj (regularRightTranslation (H := H) s) T = T) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧ T = regularConstantHom volume A := by
  have hshift (s : ℝ) : (fun t => F (t + s)) =ᵐ[volume] F := by
    have h := hF.real_translate (Multiplicative.ofAdd s)
    rw [hfixed] at h
    exact h.field_eq_ae_real hF
  have hcoeff (s : ℝ) (ξ η : H) :
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume] fun t => inner ℂ η (F t ξ) :=
    (hshift s).mono fun _ h => congrArg (fun A : H →L[ℂ] H => inner ℂ η (A ξ)) h
  obtain ⟨A, hA⟩ := operatorField_real_translation_invariant_const F
    (fun ξ η => (hmeas ξ).const_inner (c := η)) hcoeff
  refine ⟨A, hA, hF.unique ?_⟩
  intro f
  filter_upwards [regularConstantHom_apply_ae volume A f, hA] with t ht hAt
  exact ht.trans (congrArg (fun B : H →L[ℂ] H => B (f t)) hAt.symm)

end

end KadisonKastler

end OAI
