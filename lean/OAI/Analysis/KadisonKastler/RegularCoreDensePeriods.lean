import OAI.Analysis.KadisonKastler.RegularCoreFields
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace OAI

/-! # Dense periods of bounded regular coefficient fields

Strong continuity of translations on the actual `L²` space extends
commutation from any dense family of translations to all translations.
Consequently a bounded measurable field with dense periods is constant
almost everywhere. In particular, two incommensurable scalar periods
suffice, as required by the two-frequency modular-core argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Real translations are strongly continuous on the actual regular
Hilbert space. -/
theorem continuous_regularTranslateApply (f : RegularCoreHilbert H) :
    Continuous (fun s : ℝ => regularTranslateApply s f) := by
  let g : ℝ → C(ℝ, ℝ) := fun s => ⟨fun t => t + s, continuous_id.add continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g (continuous_snd.add continuous_fst)
  have hc := (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    hg (fun s => measurePreserving_add_right (volume : Measure ℝ) s) (by norm_num : (2 : ENNReal) ≠ ⊤)
  exact hc

/-- A bounded operator commuting with a dense set of translations commutes
with every translation. -/
theorem regularTranslation_commute_of_dense
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    {S : Set ℝ} (hS : Dense S)
    (hcomm : ∀ s ∈ S, Commute T
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (s : ℝ) :
    Commute T
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change T * _ = _ * T
  apply ContinuousLinearMap.ext
  intro f
  change T (regularTranslateApply s f) = regularTranslateApply s (T f)
  exact hS.induction
    (fun t ht => congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f)
      (hcomm t ht).eq)
    (isClosed_eq (T.continuous.comp (continuous_regularTranslateApply f))
      (continuous_regularTranslateApply (T f))) s

/-- A decomposable operator fixed by a dense set of translations has an
almost-everywhere constant field. -/
theorem constant_of_regularField_dense_translation_fixed
    [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    {S : Set ℝ} (hS : Dense S)
    (hfixed : ∀ s ∈ S, unitaryConj
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s)) T = T) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧
      T = regularConstantHom volume A := by
  apply constant_of_regularField_translation_fixed hF hmeas
  intro s
  have hc : Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    regularTranslation_commute_of_dense T hS (fun t ht =>
      ((commute_unitary_iff_star_right_conjugate
        (regularRightTranslation (H := H) (Multiplicative.ofAdd t)).property).mpr
          (hfixed t ht)).symm) s.toAdd
  exact (commute_unitary_iff_star_right_conjugate
    (regularRightTranslation (H := H) s).property).mp hc.symm

/-- Bounded measurable operator fields with a dense set of periods are
constant almost everywhere. -/
theorem bounded_operatorField_dense_periods_const
    [TopologicalSpace.SeparableSpace H]
    (F : ℝ → H →L[ℂ] H)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    {S : Set ℝ} (hS : Dense S)
    (hperiod : ∀ s ∈ S, (fun t => F (t + s)) =ᵐ[volume] F) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] fun _ => A := by
  let T := regularFieldOperator volume F hmeas C hbound
  have hT : RepresentsOperatorField volume F T :=
    regularFieldOperator_represents volume F hmeas C hbound
  have hfixed (s : ℝ) (hs : s ∈ S) : unitaryConj
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s)) T = T := by
    apply RepresentsOperatorField.unique (F := F) ?_ hT
    intro f
    filter_upwards [hT.real_translate (Multiplicative.ofAdd s) f, hperiod s hs]
      with t ht hp
    exact ht.trans (congrArg (fun A : H →L[ℂ] H => A (f t)) hp)
  obtain ⟨A, hA, _⟩ := constant_of_regularField_dense_translation_fixed hT hmeas hS hfixed
  exact ⟨A, hA⟩

/-- Scalar bounded coefficient fields are a special case of the actual
operator-field construction. -/
theorem bounded_scalar_dense_periods_const
    (f : ℝ → ℂ) (hmeas : AEStronglyMeasurable f volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖f t‖ ≤ C)
    {S : Set ℝ} (hS : Dense S)
    (hperiod : ∀ s ∈ S, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  let F : ℝ → ℂ →L[ℂ] ℂ := fun t => f t • 1
  have hFmeas (ξ : ℂ) : AEStronglyMeasurable (fun t => F t ξ) volume := by
    simpa only [F, smul_apply, one_apply_eq_self] using hmeas.smul_const ξ
  have hFbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C := by
    filter_upwards [hbound] with t ht
    simpa only [F, norm_smul, norm_one, mul_one] using ht
  have hFperiod : ∀ s ∈ S, (fun t => F (t + s)) =ᵐ[volume] F := by
    intro s hs
    exact (hperiod s hs).mono fun t ht => congrArg (fun z : ℂ => z • (1 : ℂ →L[ℂ] ℂ)) ht
  obtain ⟨A, hA⟩ := bounded_operatorField_dense_periods_const F hFmeas C hFbound hS hFperiod
  refine ⟨A 1, hA.mono fun t ht => ?_⟩
  have he := congrArg (fun B : ℂ →L[ℂ] ℂ => B 1) ht
  simpa only [F, smul_apply, one_apply_eq_self, smul_eq_mul, mul_one] using he

/-- Almost-everywhere periods form an actual additive subgroup. -/
def scalarAEPeriods (f : ℝ → ℂ) : AddSubgroup ℝ where
  carrier := {s | (fun t => f (t + s)) =ᵐ[volume] f}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change (fun x => f (x + (s + t))) =ᵐ[volume] f
    have ht' := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq_comp ht
    filter_upwards [ht', hs] with x ht hs
    simpa only [Function.comp_def, add_assoc] using ht.trans hs
  neg_mem' := by
    intro s hs
    have hs' := (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae_eq_comp hs
    filter_upwards [hs'] with x hx
    simpa only [Function.comp_def, add_assoc, neg_add_cancel, add_zero] using hx.symm

/-- Two periods with irrational ratio force any essentially bounded
measurable scalar field to be constant almost everywhere. -/
theorem bounded_scalar_two_periods_const
    (f : ℝ → ℂ) (hmeas : AEStronglyMeasurable f volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖f t‖ ≤ C)
    {a b : ℝ} (hirr : Irrational (a / b))
    (ha : (fun t => f (t + a)) =ᵐ[volume] f)
    (hb : (fun t => f (t + b)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hle : AddSubgroup.closure {a, b} ≤ scalarAEPeriods f := by
    apply (AddSubgroup.closure_le (scalarAEPeriods f)).mpr
    intro s hs
    rcases Set.mem_insert_iff.mp hs with h | h
    · subst s
      exact ha
    · have he : s = b := Set.mem_singleton_iff.mp h
      subst s
      exact hb
  have hd : Dense (AddSubgroup.closure {a, b} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  exact bounded_scalar_dense_periods_const f hmeas C hbound hd (fun s hs => hle hs)

omit [CompleteSpace H] in
/-- Two incommensurable periods scalarize an entire bounded measurable
operator field, with one common exceptional null set. -/
theorem bounded_operatorField_two_periods_const
    [TopologicalSpace.SeparableSpace H]
    (F : ℝ → H →L[ℂ] H)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    {a b : ℝ} (hirr : Irrational (a / b))
    (ha : (fun t => F (t + a)) =ᵐ[volume] F)
    (hb : (fun t => F (t + b)) =ᵐ[volume] F) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] fun _ => A := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hcoeff (ξ η : H) : ∃ c : ℂ,
      (fun t => inner ℂ η (F t ξ)) =ᵐ[volume] fun _ => c := by
    apply bounded_scalar_two_periods_const
      (fun t => inner ℂ η (F t ξ)) ((hmeas ξ).const_inner (c := η))
      (‖η‖ * (C * ‖ξ‖)) ?_ hirr
      (ha.mono fun _ h => congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) h)
      (hb.mono fun _ h => congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) h)
    filter_upwards [hbound] with t ht
    exact (norm_inner_le_norm η (F t ξ)).trans
      (mul_le_mul_of_nonneg_left
        (((F t).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg ξ)))
        (norm_nonneg η))
  choose c hc using fun i j : ℕ => hcoeff (v j) (v i)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i j : ℕ,
      inner ℂ (v i) (F t (v j)) = c i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hc i j
  obtain ⟨t₀, ht₀⟩ := hall.exists
  refine ⟨F t₀, hall.mono fun t ht => ?_⟩
  apply ContinuousLinearMap.ext
  have he : (fun ξ => F t ξ) = (fun ξ => F t₀ ξ) := by
    apply hv.equalizer (F t).continuous (F t₀).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => (ht i j).trans (ht₀ i j).symm)
  exact congrFun he

end

end KadisonKastler

end OAI
