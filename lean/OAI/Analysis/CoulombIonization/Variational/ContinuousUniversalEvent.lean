import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OriginalFieldOscillationBarrier
import OAI.Analysis.CoulombIonization.Localization.InverseNetEventsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open Set MeasureTheory

theorem measurableSet_forall_closed_parameter
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    {P : Ω → X → Prop} (hm : ∀ x, MeasurableSet {ω | P ω x})
    (hc : ∀ ω, IsClosed {x | P ω x}) : MeasurableSet {ω | ∀ x, P ω x} := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense X
  have he : {ω | ∀ x, P ω x} = ⋂ x ∈ D, {ω | P ω x} := by
    ext ω
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · intro h x _
      exact h x
    · intro h x
      exact closure_minimal h (hc ω) (hd x)
  rw [he]
  exact MeasurableSet.biInter hD (fun x _ => hm x)

open Set MeasureTheory
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma inverseComparisonAt_closed {X : Type*} [TopologicalSpace X]
    {d H μ : X → ℝ} (hd : Continuous d) (hH : Continuous H) (hμ : Continuous μ)
    (κ lo hi xi C : ℝ) : IsClosed {x | InverseComparisonAt (d x) (H x) (μ x) κ lo hi xi C} := by
  have hf := (hd.pow 4).mul hH
  have hr := (hd.pow 6).mul hμ
  have h₀ := isClosed_le hf continuous_const (g := fun _ => C)
  have h₁ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le hr continuous_const (g := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le continuous_const hf (f := fun _ => (h:ℝ)-xi)))
  have h₂ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le continuous_const hr (f := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le hf continuous_const (g := fun _ => (h:ℝ)+xi)))
  convert h₀.inter (h₁.inter h₂) using 1
  ext x
  simp only [mem_inter_iff,mem_iInter,mem_union,mem_ofPred_eq,InverseComparisonAt,
    imp_iff_not_or,not_lt,Subtype.forall,Pi.mul_apply,Pi.pow_apply]

lemma inverseComparisonAt_measurable {Ω : Type*} [MeasurableSpace Ω]
    {H μ : Ω → ℝ} (hH : Measurable H) (hμ : Measurable μ)
    (d κ lo hi xi C : ℝ) : MeasurableSet {q | InverseComparisonAt d (H q) (μ q) κ lo hi xi C} := by
  have hf := hH.const_mul (d^4)
  have hr := hμ.const_mul (d^6)
  have h₀ := measurableSet_le hf measurable_const (g := fun _ => C)
  have ht : Continuous (fun h : Icc lo hi => κ*(h:ℝ)^(3/2:ℝ)) :=
    ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp continuous_subtype_val).const_mul κ
  have h₁ : MeasurableSet {q | ∀ h : Icc lo hi,
      d^6*μ q ≤ κ*(h:ℝ)^(3/2:ℝ) ∨ (h:ℝ)-xi ≤ d^4*H q} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le hr measurable_const).union (measurableSet_le measurable_const hf)
    · intro q
      exact (isClosed_le continuous_const ht).union
        (isClosed_le (continuous_subtype_val.sub continuous_const) continuous_const)
  have h₂ : MeasurableSet {q | ∀ h : Icc lo hi,
      κ*(h:ℝ)^(3/2:ℝ) ≤ d^6*μ q ∨ d^4*H q ≤ (h:ℝ)+xi} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le measurable_const hr).union (measurableSet_le hf measurable_const)
    · intro q
      exact (isClosed_le ht continuous_const).union
        (isClosed_le continuous_const (continuous_subtype_val.add_const xi))
  convert h₀.inter (h₁.inter h₂) using 1
  ext q
  simp only [mem_inter_iff,mem_ofPred_eq,InverseComparisonAt,imp_iff_not_or,not_lt,Subtype.forall]

lemma original_inverse_fullAnnulus_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s u B κ lo hi xi C : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s) (hu : 0 < u) :
    MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
        InverseComparisonAt ‖y‖
          (originalQueryField F Z lam r j c₁ r₀ s q y)
          (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
  let Y := {y : Space // u ≤ ‖y‖ ∧ ‖y‖ ≤ B*u}
  have he : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Y, InverseComparisonAt ‖(y:Space)‖
        (originalQueryField F Z lam r j c₁ r₀ s q y)
        (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
    apply @measurableSet_forall_closed_parameter _ Y
      (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
    · intro y
      exact @inverseComparisonAt_measurable _
        (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
        (originalQueryField_info_measurable F Z lam r j hc hr hs y)
        (originalQueryDensity_info_measurable F r j hc hr hs y) _ _ _ _ _ _
    · intro q
      have hfield : Continuous (fun y : Y => originalQueryField F Z lam r j c₁ r₀ s q y) := by
        apply (originalQueryField_continuousOn_punctured F Z lam r j hc hr hs hrs q).comp_continuous
          continuous_subtype_val
        intro y
        change (y:Space) ≠ 0
        exact norm_pos_iff.mp (hu.trans_le y.property.1)
      have hden : Continuous (fun y : Y => originalQueryDensity F r j c₁ r₀ s q y) :=
        (jointMasterPosterior_continuous (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j hc hr hs hrs
          canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j q)).comp continuous_subtype_val
      exact inverseComparisonAt_closed continuous_subtype_val.norm hfield hden _ _ _ _ _
  convert he using 1
  ext q
  simp only [mem_ofPred_eq,Subtype.forall,Y]
  simp only [and_imp]

end CoulombAtom

end

end OAI
