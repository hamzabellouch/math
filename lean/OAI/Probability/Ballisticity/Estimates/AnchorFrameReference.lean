import Mathlib
import OAI.Probability.Ballisticity.Estimates.ReferenceContinuity
import OAI.Probability.Ballisticity.Entropy.WindowProjectionEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience.ReferenceClasses
variable {H : Type*} [AddCommGroup H]

noncomputable def anchorOffsets (U : ℕ → H) : Data H :=
  ⟨fun p => ((U p.2-U p.1 : H) : OnePoint H), by
    constructor
    · intro a; simp
    · intro a b z h
      simp only [OnePoint.coe_eq_coe] at h ⊢
      rw [← h]; abel
    · intro a b c z w h h'
      simp only [OnePoint.coe_eq_coe] at h h' ⊢
      rw [← h,← h']; abel⟩

lemma anchorOffsets_fibers (U : ℕ → H) (p q : Site H) :
    inputSite (anchorOffsets U) p = inputSite (anchorOffsets U) q ↔
      (p.2.1,U p.1+p.2.2) = (q.2.1,U q.1+q.2.2) := by
  rcases p with ⟨a,l,z⟩
  rcases q with ⟨b,l',z'⟩
  rw [inputSite_eq_iff]
  change (l=l' ∧ ((U b-U a:H):OnePoint H)=((z-z':H):OnePoint H)) ↔ _
  simp only [OnePoint.coe_eq_coe,Prod.mk.injEq]
  constructor
  · rintro ⟨hl,h⟩
    refine ⟨hl,?_⟩
    calc U a+z = U a+(z-z')+z' := by abel
      _ = U a+(U b-U a)+z' := by rw [h]
      _ = U b+z' := by abel
  · rintro ⟨hl,h⟩
    refine ⟨hl,?_⟩
    calc U b-U a = (U b+z')-(U a+z)+z-z' := by abel
      _ = z-z' := by rw [h]; abel

noncomputable def anchorFields {R : Type*} (U : ℕ → H) (ξ : UpperField H R) : AllFields H R :=
  fun p => ξ (p.2.1,U p.1+p.2.2)

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]
  {R : Type*} [MeasurableSpace R]

lemma anchorOffsets_measurable : Measurable (anchorOffsets : (ℕ → H) → Data H) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro p
  exact (OnePoint.continuous_coe.measurable).comp
    ((measurable_pi_apply p.2).sub (measurable_pi_apply p.1))

omit [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma anchorFields_measurable :
    Measurable (fun p : (ℕ → H) × UpperField H R => anchorFields p.1 p.2) := by
  apply Measurable.of_eval
  intro p
  have hev : Measurable (fun q : UpperField H R × (ℕ × H) => q.1 q.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  exact hev.comp (measurable_snd.prodMk (measurable_const.prodMk
    (((measurable_pi_apply p.1).comp measurable_fst).add measurable_const)))

theorem anchorFields_reference (ν : Measure R) [IsProbabilityMeasure ν] (U : ℕ → H) :
    (Measure.infinitePi (fun _ : ℕ × H => ν)).map (anchorFields U) = reference ν (anchorOffsets U) := by
  rw [reference_apply]
  exact map_iid_eq_of_same_fibers ν (fun p : Site H => (p.2.1,U p.1+p.2.2))
    (inputSite (anchorOffsets U)) (fun p q => (anchorOffsets_fibers U p q).symm)

theorem anchorFrame_kl_le {Z P : Type*} [MeasurableSpace Z] [MeasurableSpace P]
    (μ : Measure (Z × UpperField H R)) [IsFiniteMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (U : Z → ℕ → H) (hU : Measurable U)
    (profile : Z → P) (hp : Measurable profile) :
    let out := μ.map (fun p => ((anchorOffsets (U p.1),profile p.1),anchorFields (U p.1) p.2))
    klDiv out (out.fst.compProd ((reference (H:=H) ν).comap Prod.fst measurable_fst)) ≤
      klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × H => ν))) := by
  apply StoppedWindow.own_marginal_projection μ _
    (fun z => (anchorOffsets (U z),profile z)) ((anchorOffsets_measurable.comp hU).prodMk hp)
    (fun z ξ => anchorFields (U z) ξ)
    (anchorFields_measurable.comp ((hU.comp measurable_fst).prodMk measurable_snd))
    ((reference (H:=H) ν).comap Prod.fst measurable_fst)
  intro z
  exact anchorFields_reference ν (U z)

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
