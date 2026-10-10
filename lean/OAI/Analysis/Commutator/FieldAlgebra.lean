import Mathlib
import OAI.Analysis.Commutator.AddField
import OAI.Analysis.Commutator.ScalarField
import OAI.Analysis.Commutator.StarField

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FieldMember (Q : Ω → VonNeumannAlgebra H) (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) : Prop :=
  ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (b : ℝ) (hb : ∀ᵐ a ∂μ,‖T a‖≤b),0≤b ∧ A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a

lemma fieldMember_const (Q : Ω → VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hmem : ∀ᵐ a ∂μ,T∈Q a) :
    FieldMember μ Q (operator μ (fun _ => T) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) :=
  ⟨(fun _ => T),(fun _ => aestronglyMeasurable_const),‖T‖,
    Eventually.of_forall (fun _ => le_rfl),norm_nonneg T,rfl,hmem⟩

lemma fieldMember_zero (Q : Ω → VonNeumannAlgebra H) : FieldMember μ Q 0 := by
  have he : (0 : Lp H 2 μ →L[ℂ] Lp H 2 μ)=
      operator μ (fun _ => (0:H →L[ℂ] H)) (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => le_rfl)) := by
    apply operator_eq_of_ae_apply
    intro f
    filter_upwards [Lp.coeFn_zero H 2 μ] with a ha
    exact ha
  rw [he]
  exact fieldMember_const μ Q 0 (Eventually.of_forall (fun a => (Q a).zero_mem))

lemma fieldMember_one (Q : Ω → VonNeumannAlgebra H) : FieldMember μ Q 1 := by
  have he : (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ)=
      operator μ (fun _ => (1:H →L[ℂ] H)) (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => le_rfl)) := by
    apply operator_eq_of_ae_apply
    intro f
    exact Eventually.of_forall (fun _ => rfl)
  rw [he]
  exact fieldMember_const μ Q 1 (Eventually.of_forall (fun a => (Q a).one_mem))

lemma fieldMember_add (Q : Ω → VonNeumannAlgebra H)
    {A B : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (hB : FieldMember μ Q B) : FieldMember μ Q (A+B) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  obtain ⟨S,hS,c,hc,hc0,rfl,hSm⟩ := hB
  refine ⟨(fun a => T a+S a),add_measurable μ T S hT hS,b+c,
    add_field_bound μ T S hb hc,add_nonneg hb0 hc0,(operator_add μ T S hT hS hb hc).symm,?_⟩
  filter_upwards [hTm,hSm] with a ha hb
  exact (Q a).add_mem ha hb

lemma fieldMember_mul (Q : Ω → VonNeumannAlgebra H)
    {A B : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (hB : FieldMember μ Q B) : FieldMember μ Q (A*B) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  obtain ⟨S,hS,c,hc,hc0,rfl,hSm⟩ := hB
  refine ⟨(fun a => T a*S a),mul_measurable μ T S hT hS,b*c,
    mul_bound μ T S hb0 hb hc,mul_nonneg hb0 hc0,operator_mul μ T S hT hS hb0 hb hc,?_⟩
  filter_upwards [hTm,hSm] with a ha hb
  exact (Q a).mul_mem ha hb

lemma fieldMember_smul (Q : Ω → VonNeumannAlgebra H) (z : ℂ)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A) :
    FieldMember μ Q (z • A) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  refine ⟨(fun a => z • T a),smul_measurable μ z T hT,‖z‖*b,
    smul_field_bound μ z T hb,mul_nonneg (norm_nonneg z) hb0,
    (operator_smul μ z T hT hb).symm,?_⟩
  filter_upwards [hTm] with a ha
  exact (Q a).smul_mem ha z

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma fieldMember_star (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A) :
    FieldMember μ Q (star A) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  refine ⟨(fun a => (T a).adjoint),adjoint_measurable μ T hT hb,b,
    adjoint_field_bound μ T hb,hb0,(operator_adjoint μ T hT hb).symm,?_⟩
  filter_upwards [hTm] with a ha
  exact (Q a).star_mem' ha

def fieldAlgebra (Q : Ω → VonNeumannAlgebra H) :
    StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  carrier := FieldMember μ Q
  zero_mem' := fieldMember_zero μ Q
  one_mem' := fieldMember_one μ Q
  add_mem' := fieldMember_add μ Q
  mul_mem' := fieldMember_mul μ Q
  algebraMap_mem' z := by
    change FieldMember μ Q (algebraMap ℂ _ z)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      fieldMember_smul μ Q z (fieldMember_one μ Q)
  star_mem' := fieldMember_star μ Q

end Kadison.Decomposable

end

end
end

end OAI
