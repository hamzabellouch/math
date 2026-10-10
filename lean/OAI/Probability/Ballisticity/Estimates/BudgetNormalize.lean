import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetEndpoint

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def normalizeOr {α : Type*} [MeasurableSpace α] (μ ρ : Measure α) : Measure α :=
  if μ Set.univ = 0 then ρ else normalizedMeasure μ

lemma normalizeOr_probability {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ρ] : IsProbabilityMeasure (normalizeOr μ ρ) := by
  by_cases h : μ Set.univ=0
  · simpa only [normalizeOr,ite_eq_left h] using (inferInstance : IsProbabilityMeasure ρ)
  · simpa only [normalizeOr,ite_eq_right h] using normalizedMeasure_probability μ h

lemma normalizeOr_mass {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] : μ Set.univ • normalizeOr μ ρ = μ := by
  by_cases h : μ Set.univ=0
  · rw [h,zero_smul]; exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [normalizeOr,ite_eq_right h,mass_smul_normalizedMeasure]

lemma normalizeOr_ae {α : Type*} [MeasurableSpace α] (μ ρ : Measure α) (P : α → Prop)
    (hμ : ∀ᵐ x ∂μ, P x) (hρ : ∀ᵐ x ∂ρ, P x) : ∀ᵐ x ∂normalizeOr μ ρ, P x := by
  unfold normalizeOr
  split
  · exact hρ
  · exact Measure.ae_smul_measure hμ _

lemma measurable_normalizeOr {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ ρ : Ω → Measure α) (hμ : Measurable μ) (hρ : Measurable ρ) :
    Measurable (fun ω => normalizeOr (μ ω) (ρ ω)) := by
  unfold normalizeOr normalizedMeasure
  apply Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hμ) measurable_const) hρ
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.smul_apply,smul_eq_mul]
  exact (((Measure.measurable_coe MeasurableSet.univ).comp hμ).inv).mul
    ((Measure.measurable_coe hU).comp hμ)

abbrev BudgetProfile {d k : ℕ} (e f : Direction d) (a G : ℝ) :=
  {π : Measure (Fin k → Lattice d) // IsProbabilityMeasure π ∧
    ∀ᵐ x ∂π, x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x}

instance budgetProfile_probability {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : BudgetProfile (k:=k) e f a G) : IsProbabilityMeasure π.val := π.property.1

def BudgetProfile.toSupported {d k : ℕ} {e f : Direction d} {a G : ℝ}
    (π : BudgetProfile (k:=k) e f a G) : SupportedTupleMeasures (TupleAtHeight (k:=k) (realPosition (step e)) a) :=
  ⟨π.val,ae_iff.mp (π.property.2.mono fun _ h => h.1)⟩

lemma BudgetProfile.measurable_toSupported {d k : ℕ} (e f : Direction d) (a G : ℝ) :
    Measurable (BudgetProfile.toSupported (d:=d) (k:=k) (e:=e) (f:=f) (a:=a) (G:=G)) :=
  measurable_subtype_coe.subtype_mk

def tupleShiftUp {d k : ℕ} (e : Direction d) (H : ℕ) (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => x j + H • step e

lemma tupleShiftUp_support {d k : ℕ} (e f : Direction d) (H : ℕ) (a G : ℝ)
    (x : Fin k → Lattice d) (hx : x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x) :
    tupleShiftUp e H x ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧
      TupleSeparated f G (tupleShiftUp e H x) := by
  have hs (g : Direction d) (y : Lattice d) : signedCoordinate g (y+H • step e) =
      signedCoordinate g y + (H:ℝ)*signedCoordinate g (step e) := by
    simp only [signedCoordinate,Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    split <;> ring
  constructor
  · intro j
    change dot (realPosition (x j+H • step e)) (realPosition (step e))=a+H
    rw [dot_signed_direction,hs,signedCoordinate_step_self,mul_one,← dot_signed_direction,hx.1 j]
  · intro i j hij
    change G ≤ |signedCoordinate f (x i+H • step e)-signedCoordinate f (x j+H • step e)|
    rw [hs,hs,add_sub_add_right_eq_sub]
    exact hx.2 i j hij

noncomputable def nextBudgetProfile {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (hr : 0 ≤ r) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+H) (G-r) := by
  let μ := budgetEndpointMixture e f H r π.val ω
  let ρ := π.val.map (tupleShiftUp e H)
  letI : IsProbabilityMeasure ρ := inferInstance
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact budgetEndpointMixture_support e f H a G r π.val ω π.property.2
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    exact π.property.2.mono fun x hx => by
      have h := tupleShiftUp_support e f H a G x hx
      exact ⟨h.1,tupleSeparated_mono f (sub_le_self G hr) _ h.2⟩

lemma nextBudgetProfile_mass {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (hr : 0 ≤ r) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    relativeBudgetMassENN e f H r π.val ω •
      (nextBudgetProfile e f H a G r hr π ω).val = budgetEndpointMixture e f H r π.val ω := by
  change _ • normalizeOr _ _ = _
  rw [← budgetEndpointMixture_univ]
  exact normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
