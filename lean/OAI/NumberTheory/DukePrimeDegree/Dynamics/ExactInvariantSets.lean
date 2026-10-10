import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

namespace OAI

/-!
# Exact representatives of invariant measurable sets

An almost invariant set has an exactly invariant representative when
the acting group carries a nonzero finite measure in a translation
invariant measure class. Haar measure supplies such a finite measure.
This is the measure-class step needed to compare the full invariant
sigma algebra with a countable dense subgroup's invariant sigma algebra.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ENNReal

namespace DukePrimeDegree

section MeasurableAction

variable {H Y : Type*} [Group H] [MeasurableSpace H]
  [MeasurableSpace Y] [MulAction H Y]

def orbitAlmostAllSet (ρ : Measure H) (B : Set Y) : Set Y :=
  {x | ∀ᵐ h ∂ρ, h • x ∈ B}

lemma measurableSet_orbitAlmostAllSet
    (ρ : Measure H) [SFinite ρ]
    (hsmul : Measurable (fun p : Y × H => p.2 • p.1))
    {B : Set Y} (hB : MeasurableSet B) :
    MeasurableSet (orbitAlmostAllSet ρ B) := by
  have hm : Measurable (fun x : Y => ρ {h : H | h • x ∉ B}) :=
    measurable_measure_prodMk_left (hB.compl.preimage hsmul)
  have heq : orbitAlmostAllSet ρ B = {x : Y | ρ {h : H | h • x ∉ B} = 0} := by
    ext x
    exact ae_iff
  rw [heq]
  exact measurableSet_eq_fun hm measurable_const

omit [MeasurableSpace Y] in
lemma preimage_orbitAlmostAllSet_eq
    (ρ : Measure H)
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (B : Set Y) (g : H) :
    (fun x : Y => g • x) ⁻¹' orbitAlmostAllSet ρ B = orbitAlmostAllSet ρ B := by
  ext x
  change (∀ᵐ h ∂ρ, h • (g • x) ∈ B) ↔ ∀ᵐ h ∂ρ, h • x ∈ B
  constructor
  · intro hx
    have hh := (hρ g⁻¹).ae hx
    simpa only [mul_smul, inv_smul_smul] using hh
  · intro hx
    simpa only [mul_smul] using (hρ g).ae hx

/-- Fubini replaces separate almost invariance by one exactly invariant
set, without a countable intersection over the acting group. -/
theorem orbitAlmostAllSet_ae_eq
    (μ : Measure Y) [SFinite μ]
    (ρ : Measure H) [SFinite ρ] (hρ : ρ ≠ 0)
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    {B : Set Y} (hB : MeasurableSet B)
    (hfix : ∀ h : H, (fun x : Y => h • x) ⁻¹' B =ᵐ[μ] B) :
    orbitAlmostAllSet ρ B =ᵐ[μ] B := by
  have hmeas : MeasurableSet {p : H × Y | p.1 • p.2 ∈ B ↔ p.2 ∈ B} :=
    (hB.preimage hsmul).iff (hB.preimage measurable_snd)
  have hboth : ∀ᵐ x ∂μ, ∀ᵐ h ∂ρ, h • x ∈ B ↔ x ∈ B :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall fun h => (hfix h).mem_iff)
  apply Filter.Eventually.set_eq
  filter_upwards [hboth] with x hx
  change (∀ᵐ h ∂ρ, h • x ∈ B) ↔ x ∈ B
  constructor
  · intro hall
    by_contra hn
    have hfalse : ∀ᵐ h ∂ρ, False := (hall.and hx).mono fun h hh => hn (hh.2.mp hh.1)
    have hzero : ρ Set.univ = 0 := by simpa [ae_iff] using hfalse
    exact hρ (Measure.measure_univ_eq_zero.mp hzero)
  · intro hxB
    exact hx.mono fun h hh => hh.mpr hxB

/-- A finite measure equivalent to a left Haar measure has a measure
class invariant under every right translation. -/
theorem exists_finite_right_quasiInvariant_measure
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0) :
    ∃ ρ : Measure H, IsFiniteMeasure ρ ∧ ρ ≠ 0 ∧
      ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ := by
  obtain ⟨ρ, hfin, hhaarρ, hρhaar⟩ := exists_isFiniteMeasure_absolutelyContinuous haar
  refine ⟨ρ, hfin, ?_, ?_⟩
  · intro hzero
    apply hhaar
    apply Measure.measure_univ_eq_zero.mp
    exact hhaarρ (by rw [hzero]; simp)
  · intro g
    exact (quasiMeasurePreserving_mul_right haar g).mono hρhaar hhaarρ

/-- Exact invariant representatives are obtained from the actual
translation-invariant measure class, rather than postulated. -/
theorem exists_exact_invariant_set
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0)
    (μ : Measure Y) [SFinite μ]
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    {B : Set Y} (hB : MeasurableSet B)
    (hfix : ∀ h : H, (fun x : Y => h • x) ⁻¹' B =ᵐ[μ] B) :
    ∃ E : Set Y, MeasurableSet E ∧ E =ᵐ[μ] B ∧
      ∀ h : H, (fun x : Y => h • x) ⁻¹' E = E := by
  obtain ⟨ρ, hfin, hρ, hright⟩ := exists_finite_right_quasiInvariant_measure haar hhaar
  let : IsFiniteMeasure ρ := hfin
  exact ⟨orbitAlmostAllSet ρ B,
    measurableSet_orbitAlmostAllSet ρ (hsmul.comp measurable_swap) hB,
    orbitAlmostAllSet_ae_eq μ ρ hρ hsmul hB hfix,
    preimage_orbitAlmostAllSet_eq ρ hright B⟩

end MeasurableAction
end DukePrimeDegree

end

end OAI
