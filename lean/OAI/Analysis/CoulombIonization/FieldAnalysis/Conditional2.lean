import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierObservationTowerBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.Error

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

lemma conditionalField_nonneg {p : Ω → TFSpace → ℝ} (hn : ∀ sample x, 0 ≤ p sample x)
    (d : D) (x : TFSpace) : 0 ≤ conditionalField P X p d x :=
  integral_nonneg (fun sample => hn sample x)

lemma conditionalField_support {p : Ω → TFSpace → ℝ} {R : ℝ}
    (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) (d : D) (x : TFSpace) (hx : R < ‖x‖) :
    conditionalField P X p d x = 0 := by
  simp only [conditionalField,hs _ x hx,integral_zero]

include hX

lemma conditionalField_expectation {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p) (x : TFSpace) :
    (∫ sample, conditionalField P X p (X sample) x ∂P) = ∫ sample, p sample x ∂P := by
  rw [←integral_congr_ae (conditionalField_eq_condExp P hX hm hb x)]
  exact integral_condExp hX.comap_le

theorem conditionalField_totalMass {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    (∫ sample, (∫ x, conditionalField P X p (X sample) x) ∂P) = ∫ sample, (∫ x, p sample x) ∂P := by
  have hcm : Measurable (fun z : Ω × TFSpace => conditionalField P X p (X z.1) z.2) :=
    (conditionalField_measurable P X hm).comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hcb : DeterministicLocalBound (fun sample x => conditionalField P X p (X sample) x) := by
    intro K hK
    obtain ⟨C,hC⟩ := conditionalField_bound P X hb K hK
    exact ⟨C,fun sample x hx => hC (X sample) x hx⟩
  have hcs : ∀ sample x, R < ‖x‖ → conditionalField P X p (X sample) x = 0 :=
    fun sample x hx => conditionalField_support P X hs (X sample) x hx
  rw [integral_integral_swap (compactBound_integrable_prod hcm hcb hcs),
    integral_integral_swap (compactBound_integrable_prod hm hb hs)]
  exact integral_congr_ae (Eventually.of_forall fun x => conditionalField_expectation P X hX hm hb x)

theorem conditionalField_spatial_bounds {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (V a b : TFSpace → ℝ) (A : Set TFSpace)
    (hlo : ∀ᵐ sample ∂P, ∀ x ∈ A, a x ≤ V x+u sample x)
    (hhi : ∀ᵐ sample ∂P, ∀ x ∈ A, V x+u sample x ≤ b x) :
    ∀ᵐ d ∂P.map X, ∀ x ∈ A,
      a x ≤ V x+conditionalField P X u d x ∧
      V x+conditionalField P X u d x ≤ b x := by
  filter_upwards [conditional_all_properties P hX hlo,conditional_all_properties P hX hhi] with d hdlo hdhi
  intro x hx
  have hi := (integrable_const (V x) : Integrable (fun _ : Ω => V x) (condDistrib id X P d)).add
    (deterministicBound_integrable_section hm hb x)
  have he : (∫ sample, (V x+u sample x) ∂condDistrib id X P d) = V x+conditionalField P X u d x := by
    rw [integral_add (integrable_const _) (deterministicBound_integrable_section hm hb x)]
    simp [conditionalField]
  constructor
  · rw [←he]
    simpa only [integral_const,probReal_univ,one_smul,Pi.add_apply] using
      integral_mono_ae (integrable_const (a x)) hi (hdlo.mono fun sample hω => hω x hx)
  · rw [←he]
    simpa only [integral_const,probReal_univ,one_smul,Pi.add_apply] using
      integral_mono_ae hi (integrable_const (b x)) (hdhi.mono fun sample hω => hω x hx)

end CoulombBarrier

end

end OAI
