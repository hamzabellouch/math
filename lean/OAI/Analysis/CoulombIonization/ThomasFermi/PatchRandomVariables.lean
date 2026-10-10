import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedMeasurable
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchGapMeasurable
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreFieldRegularity
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedPatchDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAnalysis

local instance : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfPatchIntegral_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ z, f z ∂ballMeasure R) := by
  let Φ : TFField R := (memLp_const (1:ℝ)).toLp (fun _ : TFSpace => (1:ℝ))
  have he (f : TFLp (ballMeasure R)) : -(tfPatchLinear R Φ f) = ∫ z, f z ∂ballMeasure R := by
    rw [tfPatchLinear_apply,neg_neg]
    have hΦ : Φ =ᵐ[ballMeasure R] fun _ => (1:ℝ) :=
      (memLp_const (1:ℝ)).coeFn_toLp
    exact integral_congr_ae (hΦ.mono fun z hz => by simp only [hz,one_mul])
  convert (tfPatchLinear R Φ).continuous.neg using 1
  funext f
  exact (he f).symm

end CoulombAnalysis
namespace CoulombNeumann
open CoulombAtom CoulombAnalysis
local instance : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma retainedPatchLp_measurable {A : Type*} [MeasurableSpace A] {N : ℕ}
    {b : ℝ} (hb : 0 < b) (S : A → Finset (Fin N)) (x : A → Configuration N)
    (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hx : Measurable x) (y : Space) (R : ℝ) :
    Measurable (fun a => retainedPatchLp hb (S a) (x a) y R) := by
  have hm := retainedSmear_measurable_eval b (fun p : A × Space => S p.1)
    (fun p => x p.1) (fun p => y+p.2) (fun i => measurable_fst (hS i))
    (hx.comp measurable_fst) (measurable_const.add measurable_snd)
  exact measurable_memLp_toLp hm (fun a => retainedPatch_memLp hb (S a) (x a) y R)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma conditionalPatchField_ae {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M)
    (hf : MemLp (fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)) (5/2) (ballMeasure R)) :
    conditionalPatchField ψ t Z lam y R u =ᵐ[ballMeasure R]
      fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z) := by
  rw [conditionalPatchField,toLpOrZero_eq hf]
  exact hf.coeFn_toLp

lemma conditionalPatchMass_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (fun u => ∫ z, tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R) :=
  (tfPatchIntegral_continuous R).measurable.comp_aemeasurable
    (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R)

lemma conditionalPatchGap_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    AEMeasurable (fun u => tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)) := by
  have hf : AEMeasurable (conditionalPatchField ψ t Z lam y R) :=
    conditionalPatchField_aemeasurable hψ t Z lam y R
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  exact tfPatchGap_comp_aemeasurable R tfKinetic tfKinetic_pos _ _ hf hs.aemeasurable

end CoulombAtom

end

end OAI
