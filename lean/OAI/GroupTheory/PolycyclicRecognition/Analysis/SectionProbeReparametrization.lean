import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic

namespace OAI

/-! # Probe coordinates on the original quotient/kernel cell

The sampling law may be chosen on the original Haar cell and composed with
this homeomorphism. Thus the compact set selected by concentration is already
measured by the probability law required by source packing.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {Z I Q K : Type*} [TopologicalSpace Z] [TopologicalSpace I]
  [TopologicalSpace Q] [TopologicalSpace K]

/-- Coordinates of a point of the actual quotient/kernel product cell. -/
def sectionProbeCoordinates (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I) :
    ((eQ '' B) ×ˢ (eI '' U)) ≃ₜ B × U :=
  (Homeomorph.Set.prod (eQ '' B) (eI '' U)).trans
    ((eQ.image B).symm.prodCongr (eI.image U).symm)

theorem sectionProbeCoordinates_fst
    (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I)
    (y : (eQ '' B) ×ˢ (eI '' U)) :
    eQ (sectionProbeCoordinates eQ eI B U y).1.val = y.val.1 :=
  eQ.apply_symm_apply _

theorem sectionProbeCoordinates_snd
    (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I)
    (y : (eQ '' B) ×ˢ (eI '' U)) :
    eI (sectionProbeCoordinates eQ eI B U y).2.val = y.val.2 :=
  eI.apply_symm_apply _

variable {N : Type*} [TopologicalSpace N]

/-- The section selected in linear quotient coordinates is an actual
continuous section on the quotient group. -/
def coordinateQuotientSection (eQ : Z ≃ₜ Q) (σ : C(Z, N)) : C(Q, N) :=
  ⟨fun q => σ (eQ.symm q), σ.continuous.comp eQ.symm.continuous⟩

theorem coordinateQuotientSection_rightInverse
    (π : N → Q) (eQ : Z ≃ₜ Q) (σ : C(Z, N))
    (hσ : ∀ z, π (σ z) = eQ z) (q : Q) :
    π (coordinateQuotientSection eQ σ q) = q :=
  (hσ (eQ.symm q)).trans (eQ.apply_symm_apply q)

/-- The counted probe endpoint is exactly kernel coordinate times section
coordinate in the original Haar product cell. -/
theorem reparametrized_probe_first
    [Mul N] (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I)
    (ι : I → N) (inc : K → N) (hι : ∀ i, inc (eI i) = ι i)
    (σ : C(Z, N)) (probe : B × U → N)
    (hprobe : ∀ y, probe y = ι y.2.val * σ y.1.val)
    (y : (eQ '' B) ×ˢ (eI '' U)) :
    probe (sectionProbeCoordinates eQ eI B U y) =
      inc y.val.2 * coordinateQuotientSection eQ σ y.val.1 := by
  rw [hprobe, ← hι]
  rw [sectionProbeCoordinates_snd]
  rfl

end PolycyclicRecognition

end

end OAI
