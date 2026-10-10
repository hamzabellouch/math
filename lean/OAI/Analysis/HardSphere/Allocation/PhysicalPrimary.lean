import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SharedTransport
import OAI.Analysis.HardSphere.Conditioning.PhysicalRoute

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma conditioned_prod_univ (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (A : Set X) :
    conditionedMeasure (μ.prod ν) (Prod.fst ⁻¹' A)=(conditionedMeasure μ A).prod ν := by
  have he : Prod.fst ⁻¹' A=A ×ˢ (univ : Set Y) := by ext p; simp
  rw [he,conditionedMeasure,conditionedMeasure,Measure.prod_smul_left,
    Measure.prod_prod,measure_univ,mul_one,←Measure.prod_restrict,Measure.restrict_univ]

lemma conditioned_option {J : Type*} [Fintype J]
    (μ : Option J→Measure X) [∀i,IsFiniteMeasure (μ i)] [IsProbabilityMeasure (μ none)]
    (A : Set (J→X)) (hA : MeasurableSet A) :
    conditionedMeasure (Measure.pi μ) ((fun x : Option J→X ↦ fun i ↦ x (some i)) ⁻¹' A)=
    ((conditionedMeasure (Measure.pi fun i ↦ μ (some i)) A).prod (μ none)).map
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option J ↦ X)).symm := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option J ↦ X)
  have hB : MeasurableSet ((fun x : Option J→X ↦ fun i ↦ x (some i)) ⁻¹' A) :=
    hA.preimage (Measurable.of_eval fun i ↦ measurable_pi_apply (some i))
  rw [←Measure.pi_map_piOptionEquivProd μ,
    ←conditioned_map_preimage _ e.symm e.symm.measurable hB]
  change (conditionedMeasure _ (Prod.fst ⁻¹' A)).map e.symm = _
  rw [conditioned_prod_univ]

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalSlotMutual {L : Length} (r : ℝ) : Set (Option J→C(Time,Point)) :=
  (fun x ↦ fun i ↦ x (some i)) ⁻¹' physicalMutual (L:=L) r
omit [DecidableEq J] in
lemma physicalSlotMutual_measurable {L : Length} (r : ℝ) :
    MeasurableSet (physicalSlotMutual (J:=J) (L:=L) r) :=
  (physicalMutual_measurable r).preimage
    (Measurable.of_eval fun i ↦ measurable_pi_apply (some i))

def physicalPrimaryReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    Kernel (PhysicalDatum N K M G L) (Option J→C(Time,Point)) :=
  fiberNormalize (finiteKernelPi (physicalSlotReference hL g m t r R C S u particle v))
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r)

instance physicalPrimaryReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    IsFiniteKernel (physicalPrimaryReference (M:=M) hL g m t r R C S u particle v) := by
  unfold physicalPrimaryReference; infer_instance

omit [DecidableEq J] in
lemma physicalPrimaryReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    physicalPrimaryReference hL g m t r R C S u particle v d=
      conditionedMeasure (Measure.pi fun i ↦ physicalSlotReference hL g m t r R C S u particle v i d)
        (physicalSlotMutual (L:=L) r) := by
  unfold physicalPrimaryReference
  change (fiberRestrict _ _ d univ)⁻¹ • fiberRestrict _ _ d=_
  rw [fiberRestrict_apply _ ((physicalSlotMutual_measurable r).preimage measurable_snd)]
  simp only [Measure.restrict_apply_univ,finiteKernelPi_apply]
  rfl

theorem physicalPrimaryReference_actual {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    physicalPrimaryReference hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d=
      ((datumGroupReference hL g a m r R C S t u d).prod (cellPathReference v)).map
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm := by
  have : IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v none d) :=
    inferInstanceAs (IsProbabilityMeasure (cellPathReference v))
  rw [physicalPrimaryReference_apply,physicalSlotMutual,conditioned_option _ _ (physicalMutual_measurable r),
    datumGroupReference_apply]
  simp only [physicalSlotReference,Kernel.const_apply,datumIndividualReference_apply]

def physicalSharedRoute {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    Kernel (PhysicalDatum N K M G L)
      ((Option J→C(Time,Point))×(routeSlots labels→C(Time,Point)×C(Time,Point))) :=
  ambientSharedKernel (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
    (physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))))
    (physicalSelectedFactor hL g m t r R C S u particle labels v steps)
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r)

instance physicalSharedRoute_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    IsFiniteKernel (physicalSharedRoute (M:=M) hL g m t r R C S u particle labels v steps) := by
  unfold physicalSharedRoute; infer_instance

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalSlotAllowed {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) : Option J→Set C(Time,Point)
  | none => univ
  | some i => Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i)

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotAllowed_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    MeasurableSet (physicalSlotAllowed hL g m r R C S u particle d i) := by
  cases i with
  | none => exact MeasurableSet.univ
  | some i => exact (datumPermitted_measurable hL g m r R C S u (particle i)).preimage measurable_prodMk_left

def physicalSlotOn {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    (i : Option J)→Measure (physicalSlotAllowed hL g m r R C S u particle d i)
  | none => subtypeConditional (cellPathReference v) univ
  | some i => referenceOn t (datumStart hL d (particle i)) (datumEnd hL d (particle i))
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i))

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_map {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    (physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val=
      physicalSlotReference hL g m t r R C S u particle v i d := by
  cases i with
  | none =>
    change (subtypeConditional (cellPathReference v) (univ : Set C(Time,Point))).map
      Subtype.val=cellPathReference v
    rw [subtypeConditional_map _ MeasurableSet.univ,measure_univ,inv_one,
      one_smul,Measure.restrict_univ]
  | some i =>
    change (referenceOn t (datumStart hL d (particle i)) (datumEnd hL d (particle i))
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i))).map Subtype.val=
      datumIndividualReference hL g m r R C S t u (particle i) d
    rw [referenceOn_map _ _ _ ((datumPermitted_measurable hL g m r R C S u (particle i)).preimage
      measurable_prodMk_left),datumIndividualReference_apply]

instance physicalSlotOn_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    IsFiniteMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have hm := physicalSlotOn_map hL g m t r R C S u particle v d i
  have : IsFiniteMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [hm]; infer_instance
  exact Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J)
    [IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d)] :
    IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [physicalSlotOn_map]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

omit [Fintype J] [DecidableEq J] in
lemma physicalAllowed_confined {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : J)
    (f : physicalSlotAllowed hL g m r R C S u particle d (some i)) :
    Confined (projectPoint L (anchorPoint (datumHome hL d (particle i)))) (projectCurve L f.val) :=
  fun s ↦ (f.property.2.1 s).2

lemma physicalAllowed_checks {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (hr : r≤1) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :
    (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ⁻¹'
      physicalSlotMutual (L:=L) r=
    retainedEvent (primaryChecks r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
      some (fun _ f ↦ f) (fun _ ↦ measurable_id)) Finset.univ := by
  ext x
  constructor
  · intro hx e he
    exact hx e.2.val.1 e.2.val.2 e.2.property.1
  · intro hx
    let allowed := physicalSlotAllowed hL g m r R C S u particle d
    let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
    have hconf : ∀j,∀f : allowed (some j),Confined (anchor j) (projectCurve L f.val) :=
      physicalAllowed_confined hL g m r R C S u particle d
    have hh := physicalSparseChecks_complete (I:=Option J) (V:=fun i ↦ allowed i)
      r hr anchor (fun j ↦ allowed (some j)) hconf
      (fun _ ↦ some) (fun _ _ f ↦ f) (fun _ _ ↦ measurable_id) x hx
    exact hh false

lemma physicalPrimary_on_map {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (hr : r≤1) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    (conditionedMeasure (Measure.pi (physicalSlotOn hL g m t r R C S u particle v d))
      (retainedEvent (primaryChecks r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
        (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
        some (fun _ f ↦ f) (fun _ ↦ measurable_id)) Finset.univ)).map
      (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_)))=
      physicalPrimaryReference hL g m t r R C S u particle v d := by
  rw [←physicalAllowed_checks hL g m r R C S hr u particle d,
    physicalPrimaryReference_apply]
  exact (conditioned_pi_map (physicalSlotOn hL g m t r R C S u particle v d)
    (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))
    (fun _ ↦ measurable_subtype_coe) (physicalSlotMutual_measurable r)).trans
    (by simp only [physicalSlotOn_map])

end HardSphere.Groups
end
end

end OAI
