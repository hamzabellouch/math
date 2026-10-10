import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridAllocation
import OAI.Analysis.HardSphere.Geometry.SiteGroups
import OAI.Analysis.HardSphere.Bridges.PhysicalPair

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

abbrev PhysicalDatum (N K M G : ℕ) (L : Length) :=
  Configuration N L × Configuration N L × (Fin N → Bool) ×
    GridAllocation N K (G*M) × (Fin N → ConfigurationPath 1 L)

def physicalDatum {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (z : ConfigurationPath N L × GridAllocation N K (G*M)) : PhysicalDatum N K M G L :=
  (z.1 0,z.1 1,(fun i ↦ decide (∃v : Fin 3 → Fin K,
    Eligible m r R C S s₀ u v i z.1)),z.2,
    fun i ↦ if i∈groupUnion g z.2 then 0 else onePathAt i z.1)

lemma physicalDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) :
    Measurable (physicalDatum (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u) := by
  unfold physicalDatum
  apply ((continuous_eval_const 0).measurable.comp measurable_fst).prodMk
  apply ((continuous_eval_const 1).measurable.comp measurable_fst).prodMk
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    have h : MeasurableSet {z : ConfigurationPath N L × GridAllocation N K (G*M) |
        ∃v : Fin 3 → Fin K, Eligible m r R C S s₀ u v i z.1} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun v ↦
        (eligible_measurable m r R C S s₀ u v i).preimage measurable_fst
    apply measurable_to_countable'
    intro b
    cases b
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_false_iff_not,←Set.compl_ofPred] using h.compl
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using h
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  apply Measurable.ite
    (measurable_snd ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet))
    measurable_const
  exact (onePathAt_continuous i).measurable.comp measurable_fst

def physicalDatumLaw {N K M G : ℕ} {L : Length} (g : Fin G)
    (ψ : Jet N L) (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    Measure (PhysicalDatum N K M G L) :=
  ((groundPathLaw N L r T ψ).compProd
    (physicalAllocationKernel (K:=K) m (G*M) r R C S s₀ u)).map
      (physicalDatum g m r R C S s₀ u)

lemma physicalDatumLaw_probability {N K M G : ℕ} {L : Length} (g : Fin G)
    {ψ : Jet N L} {r : ℝ} (hψ : IsGroundVector N L r ψ)
    (m : ℕ) (R C S s₀ T : ℝ) (hT : 0≤T) (u : Time) :
    IsProbabilityMeasure (physicalDatumLaw (K:=K) (M:=M) g ψ m r R C S s₀ T u) := by
  have := hψ.groundPathLaw_probability hT
  unfold physicalDatumLaw
  infer_instance

def datumSelected {N K M G : ℕ} {L : Length} (g : Fin G)
    (d : PhysicalDatum N K M G L) : Finset (Fin N) := groupUnion g d.2.2.2.1

def datumHome {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Fin 3 → Fin K := gridHome hL (d.1 i)

def anchorPoint {K : ℕ} (v : Fin 3 → Fin K) : Point := fun j ↦ ((v j).val:ℝ)

lemma anchorPoint_project {K : ℕ} (L : Length) (v : Fin 3 → Fin K) :
    projectPoint L (anchorPoint v)=gridCenter L v := rfl

def datumStart {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Point :=
  nearestLift L (anchorPoint (datumHome hL d i)) (d.1 i)

def datumEnd {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Point :=
  nearestLift L (anchorPoint (datumHome hL d i)) (d.2.1 i)

lemma datumHome_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumHome hL d i) :=
  (gridHome_measurable hL).comp ((measurable_pi_apply i).comp measurable_fst)

lemma datumAnchor_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ anchorPoint (datumHome hL d i)) :=
  (measurable_of_countable (anchorPoint (K:=K))).comp (datumHome_measurable hL i)

lemma nearestLift_measurable (L : Length) :
    Measurable (fun p : Point × Torus L ↦ nearestLift L p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_subtype_coe.comp ((AddCircle.measurableEquivIco L.val (-L.val/2)).measurable.comp
    (((measurable_pi_apply j).comp measurable_snd).sub
      (AddCircle.measurable_mk'.comp ((measurable_pi_apply j).comp measurable_fst))))).add
    ((measurable_pi_apply j).comp measurable_fst)

lemma datumStart_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumStart hL d i) := by
  unfold datumStart
  exact (nearestLift_measurable L).comp
    ((datumAnchor_measurable hL i).prodMk ((measurable_pi_apply i).comp measurable_fst))

lemma datumEnd_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumEnd hL d i) := by
  unfold datumEnd
  exact (nearestLift_measurable L).comp
    ((datumAnchor_measurable hL i).prodMk ((measurable_pi_apply i).comp measurable_snd.fst))

lemma datumFrozen_measurable {N K M G : ℕ} {L : Length} (j : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ d.2.2.2.2 j) :=
  (measurable_pi_apply j).comp (measurable_snd.snd.snd.snd)

attribute [local irreducible] TrialCollision

lemma datumFrozen_collision_measurable {N K M G : ℕ} {L : Length}
    (j : Fin N) (r : ℝ) :
    MeasurableSet {p : PhysicalDatum N K M G L × C(Time,Point) |
      TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2} :=
  by
  have hm : Measurable (fun p : PhysicalDatum N K M G L × C(Time,Point) ↦
      (p.1.2.2.2.2 j,p.2)) :=
    (((datumFrozen_measurable (K:=K) (M:=M) (G:=G) (L:=L) j).comp measurable_fst).prodMk measurable_snd)
  have H : MeasurableSet {q : ConfigurationPath 1 L × C(Time,Point) | TrialCollision (L:=L) r q.1 q.2} :=
    (trialCollision_joint_closed (L:=L) r).measurableSet
  exact hm H

def datumPermitted {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) :
    Set (PhysicalDatum N K M G L × C(Time,Point)) :=
  {p | Regular m r R C u S (projectCurve L p.2) ∧
    TrialConfined L (anchorPoint (datumHome hL p.1 i)) p.2 ∧
    p.2∈fixedEndpoints (datumStart hL p.1 i) (datumEnd hL p.1 i) ∧
    ∀j, j∉datumSelected g p.1 → ¬TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2}

lemma datumPermitted_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) :
    MeasurableSet (datumPermitted (M:=M) hL g m r R C S u i) := by
  apply ((regular_measurable m r R C u S).preimage
    ((projectCurve_continuous L).measurable.comp measurable_snd)).inter
  apply ((trialConfined_joint_closed L).measurableSet.preimage
    (((datumAnchor_measurable hL i).comp measurable_fst).prodMk measurable_snd)).inter
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      ((datumStart_measurable hL i).comp measurable_fst)).inter
      (measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        ((datumEnd_measurable hL i).comp measurable_fst))
  simp only [imp_iff_not_or,not_not]
  change MeasurableSet {p : PhysicalDatum N K M G L × C(Time,Point) | ∀j,
    j∈datumSelected g p.1 ∨ ¬TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.union
  · exact (measurable_fst.snd.snd.snd.fst)
      ((Set.to_countable {a : GridAllocation N K (G*M) | j∈groupUnion g a}).measurableSet)
  · exact (datumFrozen_collision_measurable (K:=K) (M:=M) (G:=G) (L:=L) j r).compl

end HardSphere.Groups
end
end

end OAI
