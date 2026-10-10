import Mathlib
import OAI.Analysis.HardSphere.Bridges.JointCollision
import OAI.Analysis.HardSphere.Geometry.DependentChecks

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison CellOrbital Groups
attribute [local instance] Classical.propDecidable

lemma normalized_marginal_collision {X : Type*} [MeasurableSpace X]
    {L : Length} {S : Set C(Time,Point)} (μ : Measure X) (P : Measure S)
    (f : X → S) (hf : Measurable f) {G q : ℝ≥0∞} (hdom : μ.map f ≤ G • P)
    (r : ℝ) (g : C(Time,Point))
    (hq : P {u | TrialCollision (L:=L) r (projectCurve L g) u.val} ≤ q) :
    μ {x | TrialCollision (L:=L) r (projectCurve L g) (f x).val} ≤ G*q := by
  have hm : MeasurableSet {u : S | TrialCollision (L:=L) r (projectCurve L g) u.val} :=
    (trialCollision_closed r (projectCurve L g)).measurableSet.preimage measurable_subtype_coe
  have h := hdom {u | TrialCollision (L:=L) r (projectCurve L g) u.val}
  rw [Measure.map_apply hf hm,Measure.smul_apply,smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl hq)

variable {I J E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype E]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (allowed : J → Set C(Time,Point))
  (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
  (color : E → Bool) (labelL labelR : E → J) (hdiff : ∀e,labelL e ≠ labelR e)
  (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))

def factorPathCheck (r : ℝ) : E → LocalCheck V :=
  dependentCheck (fun f g : C(Time,Point) ↦ ¬TrialCollision (L:=L) r (projectCurve L g) f)
    (jointCollision_closed (L:=L) r).measurableSet.compl
    (fun e ↦ owner (color e) (labelL e)) (fun e ↦ owner (color e) (labelR e))
    (fun e x ↦ (path (color e) (labelL e) x).val)
    (fun e x ↦ (path (color e) (labelR e) x).val)
    (fun e ↦ measurable_subtype_coe.comp (hpath (color e) (labelL e)))
    (fun e ↦ measurable_subtype_coe.comp (hpath (color e) (labelR e)))

omit [Fintype I] [Fintype J] in
include howner hdiff in
lemma factorPath_insertion (r : ℝ) (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (D : ℕ) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j) ≤ G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision (L:=L) r (projectCurve L g.val) f.val} ≤ q)
    (hdegree : ∀i∈U,(Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i)).card ≤ D)
    (hsmall : a+(D:ℝ≥0∞)*(G*q) ≤ 1) :
    UniformInsertionOn (factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r) μ a U := by
  apply dependent_insertion _ _ _ _ (fun e ↦ fun h ↦ hdiff e (howner (color e) h))
    _ _ _ _ μ (fun _ _ ↦ G*q) a U
  · intro e he g
    simpa only [not_not] using normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelR e) g).val (hq _ _ (hdiff e) _)
  · intro e he f
    have h := normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelL e) f).val (hq _ _ (hdiff e).symm _)
    have hh : {g | ¬¬TrialCollision (L:=L) r (projectCurve L (path (color e) (labelR e) g).val)
        (path (color e) (labelL e) f).val}=
      {g | TrialCollision (L:=L) r (projectCurve L (path (color e) (labelL e) f).val)
        (path (color e) (labelR e) g).val} := by
      ext g
      simp only [mem_ofPred_eq,not_not]
      exact physicalPairCheck_symmetric r _ _
    rw [hh]
    exact h
  · intro i hi
    have hd := hdegree i hi
    have he : (Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support))=
        Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton]
      exact or_congr eq_comm eq_comm
    change a+(∑_e∈Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support),G*q) ≤ 1
    rw [he,Finset.sum_const, nsmul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hd) le_rfl)).trans hsmall

end HardSphere.Bridge

end
end

end

end OAI
