import Mathlib
import OAI.Analysis.HardSphere.Bridges.RouteFrozen
import OAI.Analysis.HardSphere.Comparison.ActualOutside

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma actual_reverse_trimmed {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (P Q : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (P i)] [∀i,IsProbabilityMeasure (Q i)]
    (hPQ : ∀i,i≠star→P i=Q i)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    ((conditionedMeasure (Measure.pi P) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).compProd
      (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z)).map
      (fun p ↦ ((fun i : {i // i∉s} ↦ p.1 i),reverseSelected σ s hf p.2))=
    ((conditionedMeasure (Measure.pi Q) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).compProd
      (proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) ν η s (Finset.univ\s) w)).map
      (fun p ↦ ((fun i : {i // i∉s} ↦ p.1 i),p.2)) := by
  let A := retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ
  let π : ((∀i,X i)×(∀i:s,X i×X (σ i)))→((∀i:{i // i∉s},X i)×(∀i:s,X i×X (σ i))) :=
    fun p ↦ ((fun i ↦ p.1 i),p.2)
  have hπ : Measurable π := by fun_prop
  have hh := congrArg (fun M ↦ M.map π)
    (full_paired_reverse σ s hf r anchor allowed label get hg μ ν κ η he z w
      (conditionedMeasure (Measure.pi P) A))
  rw [Measure.map_map hπ (measurable_id.prodMap (reverseSelected σ s hf).measurable)] at hh
  apply hh.trans
  apply conditioned_kernel_ignore P Q star hPQ A (measurableSet_retainedEvent _ _)
    (primaryChecks_ignore_star r anchor allowed label get hg star hstar Finset.univ)
    _ (proposalKernel_ignore_selected _ ν η s (Finset.univ\s) w star hs) π hπ
  intro x y p
  change ((fun i : {i // i∉s} ↦ (Function.update x star y) i),p) = ((fun i : {i // i∉s} ↦ x i),p)
  congr 1
  funext i
  exact Function.update_of_ne (show (i:I)≠star from fun h ↦ i.property (h.symm ▸ hs)) y x

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

def rebuildPrimary (s : Finset I)
    (p : ((∀i:{i // i∉s},X i)×(∀i:s,X i×Y i))) : ∀i,X i :=
  fun i ↦ if hi : i∈s then (p.2 ⟨i,hi⟩).1 else p.1 ⟨i,hi⟩

omit [Fintype I] in
lemma rebuildPrimary_measurable (s : Finset I) : Measurable (rebuildPrimary (X:=X) (Y:=Y) s) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈s
  · simpa only [rebuildPrimary,dite_eq_left hi,Function.comp_def] using
      measurable_fst.comp ((measurable_pi_apply (⟨i,hi⟩:s)).comp measurable_snd)
  · simpa only [rebuildPrimary,dite_eq_right hi,Function.comp_def] using
      (measurable_pi_apply (⟨i,hi⟩:{i // i∉s})).comp measurable_fst

omit [Fintype I] [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)] in
lemma rebuildPrimary_trim (s : Finset I) (x : ∀i,X i) (p : ∀i:s,X i×Y i) :
    rebuildPrimary s ((fun i ↦ x i),p)=Function.updateFinset x s (fun i ↦ (p i).1) := by
  funext i
  by_cases hi : i∈s <;> simp [rebuildPrimary,Function.updateFinset,hi]

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma actual_two_primary_laws {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (heq : ∀i,i≠star→μ i=ν i)
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    let R := primaryChecks r anchor allowed label get hg
    let C := routeChecks σ s hf r anchor allowed label get hg
    let C' := routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg
    let P := conditionedMeasure (Measure.pi μ) (retainedEvent R Finset.univ)
    let Q := conditionedMeasure (Measure.pi ν) (retainedEvent R Finset.univ)
    let T := P.compProd (proposalKernel C μ κ s (Finset.univ\s) z)
    T.map (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (p.2 i).1))=
      P.withDensity (fun x ↦ conditionalLikelihood R C μ κ s (Finset.univ\s) x z) ∧
    T.map (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (reverseSelected σ s hf p.2 i).1))=
      Q.withDensity (fun x ↦ conditionalLikelihood R C' ν η s (Finset.univ\s) x w) := by
  dsimp only
  refine ⟨full_primary_law _ _ μ κ s z (fun y u ↦ routeChecks_primary_weight σ s hf r anchor allowed label get hg Finset.univ (fun i ↦ (y i,u i))),?_⟩
  have h := congrArg (fun M ↦ M.map (rebuildPrimary (X:=X) (Y:=fun i ↦ X (σ i)) s))
    (actual_reverse_trimmed σ s hf r anchor allowed label get hg star hstar hs μ ν heq μ ν κ η he z w)
  rw [Measure.map_map (rebuildPrimary_measurable s) (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) ↦ ((fun i:{i // i∉s} ↦ p.1 i), reverseSelected σ s hf p.2)) from
      (Measurable.of_eval (fun i ↦ (measurable_pi_apply i.val).comp measurable_fst)).prodMk ((reverseSelected σ s hf).measurable.comp measurable_snd)),
    Measure.map_map (rebuildPrimary_measurable s) (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×X (σ i)) ↦ ((fun i:{i // i∉s} ↦ p.1 i), p.2)) from by fun_prop)] at h
  simp only [Function.comp_def,rebuildPrimary_trim] at h
  rw [h]
  exact full_primary_law _ _ ν η s w
    (fun y u ↦ routeChecks_primary_weight σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg Finset.univ (fun i ↦ (y i,u i)))

end HardSphere.Bridge

end
end

end

end OAI
