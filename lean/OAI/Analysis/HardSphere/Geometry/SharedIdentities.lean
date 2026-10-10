import Mathlib
import OAI.Analysis.HardSphere.Allocation.CoarsePhysical
import OAI.Analysis.HardSphere.Conditioning.SharedTransport

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
attribute [local instance] Classical.propDecidable
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

omit [Fintype I] in
lemma ambientShared_map (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,Y i))) (hA : MeasurableSet A) (e : E) :
    (ambientSharedKernel s σ hσ ξ ρ
      ((fun p : E×(∀i,X i) ↦ (p.1,routeConfigMap f p.2)) ⁻¹' A) e).map
        (routePairedMap f s σ)=
    ambientSharedKernel s σ hσ (ξ.map (routeConfigMap f))
      (fun i ↦ (ρ i).map (Prod.map (f i) (f (σ.symm i)))) A e := by
  rw [ambientSharedKernel_apply_measure,ambientSharedKernel_apply_measure,
    Kernel.map_apply _ (routeConfigMap_measurable f hf)]
  apply coarse_joint_reference (ξ e) _ _ _ (routeConfigMap_measurable f hf)
    (fun p ↦ routeFactorMap f s σ p.2) ((routeFactorMap_measurable f hf s σ).comp measurable_snd)
  exact ae_of_all _ (fun x ↦ ambientRefresh_map f hf s σ hσ ρ A hA e x)

variable {J : Type*} [Fintype J] [DecidableEq J] {L : HardSphere.Length}

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma ambientFirst_updated (s : Finset I) (σ : Equiv.Perm I)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)=
      ambientFirst s σ (x,p) := by
  funext i
  by_cases hi : i∈s
  · simp only [ambientFirst,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientFirst,Function.updateFinset,dite_eq_right hi]

omit [Fintype I] in
lemma ambientSecond_updated (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (partialReversePairs σ s hσ (Function.updateFinset (fun i ↦ (x i,z i)) s p) i).1)=
      ambientSecond s σ hσ (x,p) := by
  rw [partialReverse_update]
  funext i
  by_cases hi : i∈s
  · simp only [ambientSecond,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientSecond,Function.updateFinset,dite_eq_right hi,
      partialReversePairs_outside_fst σ s hσ _ i hi]

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_both (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (p : ∀i,X i×X (σ.symm i)) :
    p∈retainedEvent (routeChecks σ s hσ r anchor allowed label get hg) Finset.univ ↔
      (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      (fun i ↦ (partialReversePairs σ s hσ p i).1)∈
        retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ := by
  constructor
  · intro hp
    refine ⟨routeChecks_primary σ s hσ r anchor allowed label get hg _ p hp,?_⟩
    intro e _
    rcases e with ⟨b,e⟩
    change ¬TrialCollision r
      (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
      (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val
    rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1]
    exact hp (true,e) (Finset.subset_univ _)
  · rintro ⟨hp,hq⟩ ⟨b,e⟩ _
    cases b
    · exact hp (false,e) (Finset.subset_univ _)
    · have h := hq (false,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val at h
      rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1] at h
      exact h

omit [Fintype J] [DecidableEq J] in
lemma ambient_proposalEvent (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (z : ∀i,X (σ.symm i)) :
    {p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) |
      ambientFirst s σ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      ambientSecond s σ hσ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ} =
    proposalEvent (routeChecks σ s hσ r anchor allowed label get hg) s (Finset.univ\s) z := by
  ext p
  simp only [proposalEvent,mem_ofPred_eq,Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [routeChecks_both,ambientFirst_updated,ambientSecond_updated]

lemma ambientRefresh_constant (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (z : ∀i,X (σ.symm i)) (e : E) (x : ∀i,X i) :
    ambientRefreshKernel s σ hσ (fun i ↦ Kernel.const E ((μ i).compProd (κ i)))
      (Prod.snd ⁻¹' retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ) (e,x)=
    proposalKernel (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) z x := by
  rw [ambientRefreshKernel_apply _ _ _ _ _
      ((measurableSet_retainedEvent _ _).preimage measurable_snd),proposalKernel_apply]
  simp only [Kernel.const_apply]
  have he := congrArg (fun A ↦ Prod.mk x ⁻¹' A)
    (ambient_proposalEvent σ s hσ r anchor allowed label get hg z)
  change conditionedMeasure _ _=conditionedMeasure _ _
  congr 1

lemma ambient_two_primary_laws (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (heq : ∀i,i≠star→μ i=ν i)
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) (e : E) :
    let R := primaryChecks r anchor allowed label get hg
    let C := routeChecks σ s hσ r anchor allowed label get hg
    let C' := routeChecks σ.symm s (reverse_fix σ s hσ) r anchor allowed label get hg
    let P := conditionedMeasure (Measure.pi μ) (retainedEvent R Finset.univ)
    let Q := conditionedMeasure (Measure.pi ν) (retainedEvent R Finset.univ)
    let T := ambientSharedKernel s σ hσ (Kernel.const E P)
      (fun i ↦ Kernel.const E ((μ i).compProd (κ i))) (Prod.snd ⁻¹' retainedEvent R Finset.univ) e
    T.map (ambientFirst s σ)=
      P.withDensity (fun x ↦ conditionalLikelihood R C μ κ s (Finset.univ\s) x z) ∧
    T.map (ambientSecond s σ hσ)=
      Q.withDensity (fun x ↦ conditionalLikelihood R C' ν η s (Finset.univ\s) x w) := by
  dsimp only
  rw [ambientSharedKernel_apply_measure,Kernel.const_apply]
  have hk : (ambientRefreshKernel s σ hσ
      (fun i : s ↦ Kernel.const E ((μ i).compProd (κ i)))
      (Prod.snd ⁻¹' retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).comap
        (Prod.mk e) measurable_prodMk_left=
      proposalKernel (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) z := by
    ext x A hA
    exact congrArg (fun m ↦ m A) (ambientRefresh_constant σ s hσ r anchor allowed label get hg μ κ z e x)
  rw [hk]
  exact actual_two_primary_laws σ s hσ r anchor allowed label get hg star hstar hs μ ν heq κ η he z w

end HardSphere.Comparison
end
end

end OAI
