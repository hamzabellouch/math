import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalSupported
import OAI.Analysis.HardSphere.Bridges.RouteAuxiliary

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups
variable {I J : Type*} [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_map_measure (μ : ∀i,Measure (X i)) {i j : I} (h : i=j) :
    (μ i).map (fiberEquiv h)=μ j := by
  subst j
  change (μ i).map id=μ i
  exact Measure.map_id

omit [Fintype I] in
theorem routePath_marginal_le (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i,Measure (X i×X (σ.symm i)))
    (G : ℝ≥0∞) (heq : ∀j,μ (label j)=ν (label j))
    (hl : ∀i∈s,(ρ i).fst≤G • μ i) (hr : ∀i∈s,(ρ i).snd≤G • ν (σ.symm i))
    (b : Bool) (j : J) (hs : routeOwner σ label b j∈s) :
    (ρ (routeOwner σ label b j)).map (routePath σ s hf allowed label get b j)≤
      G • (μ (label j)).map (get j) := by
  cases b
  · change (ρ (label j)).map (fun p ↦ get j p.1)≤_
    have hh := (Measure.map_mono (f:=get j) (hl _ hs) (hg j)).trans_eq
      (Measure.map_smul _ (hg j).aemeasurable)
    simpa only [Measure.fst,Measure.map_map (hg j) measurable_fst,Function.comp_def] using hh
  · have hj : label j∈s := (move_mem_iff σ s hf (label j)).mp hs
    simp only [routePath,dite_eq_left hj]
    have hm : Measurable (fun p : X (σ.symm (σ (label j))) ↦
        get j (fiberEquiv (σ.symm_apply_apply (label j)) p)) :=
      (hg j).comp (fiberEquiv _).measurable
    have hmap := Measure.map_mono (f:=(fun p : X (σ.symm (σ (label j))) ↦
      get j (fiberEquiv (σ.symm_apply_apply (label j)) p))) (hr _ hs) hm
    rw [Measure.map_smul G hm.aemeasurable] at hmap
    have hc : (ν (σ.symm (σ (label j)))).map (fun p ↦
        get j (fiberEquiv (σ.symm_apply_apply (label j)) p))=(μ (label j)).map (get j) := by
      calc
        _ = ((ν (σ.symm (σ (label j)))).map (fiberEquiv (σ.symm_apply_apply (label j)))).map (get j) :=
          (Measure.map_map (hg j) (fiberEquiv _).measurable).symm
        _ = _ := by rw [fiberEquiv_map_measure,←heq j]
    rw [hc] at hmap
    change (ρ (σ (label j))).map (fun p ↦ get j (fiberEquiv (σ.symm_apply_apply (label j)) p.2))≤_
    rw [Measure.snd,Measure.map_map hm measurable_snd] at hmap
    exact hmap

end HardSphere.Bridge
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener Comparison GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma reverseFactor_snd (σ : Equiv.Perm I) (j : I)
    (ρ : Measure (X (σ j)×X (σ.symm (σ j)))) :
    (ρ.map (reverseFactor σ j)).snd=ρ.fst := by
  rw [Measure.snd,Measure.fst,Measure.map_map measurable_snd (reverseFactor σ j).measurable]
  rfl

omit [Fintype I] in
lemma reverse_pair_bounds (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (μ ν : ∀i,Measure (X i))
    (ρ : ∀i,Measure (X i×X (σ.symm i))) (θ : ∀i,Measure (X i×X (σ i)))
    (G : ℝ≥0∞) (he : ∀i∈s,(ρ (σ i)).map (reverseFactor σ i)=θ i)
    (hl : ∀i∈s,(ρ i).fst≤G • μ i) (hr : ∀i∈s,(ρ i).snd≤G • ν (σ.symm i)) :
    (∀i∈s,(θ i).fst≤G • ν i) ∧ (∀i∈s,(θ i).snd≤G • μ (σ i)) := by
  constructor
  · intro i hi
    rw [←he i hi,reverseFactor_fst]
    have hh := Measure.map_mono (hr _ ((move_mem_iff σ s hf i).mpr hi))
      (fiberEquiv (σ.symm_apply_apply i)).measurable
    rwa [Measure.map_smul _ (fiberEquiv (σ.symm_apply_apply i)).measurable.aemeasurable,
      fiberEquiv_map_measure] at hh
  · intro i hi
    rw [←he i hi,reverseFactor_snd]
    exact hl _ ((move_mem_iff σ s hf i).mpr hi)
end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable

omit [Fintype J] in
lemma route_selected_accessible {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (labels : Fin n↪J) (d : PhysicalDatum N K M G L)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (j : J) (h : some j∈routeSlots labels) :
    datumAccessible hL g m t r R C S u (particle j) d := by
  rw [routeSlots_exact] at h
  rcases Finset.mem_insert.mp h with h|h
  · contradiction
  · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    rw [←Option.some.inj he]
    exact ha i

omit [Fintype J] in
theorem physical_auxiliary_path_bounds {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (κ : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)))
    [∀i,IsFiniteKernel (η i)]
    (he : ∀i:routeSlots labels,
      (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (κ i)=
        physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (hr : ∀i:routeSlots labels,
      ((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
        (κ (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
          (routePermutation labels) i)=
      (physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (η i)) :
    let σ := routePermutation labels
    let s := routeSlots labels
    let A := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    (∀b j,routeOwner σ some b j∈s→
      ((μ (routeOwner σ some b j)).compProd (κ (routeOwner σ some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ s (routePermutation_fixed labels) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • μ (some j)) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (η (routeOwner σ.symm some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • ν (some j)) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  let ρ := fun i ↦ (μ i).compProd (κ i)
  let θ := fun i ↦ (ν i).compProd (η i)
  have hl : ∀i∈s,(ρ i).fst≤routeDensityBound t • μ i := by
    intro i hi
    change ((μ i).compProd (κ i)).fst≤_
    rw [he ⟨i,hi⟩]
    exact (physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess ⟨i,hi⟩).2.2.2.1
  have hs : ∀i∈s,(ρ i).snd≤routeDensityBound t • ν (σ.symm i) := by
    intro i hi
    change ((μ i).compProd (κ i)).snd≤_
    rw [he ⟨i,hi⟩]
    exact (physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess ⟨i,hi⟩).2.2.2.2.1
  have hb := reverse_pair_bounds σ s (routePermutation_fixed labels) μ ν ρ θ (routeDensityBound t)
    (fun i hi ↦ hr ⟨i,hi⟩) hl hs
  constructor
  · intro b j hj
    simpa only [μ,ν,ρ,θ,σ,s,Measure.map_id'] using routePath_marginal_le (X:=X) σ s (routePermutation_fixed labels)
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id) μ ν ρ
      (routeDensityBound t) (fun _ ↦ rfl) hl hs b j hj
  · intro b j hj
    simpa only [μ,ν,ρ,θ,σ,s,Measure.map_id',Equiv.symm_symm] using routePath_marginal_le (X:=X) σ.symm s
      (reverse_fix σ s (routePermutation_fixed labels)) (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some
      (fun _ f ↦ f) (fun _ ↦ measurable_id) ν μ θ (routeDensityBound t)
      (fun _ ↦ rfl) hb.1 hb.2 b j hj

end HardSphere.Groups
end
end

end OAI
