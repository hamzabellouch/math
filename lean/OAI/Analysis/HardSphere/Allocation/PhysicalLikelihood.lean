import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalLifted
import OAI.Analysis.HardSphere.Bridges.RouteAuxiliary

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physicalOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (i : Option J) : IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d) := by
    cases i with
    | none => exact inferInstanceAs (IsProbabilityMeasure (cellPathReference v))
    | some i => exact hp i
  exact physicalSlotOn_probability hL g m t r R C S u particle v d i

omit [Fintype J] in
theorem physical_auxiliary_exists {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
    let σ := routePermutation labels
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d
    ∃ (κ : ∀i,Kernel (X i) (X (σ.symm i))) (η : ∀i,Kernel (X i) (X (σ i))),
      (∀i,IsFiniteKernel (κ i)) ∧ (∀i,IsFiniteKernel (η i)) ∧
      (∀i:routeSlots labels,(μ i).compProd (κ i)=ρ i) ∧
      (∀i,((μ (σ i)).compProd (κ (σ i))).map (reverseFactor (X:=X) σ i)=(ν i).compProd (η i)) ∧
      (∀i x,κ i x univ≤routeDensityBound t) ∧ (∀i x,η i x univ≤routeDensityBound t) ∧
      (∀i,∫⁻x,κ i x univ ∂μ i=1) ∧ (∀i,∫⁻x,η i x univ ∂ν i=1) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have : ∀i,IsProbabilityMeasure (ν i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have hρ := physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess
  have : ∀i,IsProbabilityMeasure (ρ i) := fun i ↦ (hρ i).1
  let ρ' := extendSelectedPair σ s μ ν ρ
  have hh := extendSelectedPair_bounds σ s μ ν ρ (one_le_routeDensityBound t)
    (fun i ↦ (hρ i).2.2.2.1) (fun i ↦ (hρ i).2.2.2.2.1)
  obtain ⟨κ,η,hκf,hηf,hκe,hηe,hκb,hηb,hκm,hηm⟩ := exists_two_auxiliary σ μ ν ρ'
    (routeDensityBound_ne_top ht) (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)
  refine ⟨κ,η,hκf,hηf,?_,?_,hκb,hηb,hκm,hηm⟩
  · intro i
    exact (hκe i).trans (extendSelectedPair_selected σ s μ ν ρ i)
  · intro i
    rw [hκe,hηe]

theorem physical_two_likelihoods {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
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
      (physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (η i))
    (z : ∀i,physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))
    (w : ∀i,physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)) :
    let σ := routePermutation labels
    let s := routeSlots labels
    let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
    let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let R₀ := physicalOnChecks hL g m r R C S u particle d
    let C₀ := routeChecks σ s (routePermutation_fixed labels) r anchor allowed some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    let C₁ := routeChecks σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) r anchor allowed some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    let T := physicalSharedOn hL g m t r R C S u particle labels v steps d
    T.map (ambientFirst s σ)=
      (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity
        (fun x ↦ conditionalLikelihood R₀ C₀ μ κ s (Finset.univ\s) x z) ∧
    T.map (ambientSecond s σ (routePermutation_fixed labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity
        (fun x ↦ conditionalLikelihood R₀ C₁ ν η s (Finset.univ\s) x w) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have : ∀i,IsProbabilityMeasure (ν i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have heq : ∀i,i≠none→μ i=ν i := by
    intro i hi
    cases i with
    | none => exact (hi rfl).elim
    | some i => rfl
  have hs : none∈s := by
    exact Finset.mem_map.mpr ⟨Fin.last (n+1),Finset.mem_univ _,routeEmbedding_last labels⟩
  have h := ambient_two_primary_laws (X:=X) σ s (routePermutation_fixed labels) r
    (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    none (fun _ ↦ Option.some_ne_none _) hs μ ν heq κ η hr z w ()
  have hρ : (fun i:s ↦ Kernel.const Unit ((μ i).compProd (κ i)))=
      (fun i:s ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i)) := by
    funext i
    rw [he i]
  dsimp only at h
  simp only [hρ] at h
  exact h

end HardSphere.Groups
end
end

end OAI
