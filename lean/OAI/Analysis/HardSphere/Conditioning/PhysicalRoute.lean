import Mathlib
import OAI.Analysis.HardSphere.Conditioning.RoutePartition
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteFactors

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {J : Type*}

def routePosition {d : ℕ} (labels : Fin d↪J) (i : routeSlots labels) : Fin (d+1) :=
  (Finset.mem_map.mp i.property).choose

lemma routeEmbedding_position {d : ℕ} (labels : Fin d↪J) (i : routeSlots labels) :
    routeEmbedding labels (routePosition labels i)=i.val :=
  (Finset.mem_map.mp i.property).choose_spec.2

def routeSlotEquiv {d : ℕ} (labels : Fin d↪J) : Fin (d+1) ≃ routeSlots labels where
  toFun k := ⟨routeEmbedding labels k,Finset.mem_map.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
  invFun := routePosition labels
  left_inv _ := (routeEmbedding labels).injective (routeEmbedding_position labels _)
  right_inv _ := Subtype.ext (routeEmbedding_position labels _)

lemma routePermutation_symm_first {n : ℕ} (labels : Fin (n+1)↪J) :
    (routePermutation labels).symm (routeEmbedding labels 0)=none := by
  apply (routePermutation labels).injective
  rw [Equiv.apply_symm_apply,routePermutation_star]
  exact routeEmbedding_castSucc labels 0

lemma routePermutation_symm_later {n : ℕ} (labels : Fin (n+1)↪J)
    (k : Fin (n+2)) (hk : k.val≠0) :
    (routePermutation labels).symm (routeEmbedding labels k)=
      some (labels ⟨k.val-1,by omega⟩) := by
  apply (routePermutation labels).injective
  rw [Equiv.apply_symm_apply,routePermutation_label]
  congr 1
  exact Fin.ext (by simp only [Fin.val_succ];omega)

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*}

def physicalSlotReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    Option J→Kernel (PhysicalDatum N K M G L) C(Time,Point)
  | none => Kernel.const _ (cellPathReference v)
  | some i => datumIndividualReference hL g m r R C S t u (particle i)

instance physicalSlotReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (i : Option J) :
    IsFiniteKernel (physicalSlotReference (M:=M) hL g m t r R C S u particle v i) := by
  cases i <;> dsimp only [physicalSlotReference] <;> infer_instance

lemma physicalSlot_first {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) :
    physicalSlotReference hL g m t r R C S u particle (v (Fin.last (n+1)))
      (routeEmbedding labels k) d=routeFirstReference hL g m t r R C S u (labels.trans particle) v k d := by
  by_cases hk : k.val<n+1
  · have he : routeEmbedding labels k=some (labels ⟨k.val,hk⟩) := routeEmbedding_castSucc labels ⟨k.val,hk⟩
    rw [he]
    simp only [routeFirstReference,dite_eq_left hk,physicalSlotReference,Function.Embedding.trans_apply]
  · have he : k=Fin.last (n+1) := Fin.ext (by simp only [Fin.val_last];omega)
    subst k
    rw [routeEmbedding_last]
    simp only [routeFirstReference,Fin.val_last,lt_self_iff_false,↓reduceDIte,physicalSlotReference,Kernel.const_apply]

lemma physicalSlot_second {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) :
    physicalSlotReference hL g m t r R C S u particle (v 0)
      ((routePermutation labels).symm (routeEmbedding labels k)) d=
      routeSecondReference hL g m t r R C S u (labels.trans particle) v k d := by
  by_cases hk : k.val=0
  · have he : k=0 := Fin.ext hk
    subst k
    rw [routePermutation_symm_first]
    simp only [routeSecondReference,Fin.val_zero,↓reduceDIte,physicalSlotReference,Kernel.const_apply]
  · rw [routePermutation_symm_later labels k hk]
    simp only [routeSecondReference,dite_eq_right hk,physicalSlotReference,Function.Embedding.trans_apply]

def physicalSelectedFactor {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (i : routeSlots labels) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  physicalRouteFactor hL g m t r R C S u (labels.trans particle) v steps (routePosition labels i)

instance physicalSelectedFactor_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (i : routeSlots labels) :
    IsFiniteKernel (physicalSelectedFactor (M:=M) hL g m t r R C S u particle labels v steps i) :=
  physicalRouteFactor_finite ..

theorem physicalSelectedFactor_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (i : routeSlots labels) :
    let ρ := physicalSelectedFactor hL g m t r R C S u particle labels v steps i d
    let P := physicalSlotReference hL g m t r R C S u particle (v (Fin.last (n+1))) i d
    let Q := physicalSlotReference hL g m t r R C S u particle (v 0) ((routePermutation labels).symm i) d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst≤routeDensityBound t • P ∧ ρ.snd≤routeDensityBound t • Q ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only [physicalSelectedFactor]
  rw [←routeEmbedding_position labels i,physicalSlot_first,physicalSlot_second]
  exact physicalRouteFactor_physical hL g m t r R C S ht u (labels.trans particle) v steps hc d hhome haccess _

end HardSphere.Groups
end
end

end OAI
