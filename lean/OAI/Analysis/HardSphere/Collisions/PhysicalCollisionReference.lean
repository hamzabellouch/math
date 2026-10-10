import Mathlib
import OAI.Analysis.HardSphere.Collisions.PhysicalCollision
import OAI.Analysis.HardSphere.Bridges.RouteMarginals

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [DecidableEq J]

def physicalCollisionReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J) :
    Measure (physicalSlotAllowed hL g m r R C S u particle d (some j)) :=
  if datumAccessible hL g m t r R C S u (particle j) d then
    physicalSlotOn hL g m t r R C S u particle (datumHome hL d (particle j)) d (some j) else 0

omit [DecidableEq J] in
lemma physicalCollisionReference_eq {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J)
    (ha : datumAccessible hL g m t r R C S u (particle j) d) (v : Fin 3→Fin K) :
    physicalCollisionReference hL g m t r R C S u particle d j=
      physicalSlotOn hL g m t r R C S u particle v d (some j) := by
  change (if datumAccessible hL g m t r R C S u (particle j) d then _ else _) = _
  rw [ite_eq_left ha]
  rfl

lemma routeOwner_mem_real {n : ℕ} (labels : Fin n↪J) (b : Bool) (j : J)
    (h : routeOwner (routePermutation labels) some b j∈routeSlots labels) :
    some j∈routeSlots labels := by
  cases b
  · exact h
  · exact (move_mem_iff _ _ (routePermutation_fixed labels) _).mp h

lemma reverse_routeOwner_mem_real {n : ℕ} (labels : Fin n↪J) (b : Bool) (j : J)
    (h : routeOwner (routePermutation labels).symm some b j∈routeSlots labels) :
    some j∈routeSlots labels := by
  cases b
  · exact h
  · exact (move_mem_iff _ _ (reverse_fix _ _ (routePermutation_fixed labels)) _).mp h

omit [DecidableEq J] in
theorem physicalCollisionReference_collision {N K M G m : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (h50 : 50 < L.val) (hm : 0 < m)
    (g : Fin G) (t r R C S h : ℝ) (u : Time)
    (ht : 0 < t) (hr : 0 < r) (hr1 : r≤1) (hR : 0≤R) (hC : 0≤C) (hh : 0 < h)
    (hu : (u:ℝ)=h/(2*t)) (hsmall : r*R≤1)
    (hτr : (2*t)/(m:ℝ)≤r^2) (hmscale : (m:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(m:ℝ))≤h) (hlarge : 8*(2*t)≤(m:ℝ)*h) (hdrift : 26/(m:ℝ)≤r)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L)
    (hy : ∀j,‖datumStart hL d (particle j)-anchorPoint (datumHome hL d (particle j))‖≤3)
    (hz : ∀j,‖datumEnd hL d (particle j)-anchorPoint (datumHome hL d (particle j))‖≤3)
    (hsep0 : ∀ i j, i ≠ j → r + 2*S < torusDistance L (projectPoint L (datumStart hL d (particle i)))
      (projectPoint L (datumStart hL d (particle j))))
    (hsep1 : ∀ i j, i ≠ j → r + 2*S < torusDistance L (projectPoint L (datumEnd hL d (particle i)))
      (projectPoint L (datumEnd hL d (particle j)))) :
    ∀ j k, j ≠ k → ∀ f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤datumCollisionBound t r h R C := by
  intro j k hjk f
  by_cases hj : datumAccessible hL g m t r R C S u (particle j) d
  · simp only [physicalCollisionReference,ite_eq_left hj]
    exact datum_reference_collision hL h50 hm g t r R C S h u ht hr hr1 hR hC hh hu hsmall
      hτr hmscale hwindow hlarge hdrift d (particle j) (particle k) hj (hy j) (hz j)
      (hsep0 j k hjk) (hsep1 j k hjk) f
  · simp only [physicalCollisionReference,ite_eq_right hj,Measure.coe_zero,Pi.zero_apply,zero_le]

omit [DecidableEq J] in
lemma physical_primary_domination {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J)
    (ha : datumAccessible hL g m t r R C S u (particle j) d) (v : Fin 3→Fin K) :
    (physicalSlotOn hL g m t r R C S u particle v d (some j)).map (fun f ↦ f)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j := by
  rw [Measure.map_id',physicalCollisionReference_eq hL g m t r R C S u particle d j ha v]
  intro A
  rw [Measure.smul_apply]
  exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_left (one_le_routeDensityBound t) _)

theorem physical_auxiliary_collision_bounds {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0 < t) (u : Time)
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
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (η (routeOwner σ.symm some b j))).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) A some (fun _ f ↦ f) b j)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) := by
  dsimp only
  obtain ⟨h₀,h₁⟩ := physical_auxiliary_path_bounds hL g m t r R C S ht u particle labels v steps hc d hhome haccess κ η he hr
  constructor
  · intro b j hj
    rw [physicalCollisionReference_eq hL g m t r R C S u particle d j
      (route_selected_accessible hL g m t r R C S u particle labels d haccess j
        (routeOwner_mem_real labels b j hj)) (v (Fin.last (n+1)))]
    exact h₀ b j hj
  · intro b j hj
    rw [physicalCollisionReference_eq hL g m t r R C S u particle d j
      (route_selected_accessible hL g m t r R C S u particle labels d haccess j
        (reverse_routeOwner_mem_real labels b j hj)) (v 0)]
    exact h₁ b j hj

end HardSphere.Groups
end
end

end OAI
