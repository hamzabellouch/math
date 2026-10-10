import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalLifted

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
lemma fiberNormalize_mass_le_one (κ : Kernel E X) [IsSFiniteKernel κ]
    (A : Set (E×X)) (e : E) : fiberNormalize κ A e univ≤1 := by
  change ((fiberRestrict κ A e univ)⁻¹ • fiberRestrict κ A e) univ≤1
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

variable {I : Type*} [Fintype I] [DecidableEq I]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
omit [Fintype I] in
lemma ambientSharedKernel_mass_le (s : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉s→σ i=i) (ξ : Kernel E (∀i,V i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (V i×V (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,V i))) (e : E) :
    ambientSharedKernel s σ hσ ξ ρ A e univ≤ξ e univ := by
  rw [ambientSharedKernel,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  calc
    _ ≤ ∫⁻_x,1 ∂ξ e := lintegral_mono fun _ ↦ fiberNormalize_mass_le_one _ _ _
    _ = _ := by simp
end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalPairedRoute {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    Kernel (PhysicalDatum N K M G L) ((Option J→C(Time,Point))×(Option J→C(Time,Point))) :=
  (physicalSharedRoute hL g m t r R C S u particle labels v steps).map
    (fun z ↦ (ambientFirst (routeSlots labels) (routePermutation labels) z,
      ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels) z))

instance physicalPairedRoute_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) : IsFiniteKernel (physicalPairedRoute (M:=M) hL g m t r R C S u particle labels v steps) := by
  unfold physicalPairedRoute; infer_instance

lemma physicalPairedRoute_total {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    physicalPairedRoute hL g m t r R C S u particle labels v steps d univ=
      physicalSharedRoute hL g m t r R C S u particle labels v steps d univ := by
  rw [physicalPairedRoute,Kernel.map_apply _ ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _)),
    Measure.map_apply ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _)) MeasurableSet.univ]
  rfl

lemma physicalPairedRoute_mass_le_one {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    physicalPairedRoute hL g m t r R C S u particle labels v steps d univ≤1 := by
  rw [physicalPairedRoute_total]
  exact (ambientSharedKernel_mass_le _ _ _ _ _ _ _).trans (fiberNormalize_mass_le_one _ _ _)

lemma physicalPairedRoute_mass_from_allowed {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    physicalPairedRoute hL g m t r R C S u particle labels v steps d univ=
      physicalSharedOn hL g m t r R C S u particle labels v steps d univ := by
  rw [physicalPairedRoute_total,←physicalSharedOn_map hL g m t r R C S ht hr u particle labels v steps hc d hhome haccess]
  rw [Measure.map_apply (routePairedMap_measurable _ (fun _ ↦ measurable_subtype_coe) _ _) MeasurableSet.univ]
  rfl

end HardSphere.Groups
end
end

end OAI
