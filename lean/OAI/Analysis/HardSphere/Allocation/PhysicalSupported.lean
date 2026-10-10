import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalPrimary

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSlotAllowed_borel {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    StandardBorelSpace (physicalSlotAllowed hL g m r R C S u particle d i) :=
  (physicalSlotAllowed_measurable hL g m r R C S u particle d i).standardBorel

lemma routeDensityBound_ne_top {t : ℝ} (ht : 0<t) : routeDensityBound t≠⊤ := by
  have ha : (ENNReal.ofReal (9/10:ℝ))≠0 := by positivity
  have hb : (ENNReal.ofReal (49/50:ℝ))≠0 := by positivity
  have hc := (midpointLower_pos ht 13).ne'
  simp only [routeDensityBound,ne_eq,max_eq_top]
  exact not_or.mpr ⟨by norm_num,ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb) (ENNReal.inv_ne_top.mpr hc))⟩

lemma one_le_routeDensityBound (t : ℝ) : 1≤routeDensityBound t :=
  le_trans (by norm_num) (le_max_left _ _)

def physicalSelectedOn {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) (i : routeSlots labels) :
    Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)) :=
  supportedPair (physicalSelectedFactor hL g m t r R C S u particle labels v steps i d)
    (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))

omit [Fintype J] [DecidableEq J] in
theorem physicalSelectedOn_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (i : routeSlots labels) :
    let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d i
    let P := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i
    let Q := physicalSlotOn hL g m t r R C S u particle (v 0) d ((routePermutation labels).symm i)
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst≤routeDensityBound t • P ∧ ρ.snd≤routeDensityBound t • Q ∧
      ρ.map (Prod.map Subtype.val Subtype.val)=
        physicalSelectedFactor hL g m t r R C S u particle labels v steps i d := by
  dsimp only
  obtain ⟨hp,hP,hQ,hfst,hsnd,-⟩ := physicalSelectedFactor_physical
    hL g m t r R C S ht u particle labels v steps hc d hhome haccess i
  let := hp
  let := hP
  let := hQ
  rw [←physicalSlotOn_map hL g m t r R C S u particle (v (Fin.last (n+1))) d i] at hfst
  rw [←physicalSlotOn_map hL g m t r R C S u particle (v 0) d ((routePermutation labels).symm i)] at hsnd
  have hS := physicalSlotAllowed_measurable hL g m r R C S u particle d i
  have hT := physicalSlotAllowed_measurable hL g m r R C S u particle d ((routePermutation labels).symm i)
  have hsupp := supported_of_marginals _ hS hT _ _ hfst hsnd
  exact ⟨supportedPair_probability _ hS hT hsupp,
    physicalSlotOn_probability hL g m t r R C S u particle _ d i,
    physicalSlotOn_probability hL g m t r R C S u particle _ d _,
    supportedPair_fst_le _ hS hT hsupp _ hfst,
    supportedPair_snd_le _ hS hT hsupp _ hsnd,
    supportedPair_map _ hS hT hsupp⟩

end HardSphere.Groups
end
end

end OAI
