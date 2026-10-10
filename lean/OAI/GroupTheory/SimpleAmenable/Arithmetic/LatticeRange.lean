import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConditionalBooleanGeneration
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PerfectGeneratingFamilies

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceLatticeRange

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def sourceLatticeFullMap :
    Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      polygonFullGroup a (m+1) :=
  (polygonAlternatingGroup a (m+1)).subtype.comp (sourceLatticeMap a r m hm)

@[simp] theorem sourceLatticeFullMap_of (i : Fin m × Fin 2) :
    sourceLatticeFullMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
      sourceGenerator a r m (Sum.inr i) := by
  change (sourceLatticeMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i))).val = _
  rw [sourceLatticeMap,commutingFamilyHom_of]
  rfl

theorem sourceLatticeFullMap_balanced (i : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single i v - Pi.single (Fin.last m) v) ∈
      (sourceLatticeFullMap a r m hm).range := by
  classical
  let K := (sourceLatticeFullMap a r m hm).range
  change _ ∈ K
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  let dx : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (cutTau,0) - Pi.single (Fin.last m) (cutTau,0)
  let dy : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (0,cutTau) - Pi.single (Fin.last m) (0,cutTau)
  have hx : trackTranslation (a := a) dx ∈ K :=
    ⟨_,sourceLatticeFullMap_of a r m hm (i,0)⟩
  have hy : trackTranslation (a := a) dy ∈ K := by
    refine ⟨Multiplicative.ofAdd (FreeAbelianGroup.of (i,1)),?_⟩
    simpa only [sourceGenerator,show (1 : Fin 2) ≠ 0 by decide,ite_false]
      using sourceLatticeFullMap_of a r m hm (i,1)
  have he : trackTranslation (a := a) (Pi.single i.castSucc v - Pi.single (Fin.last m) v) =
      trackTranslation (v.1.im • dx + v.2.im • dy) := by
    let d : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc v - Pi.single (Fin.last m) v
    change trackTranslation d = _
    rw [trackTranslation_reduce d]
    congr 1
    funext k
    by_cases hki : k = i.castSucc <;> by_cases hkl : k = Fin.last m <;>
      apply Prod.ext <;> simp [d,dx,dy,hki,hkl,zsmul_eq_mul]
  rw [he,trackTranslation_add,trackTranslation_zsmul,trackTranslation_zsmul]
  exact K.mul_mem (K.zpow_mem hx _) (K.zpow_mem hy _)

theorem sourceLatticeFullMap_difference (i j : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈
      (sourceLatticeFullMap a r m hm).range := by
  have he : (Pi.single j v - Pi.single i v : Fin (m+1) → CutRing × CutRing) =
      (Pi.single j v - Pi.single (Fin.last m) v) -
        (Pi.single i v - Pi.single (Fin.last m) v) := by abel
  rw [he,trackTranslation_sub]
  exact (sourceLatticeFullMap a r m hm).range.mul_mem
    (sourceLatticeFullMap_balanced a r m hm j v)
    ((sourceLatticeFullMap a r m hm).range.inv_mem
      (sourceLatticeFullMap_balanced a r m hm i v))

theorem sourceLatticeFullMap_prescribed (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : Fin (m+1) → CutRing × CutRing) :
    ∃ k d, sourceLatticeFullMap a r m hm k = trackTranslation d ∧
      ∀ i ∈ I, d i = u i := by
  classical
  let d : Fin (m+1) → CutRing × CutRing :=
    ∑ i ∈ I, (Pi.single i (u i) - Pi.single b (u i))
  have hd : trackTranslation (a := a) d ∈ (sourceLatticeFullMap a r m hm).range := by
    dsimp only [d]
    clear hb
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,trackTranslation_add]
      exact (sourceLatticeFullMap a r m hm).range.mul_mem
        (sourceLatticeFullMap_difference a r m hm b i (u i)) ih
  obtain ⟨k,hk⟩ := hd
  refine ⟨k,d,hk,?_⟩
  intro i hi
  have hib : i ≠ b := fun h => hb (h ▸ hi)
  simp [d,Finset.sum_apply,Pi.sub_apply,Pi.single_apply,hib,hi]

theorem sourceLatticeFullMap_translation (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    ∃ d, sourceLatticeFullMap a r m hm k = trackTranslation d := by
  change ∃ d, sourceLatticeFullMap a r m hm
    (Multiplicative.ofAdd (Multiplicative.toAdd k)) = trackTranslation d
  induction Multiplicative.toAdd k using FreeAbelianGroup.induction_on with
  | zero => refine ⟨0,?_⟩; exact (map_one _).trans trackTranslation_zero.symm
  | of i => exact ⟨_,sourceLatticeFullMap_of a r m hm i⟩
  | neg i hi =>
      obtain ⟨d,hd⟩ := hi
      refine ⟨-d,?_⟩
      change sourceLatticeFullMap a r m hm
        ((Multiplicative.ofAdd (FreeAbelianGroup.of i))⁻¹) = _
      rw [map_inv,hd,trackTranslation_neg]
  | add x y hx hy =>
      obtain ⟨d,hd⟩ := hx
      obtain ⟨e,he⟩ := hy
      refine ⟨d+e,?_⟩
      change sourceLatticeFullMap a r m hm
        (Multiplicative.ofAdd x * Multiplicative.ofAdd y) = _
      rw [map_mul,hd,he,trackTranslation_add]

end SourceLatticeRange

end SimpleAmenable
end
end

end OAI
