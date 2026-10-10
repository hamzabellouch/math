import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSector

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SectorOffsetCoherence

theorem spatialTranslate_reduce {a : ℕ} (u : CutRing × CutRing) (V : polygonAlgebra a) :
    spatialTranslate u V = spatialTranslate
      ((u.1.im:CutRing)*cutTau,(u.2.im:CutRing)*cutTau) V := by
  apply Subtype.ext
  ext p
  change (translation a u).symm p ∈ V.val ↔
    (translation a ((u.1.im:CutRing)*cutTau,(u.2.im:CutRing)*cutTau)).symm p ∈ V.val
  rw [translation_reduce a u]

theorem coordinatePrimitive_translate_label_eq {a : ℕ} (j : Fin 2)
    (u v : CutRing × CutRing)
    (h : endpointLabel (if j = 0 then u.1 else u.2) =
      endpointLabel (if j = 0 then v.1 else v.2)) :
    spatialTranslate u (coordinatePrimitive a j) = spatialTranslate v (coordinatePrimitive a j) := by
  rw [spatialTranslate_reduce u,spatialTranslate_reduce v]
  apply coordinatePrimitive_translate_eq j
  fin_cases j
  · change u.1.im = v.1.im at h
    change (u.1.im:CutRing)*cutTau = (v.1.im:CutRing)*cutTau
    exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) h
  · change u.2.im = v.2.im at h
    change (u.2.im:CutRing)*cutTau = (v.2.im:CutRing)*cutTau
    exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) h

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*}

theorem primitiveFamily_congr_offsets (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1)) :
    B.primitiveFamily I b hb P = B.primitiveFamily I b hb Q := by
  funext i
  cases i with
  | none => rfl
  | some i =>
    change B.primitiveCopy I b hb (P i) = B.primitiveCopy I b hb (Q i)
    have he : P i = ((Q i).1,(P i).2) := Prod.ext (hj i) rfl
    rw [he]
    exact B.primitiveCopy_translate_eq I b hb (Q i).1 (P i).2 (Q i).2
      (by simpa only [hj i] using hp i)

variable [Finite ι] [Finite κ]

theorem geometricSector_congr_offsets (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.geometricSector I b hb P h V = B.geometricSector I b hb Q g V := by
  have he := B.primitiveFamily_congr_offsets I b hb P Q hj hp
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    intro x y hxy
    apply hV x y
    intro i
    change x ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val ↔
      y ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val
    rw [hp i]
    exact hxy i
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb Q)).range g
  · rintro x ⟨s,rfl⟩
    rw [← he]
    exact B.geometricSector_mem I b hb P h V s
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb Q g V s
  · rw [B.geometricSector_projection I b hb P h V hV,
      B.geometricSector_projection I b hb Q g V hV']

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_congr_offsets (hlarge : 15 < m+1)
    (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.fullGeometricSector hlarge P h V = B.fullGeometricSector hlarge Q g V := by
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    intro x y hxy
    apply hV x y
    intro i
    change x ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val ↔
      y ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val
    rw [hp i]
    exact hxy i
  apply universal_five_alphabet_hom_ext (by simp; omega)
  intro I
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  rw [B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
      (h _ (by rw [I.property.2]; omega) b hb) V hV,
    B.fullGeometricSector_inclusion hlarge Q g I.val (by rw [I.property.2]) b hb
      (g _ (by rw [I.property.2]; omega) b hb) V hV']
  exact B.geometricSector_congr_offsets I.val b hb P Q hj hp _ _ V hV

end InitialCoverSystem
end SectorOffsetCoherence

end SimpleAmenable
end
end

end OAI
