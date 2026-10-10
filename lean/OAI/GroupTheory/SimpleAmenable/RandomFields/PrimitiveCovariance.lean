import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveWords

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveCovariance

@[simp] theorem spatialTranslate_zero {a : ℕ} (U : polygonAlgebra a) :
    spatialTranslate 0 U = U := by
  apply Subtype.ext
  ext x
  simp [spatialTranslate]

theorem spatialTranslate_add {a : ℕ} (u v : CutRing × CutRing) (U : polygonAlgebra a) :
    spatialTranslate (u+v) U = spatialTranslate u (spatialTranslate v U) := by
  apply Subtype.ext
  ext x
  change translate a (-(u+v)) x ∈ U.val ↔ translate a (-v) (translate a (-u) x) ∈ U.val
  rw [← translate_add,neg_add,add_comm]

@[simp] theorem spatialTranslate_whole {a : ℕ} (u : CutRing × CutRing) :
    spatialTranslate u (wholePolygon a) = wholePolygon a := by
  apply Subtype.ext
  rfl

namespace CommonFrame

variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I : Finset (Fin (m+1))} {u v : CutRing × CutRing}

noncomputable def mul (F : CommonFrame a r m hm I u) (G : CommonFrame a r m hm I v) :
    CommonFrame a r m hm I (u+v) where
  k := F.k * G.k
  d := F.d + G.d
  projection := by rw [map_mul,F.projection,G.projection,trackTranslation_add]
  common i hi := by simp only [Pi.add_apply,F.common i hi,G.common i hi]

end CommonFrame

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveCopy_frame (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing))
    (F : CommonFrame a r m hm I p.2) :
    B.primitiveCopy I b hb p = B.translatedAlphabet I p.1 F.k :=
  B.commonTranslatedAlphabet_independent (commonFrame a r m hm I b hb p.2) F p.1 rfl

theorem primitiveCopy_translate_eq (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (j : Fin 5) (u v : CutRing × CutRing)
    (huv : spatialTranslate u (initialTest a r j) = spatialTranslate v (initialTest a r j)) :
    B.primitiveCopy I b hb (j,u) = B.primitiveCopy I b hb (j,v) :=
  B.commonTranslatedAlphabet_independent (commonFrame a r m hm I b hb u)
    (commonFrame a r m hm I b hb v) j huv

theorem translatedAlphabet_mul (I : Finset (Fin (m+1))) (j : Fin 5)
    (k l : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.translatedAlphabet I j (k*l) =
      (MulAut.conj (B.t k)).toMonoidHom.comp (B.translatedAlphabet I j l) := by
  ext s
  change B.t (k*l) * B.initialAlphabet I j s * (B.t (k*l))⁻¹ =
    B.t k * (B.t l * B.initialAlphabet I j s * (B.t l)⁻¹) * (B.t k)⁻¹
  rw [map_mul]
  group

theorem primitiveCopy_conjugate (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) (p : Fin 5 × (CutRing × CutRing)) :
    B.primitiveCopy I b hb (p.1,u+p.2) =
      (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.primitiveCopy I b hb p) := by
  rw [B.primitiveCopy_frame I b hb _ (F.mul (commonFrame a r m hm I b hb p.2))]
  exact B.translatedAlphabet_mul I p.1 F.k _

theorem primitiveCopy_zero (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (j : Fin 5) :
    B.primitiveCopy I b hb (j,0) = B.initialAlphabet I j := by
  let F : CommonFrame a r m hm I 0 := {
    k := 1
    d := 0
    projection := by simp
    common := by simp }
  rw [B.primitiveCopy_frame I b hb _ F]
  ext s
  change B.t 1 * B.initialAlphabet I j s * (B.t 1)⁻¹ = B.initialAlphabet I j s
  simp

theorem initialAlphabet_conjugate_common (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.initialAlphabet I 0) = B.initialAlphabet I 0 := by
  rw [← B.primitiveCopy_zero I b hb 0,← B.primitiveCopy_conjugate I b hb u F]
  have hz : spatialTranslate (u+0) (initialTest a r 0) =
      spatialTranslate 0 (initialTest a r 0) := by
    change spatialTranslate (u+0) (wholePolygon a) = spatialTranslate 0 (wholePolygon a)
    simp
  rw [B.primitiveCopy_translate_eq I b hb 0 (u+0) 0 hz]

end InitialCoverSystem
end PrimitiveCovariance

section FamilyCovariance

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

theorem copyFamilyEval_comp (F : ι → E →* H) (f : H →* Q) :
    copyFamilyEval (fun i => f.comp (F i)) = f.comp (copyFamilyEval F) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  simp

theorem copyFamilyEval_reindex_range {κ : Type*} (F : ι → E →* H) (v : κ → ι) :
    (copyFamilyEval (F ∘ v)).range ≤ (copyFamilyEval F).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i
  exact le_iSup (fun j => (F j).range) (v i)

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveFamily_conjugate (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (u : CutRing × CutRing) (F : CommonFrame a r m hm I u) :
    B.primitiveFamily I b hb (fun i => ((P i).1,u+(P i).2)) =
      fun i => (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.primitiveFamily I b hb P i) := by
  funext i
  cases i with
  | none => exact (B.initialAlphabet_conjugate_common I b hb u F).symm
  | some i => exact B.primitiveCopy_conjugate I b hb u F (P i)

theorem PrimitiveFamilyLaw.translate (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (u : CutRing × CutRing) :
    B.PrimitiveFamilyLaw I b hb (fun i => ((P i).1,u+(P i).2)) := by
  unfold PrimitiveFamilyLaw
  rw [B.primitiveFamily_conjugate I b hb P u (commonFrame a r m hm I b hb u),
    copyFamilyEval_comp,MonoidHom.range_comp]
  exact centralOn_conjugate _ _ _ h

theorem PrimitiveFamilyLaw.reindex {κ : Type*} (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (v : κ → ι) :
    B.PrimitiveFamilyLaw I b hb (P ∘ v) := by
  apply CentralOn.mono h
  have he : B.primitiveFamily I b hb (P ∘ v) =
      B.primitiveFamily I b hb P ∘ Option.map v := by
    funext i
    cases i <;> rfl
  rw [he]
  exact copyFamilyEval_reindex_range _ _

theorem PrimitiveFamilyLaw.congr_offsets (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : B.PrimitiveFamilyLaw I b hb P) : B.PrimitiveFamilyLaw I b hb Q := by
  have he : B.primitiveFamily I b hb P = B.primitiveFamily I b hb Q := by
    funext i
    cases i with
    | none => rfl
    | some i =>
      change B.primitiveCopy I b hb (P i) = B.primitiveCopy I b hb (Q i)
      have he : P i = ((Q i).1,(P i).2) := Prod.ext (hj i) rfl
      rw [he]
      exact B.primitiveCopy_translate_eq I b hb (Q i).1 (P i).2 (Q i).2
        (by simpa only [hj i] using hp i)
  unfold PrimitiveFamilyLaw at h ⊢
  rwa [← he]

end InitialCoverSystem
end FamilyCovariance

end SimpleAmenable
end
end

end OAI
