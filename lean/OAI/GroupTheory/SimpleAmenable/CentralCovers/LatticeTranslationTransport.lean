import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationRoutingHelpers
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationTransport

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LatticeTranslationTransport

noncomputable def sourceGeneratorOffsets (m : ℕ) (j : Fin m × Fin 2) :
    Fin (m+1) → CutRing × CutRing :=
  Pi.single j.1.castSucc (if j.2=0 then (cutTau,0) else (0,cutTau)) -
    Pi.single (Fin.last m) (if j.2=0 then (cutTau,0) else (0,cutTau))

noncomputable def sourceLatticeOffsets (m : ℕ) :
    FreeAbelianGroup (Fin m × Fin 2) →+ (Fin (m+1) → CutRing × CutRing) :=
  FreeAbelianGroup.lift (sourceGeneratorOffsets m)

@[simp] theorem sourceLatticeOffsets_of (m : ℕ) (j : Fin m × Fin 2) :
    sourceLatticeOffsets m (FreeAbelianGroup.of j)=sourceGeneratorOffsets m j :=
  FreeAbelianGroup.lift_apply_of _ _

theorem sourceGeneratorOffsets_support (m : ℕ) (j : Fin m × Fin 2)
    (t : Fin (m+1)) (ht : t ∉ ({j.1.castSucc,Fin.last m} : Finset (Fin (m+1)))) :
    sourceGeneratorOffsets m j t=0 := by
  classical
  have hi : t≠j.1.castSucc := fun he => ht (he ▸ Finset.mem_insert_self _ _)
  have hl : t≠Fin.last m := fun he => ht (he ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  simp [sourceGeneratorOffsets,Pi.sub_apply,hi,hl]

theorem sourceLatticeFullMap_offsets (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (k : FreeAbelianGroup (Fin m × Fin 2)) :
    sourceLatticeFullMap a r m hm (Multiplicative.ofAdd k)=
      trackTranslation (sourceLatticeOffsets m k) := by
  induction k using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero,ofAdd_zero,map_one,trackTranslation_zero]
  | of j =>
    rw [sourceLatticeOffsets_of]
    exact sourceLatticeFullMap_of a r m hm j
  | neg j ih =>
    change sourceLatticeFullMap a r m hm ((Multiplicative.ofAdd (FreeAbelianGroup.of j))⁻¹)=_
    rw [map_inv,ih,map_neg,trackTranslation_neg]
  | add k l ihk ihl =>
    change sourceLatticeFullMap a r m hm (Multiplicative.ofAdd k*Multiplicative.ofAdd l)=_
    rw [map_mul,ihk,ihl,map_add,trackTranslation_add]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_translation_lattice (k : FreeAbelianGroup (Fin m × Fin 2))
    (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    (MulAut.conj (B.t (Multiplicative.ofAdd k))).toMonoidHom.comp
      (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => sourceLatticeOffsets m k (i j)+u j)
        (SlotMap_shift_injective V i u hinj (sourceLatticeOffsets m k)) := by
  induction k using FreeAbelianGroup.induction_on generalizing u with
  | zero =>
    simp only [ofAdd_zero,map_one,map_zero,Pi.zero_apply,zero_add]
    ext s : 1
    rfl
  | of j =>
    simpa only [sourceLatticeOffsets_of] using B.slotStar_translation_two_support hlarge h hr R hR hwide V i u hinj
      (Multiplicative.ofAdd (FreeAbelianGroup.of j)) (sourceGeneratorOffsets m j)
      (sourceLatticeFullMap_of a r m hm j) {j.1.castSucc,Fin.last m}
      (by exact le_trans (Finset.card_insert_le _ _) (by simp)) (sourceGeneratorOffsets_support m j)
  | neg j _ =>
    have hd := sourceLatticeFullMap_offsets a r m hm (-FreeAbelianGroup.of j)
    exact B.slotStar_translation_two_support hlarge h hr R hR hwide V i u hinj
      (Multiplicative.ofAdd (-FreeAbelianGroup.of j)) _ hd {j.1.castSucc,Fin.last m}
      (by exact le_trans (Finset.card_insert_le _ _) (by simp)) (by
        intro t ht
        rw [map_neg,sourceLatticeOffsets_of,Pi.neg_apply,sourceGeneratorOffsets_support m j t ht,neg_zero])
  | add k l ihk ihl =>
    have hl := DFunLike.congr_fun (ihl u hinj)
    have hk := DFunLike.congr_fun (ihk (fun j => sourceLatticeOffsets m l (i j)+u j)
      (SlotMap_shift_injective V i u hinj (sourceLatticeOffsets m l)))
    have hoff : (fun j => sourceLatticeOffsets m k (i j)+(sourceLatticeOffsets m l (i j)+u j)) =
        (fun j => sourceLatticeOffsets m (k+l) (i j)+u j) := by
      funext j
      rw [map_add,Pi.add_apply,add_assoc]
    ext s : 1
    change B.t (Multiplicative.ofAdd k*Multiplicative.ofAdd l)*
      B.slotStar hlarge h hr hwide V i u hinj s*
        (B.t (Multiplicative.ofAdd k*Multiplicative.ofAdd l))⁻¹ = _
    rw [map_mul]
    calc
      _ = B.t (Multiplicative.ofAdd k)*
          (B.t (Multiplicative.ofAdd l)* B.slotStar hlarge h hr hwide V i u hinj s*
            (B.t (Multiplicative.ofAdd l))⁻¹)*(B.t (Multiplicative.ofAdd k))⁻¹ := by group
      _ = _ := by
        rw [show B.t (Multiplicative.ofAdd l)*B.slotStar hlarge h hr hwide V i u hinj s*
          (B.t (Multiplicative.ofAdd l))⁻¹ = _ from hl s]
        exact (hk s).trans (by simp only [hoff])

end InitialCoverSystem
end LatticeTranslationTransport

end SimpleAmenable
end
end

end OAI
