import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TranslationRoutingHelpers
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ShiftedRouting
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CanonicalSlotStars

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TranslationTransport

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

noncomputable def balancedShift (b : Fin m) (d : Fin m → CutRing × CutRing) :
    Fin m → CutRing × CutRing := finiteBalancedVector P.alphabet b (P.blockOffsets d)

theorem balancedShift_row (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j l : Fin 5) :
    P.balancedShift b d (P.row j l)=d (i j) := by
  rw [balancedShift,finiteBalancedVector_apply P.alphabet b hb _ _
    (P.row_subset j (orderedTrackAlphabet_mem _ l)),P.blockOffsets_apply]

theorem balancedShift_source (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j : Fin 5) :
    P.balancedShift b d (i j)=d (i j) :=
  (congrArg (P.balancedShift b d) (P.source j)).symm.trans (P.balancedShift_row b hb d j 0)

theorem balancedShift_block (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j l : Fin 5) :
    P.balancedShift b d (P.row j l)=P.balancedShift b d (i j) :=
  (P.balancedShift_row b hb d j l).trans (P.balancedShift_source b hb d j).symm

theorem difference_support (b : Fin m) (d : Fin m → CutRing × CutRing)
    (J : Finset (Fin m)) (hsupp : ∀ t, t∉J → d t=0)
    (t : Fin m) (ht : t∉J ∪ insert b P.alphabet) : (d-P.balancedShift b d) t=0 := by
  have htJ : t∉J := fun hh => ht (Finset.mem_union_left _ hh)
  have htP : t∉insert b P.alphabet := fun hh => ht (Finset.mem_union_right _ hh)
  rw [Pi.sub_apply]
  exact sub_eq_zero.mpr ((hsupp t htJ).trans
    (finiteBalancedVector_supported P.alphabet b (P.blockOffsets d) t htP).symm)

theorem difference_source (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j : Fin 5) :
    (d - P.balancedShift b d) (i j)=0 := by
  rw [Pi.sub_apply,P.balancedShift_source b hb d j,sub_self]

theorem difference_alphabet_card (b : Fin m) (J : Finset (Fin m)) (hJ : J.card≤2) :
    (J ∪ insert b P.alphabet).card≤28 := by
  have hc := P.alphabet_card
  have h₁ := Finset.card_union_le J (insert b P.alphabet)
  have h₂ := Finset.card_insert_le b P.alphabet
  omega

end PrivateRoutingBank

theorem exists_privateRoutingBank_with_balance {m : ℕ} (i : Fin 5 → Fin m)
    (hwide : 26 ≤ m) : ∃ P : PrivateRoutingBank i, ∃ b : Fin m, b ∉ P.alphabet := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin m)) \
      (∅ ∪ Finset.univ.image i)).card := by
    rw [Finset.empty_union,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hc := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at hc ⊢
    omega
  obtain ⟨P,_⟩ := exists_privateRoutingBank i ∅ hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin m)).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  exact ⟨P,b,hb⟩

theorem translation_conjugate_eq {A H : Type*} [CommGroup A] [Group H]
    (t : A →* H) (k l : A) (x : H) (hc : Commute (t (k*l⁻¹)) x) :
    t k*x*(t k)⁻¹=t l*x*(t l)⁻¹ := by
  let δ := k*l⁻¹
  have hkk : k=l*δ := by dsimp [δ]; simp only [mul_comm k l⁻¹,← mul_assoc,mul_inv_cancel,one_mul]
  have hcc : t δ*x*(t δ)⁻¹=x := by rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  calc
    t k*x*(t k)⁻¹ = t l*(t δ*x*(t δ)⁻¹)*(t l)⁻¹ := by rw [hkk,map_mul]; group
    _ = t l*x*(t l)⁻¹ := by rw [hcc]

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

theorem slotStar_translation_bank (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ j l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by
  let ρ := SlotRouting.privateBank (B := B) (hlarge := hlarge) (h := h) (hr := hr)
    V i u P b hb hinj
  have htarget (j : Fin 5) : d (ρ.target j)=d (i j) := hblock j 1
  have hmem := B.privateRoutingWord_shift_mem hlarge h hr i u P b hb V k d hd hblock
  let σ := ρ.shift k d hd htarget hmem.1 hmem.2
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide V i _ _ σ]
  exact (ρ.shift_star k d hd htarget hmem.1 hmem.2).symm

theorem slotStar_translation_difference_commute (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (k k' : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hk' : sourceLatticeFullMap a r m hm k'=trackTranslation (P.balancedShift b d))
    (J : Finset (Fin (m+1))) (hJ : J.card≤2) (hsupp : ∀ t, t∉J → d t=0)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t (k*k'⁻¹)) (B.slotStar hlarge h hr hwide V i u hinj s) := by
  have hδ : sourceLatticeFullMap a r m hm (k*k'⁻¹)=
      trackTranslation (d-P.balancedShift b d) := by
    rw [map_mul,map_inv,hd,hk',trackTranslation_sub]
  exact B.slotStar_zero_commute hlarge h hr R hR hwide V i u hinj (k*k'⁻¹)
    (d-P.balancedShift b d) hδ (J ∪ insert b P.alphabet)
    (P.difference_alphabet_card b J hJ) (P.difference_support b d J hsupp)
    (P.difference_source b hb d) s

theorem slotStar_translation_two_support (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (J : Finset (Fin (m+1))) (hJ : J.card≤2)
    (hsupp : ∀ t, t∉J → d t=0) :
    (MulAut.conj (B.t k)).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by
  obtain ⟨P,b,hb⟩ := exists_privateRoutingBank_with_balance i (by omega)
  let v := P.balancedShift b d
  obtain ⟨k',hk'⟩ := finiteBalancedVector_range a r m hm P.alphabet b (P.blockOffsets d)
  have hv : sourceLatticeFullMap a r m hm k'=trackTranslation v := hk'
  have he := B.slotStar_translation_bank hlarge h hr R hR hwide V i u hinj P b hb k' v hv
    (P.balancedShift_block b hb d)
  have hoff : (fun j => v (i j)+u j)=(fun j => d (i j)+u j) :=
    funext (fun j => congrArg (fun z => z+u j) (P.balancedShift_source b hb d j))
  have he' : (MulAut.conj (B.t k')).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by simpa only [hoff] using he
  rw [← he']
  ext s : 1
  apply translation_conjugate_eq B.t k k'
  exact B.slotStar_translation_difference_commute hlarge h hr R hR hwide V i u hinj
    P b hb k k' d hd hk' J hJ hsupp s

end InitialCoverSystem
end TranslationTransport

end SimpleAmenable
end
end

end OAI
