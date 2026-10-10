import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.RepeatedTrackRouting
import OAI.GroupTheory.SimpleAmenable.Simplicial.SmallEvenRouting

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

noncomputable def orderedOffsets {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (u : Fin 5 → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  Function.extend ι u 0

@[simp] theorem orderedOffsets_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (u : Fin 5 → CutRing × CutRing) (j : Fin 5) : orderedOffsets ι u (ι j)=u j :=
  ι.injective.extend_apply u 0 j

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

structure SlotRouting (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) where
  alphabet : Finset (Fin (m+1))
  card_le : alphabet.card ≤ 25
  source_mem : ∀ j, i j ∈ alphabet
  target : Fin 5 ↪ Fin (m+1)
  target_mem : ∀ j, target j ∈ alphabet
  offsets : Fin (m+1) → CutRing × CutRing
  offsets_spec : ∀ j, offsets (target j)=u j
  frame : OffsetFrame a r m hm (orderedTrackAlphabet target) offsets
  word : BoundedRelationCover M (alternatingGenerator a r m hm)
  aligned : word ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  supported : word ∈ sourceAlignedGroup a r m hm M B.t alphabet
  transport : ∀ (j : Fin 5) (x : V.val),
    (coverMap M (alternatingGenerator a r m hm) word).val.val (i j,translate a (u j) x.val) =
      (target j,translate a (u j) x.val)

theorem slotRouting_nonempty (hwide : 26 ≤ m+1) (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    Nonempty (B.SlotRouting hlarge h hr V i u) := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \
      (∅ ∪ Finset.univ.image i)).card := by
    rw [Finset.empty_union,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hc := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at hc ⊢
    omega
  obtain ⟨P,_⟩ := exists_privateRoutingBank i ∅ hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin (m+1))).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  have ht (j : Fin 5) : P.target j ∈ P.alphabet :=
    P.row_subset j (orderedTrackAlphabet_mem (P.row j) 1)
  have hbt : b ∉ orderedTrackAlphabet P.target := by
    intro hh
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hh
    exact hb (ht j)
  obtain ⟨w,hw,hwJ,hwt⟩ := B.repeated_bank_routing hlarge h hr i u P b hb V hinj
  exact ⟨{
    alphabet := P.alphabet
    card_le := P.alphabet_card
    source_mem := P.source_mem
    target := P.target
    target_mem := ht
    offsets := orderedOffsets P.target u
    offsets_spec := orderedOffsets_apply P.target u
    frame := balancedOffsetFrame a r m hm _ b hbt (orderedOffsets P.target u)
    word := w
    aligned := hw
    supported := hwJ
    transport := hwt }⟩

namespace SlotRouting
variable {B hlarge h hr}

noncomputable def star {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u) :
    UniversalExtension (alternatingGroup (Fin 5)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj ρ.word⁻¹).toMonoidHom.comp
    (B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V)

theorem aligned_transport
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    {V : polygonAlgebra a} {i k : Fin 5 → Fin (m+1)} {u : Fin 5 → CutRing × CutRing}
    (ρ : B.SlotRouting hlarge h hr V i u) (σ : B.SlotRouting hlarge h hr V k u)
    (J : Finset (Fin (m+1))) (hwide : J.card+88 ≤ m+1)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val) =
        (k j,translate a (u j) x.val)) :
    (MulAut.conj z).toMonoidHom.comp ρ.star = σ.star := by
  classical
  let S := ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range
  let K := σ.alphabet ∪ J ∪ ρ.alphabet
  let L := sourceAlignedGroup a r m hm M B.t K
  let w := σ.word*z*ρ.word⁻¹
  have hwS : w ∈ S := S.mul_mem (S.mul_mem σ.aligned hz) (S.inv_mem ρ.aligned)
  have hσL : σ.word ∈ L := sourceAlignedGroup_mono B.t
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) σ.supported
  have hρL : ρ.word ∈ L := sourceAlignedGroup_mono B.t Finset.subset_union_right ρ.supported
  have hzL : z ∈ L := sourceAlignedGroup_mono B.t
    (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left) hzJ
  have hwL : w ∈ L := L.mul_mem (L.mul_mem hσL hzL) (L.inv_mem hρL)
  have hK : K.card+38 ≤ m+1 := by
    have h₁ := Finset.card_union_le σ.alphabet J
    have h₂ := Finset.card_union_le (σ.alphabet∪J) ρ.alphabet
    have hρ := ρ.card_le
    have hσ := σ.card_le
    dsimp [K]
    omega
  have hwt : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) w).val.val
        (ρ.target j,translate a (ρ.offsets (ρ.target j)) x.val) =
        (σ.target j,translate a (σ.offsets (σ.target j)) x.val) := by
    intro j x
    rw [ρ.offsets_spec j,σ.offsets_spec j]
    change (coverMap M (alternatingGenerator a r m hm) (σ.word*z*ρ.word⁻¹)).val.val _ = _
    rw [map_mul,map_mul,map_inv]
    change (coverMap M (alternatingGenerator a r m hm) σ.word).val.val
      ((coverMap M (alternatingGenerator a r m hm) z).val.val
        ((coverMap M (alternatingGenerator a r m hm) ρ.word).val.val.symm _)) = _
    rw [← ρ.transport j x,Equiv.symm_apply_apply,htransport j x,σ.transport j x]
  have he := B.distinctSlotStar_aligned_transport hlarge h hr R hR ρ.target σ.target
    ρ.offsets σ.offsets (fun j => (ρ.offsets_spec j).trans (σ.offsets_spec j).symm)
    ρ.frame σ.frame V K hK w hwS hwL hwt
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change w*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*w⁻¹ =
    B.distinctSlotStar hlarge h hr σ.target σ.offsets σ.frame V s at hh
  change z*(ρ.word⁻¹*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(ρ.word⁻¹)⁻¹)*z⁻¹ =
    σ.word⁻¹*B.distinctSlotStar hlarge h hr σ.target σ.offsets σ.frame V s*(σ.word⁻¹)⁻¹
  simp only [inv_inv]
  rw [← hh]
  dsimp [w]
  group

theorem independent
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 88 ≤ m+1) {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing}
    (ρ σ : B.SlotRouting hlarge h hr V i u) : ρ.star=σ.star := by
  have he := ρ.aligned_transport R hR σ ∅ (by simpa using hwide) 1
    (Subgroup.one_mem _) (Subgroup.one_mem _) (by intro j x; simp)
  ext s : 1
  have hh := DFunLike.congr_fun he s
  change 1*ρ.star s*1⁻¹=σ.star s at hh
  simpa using hh

end SlotRouting
end InitialCoverSystem

end SimpleAmenable

end OAI
