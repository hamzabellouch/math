import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.RepeatedTrackRouting
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FrameCompatibility

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TranslationRoutingHelpers

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

noncomputable def blockOffsets (d : Fin m → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  Function.extend (fun p : Fin 5 × Fin 5 => P.row p.1 p.2) (fun p => d (i p.1)) 0

@[simp] theorem blockOffsets_apply (d : Fin m → CutRing × CutRing) (j k : Fin 5) :
    P.blockOffsets d (P.row j k)=d (i j) := by
  have hf : Function.FactorsThrough (fun p : Fin 5 × Fin 5 => d (i p.1))
      (fun p : Fin 5 × Fin 5 => P.row p.1 p.2) := by
    intro p q he
    obtain ⟨j,k⟩ := p
    obtain ⟨l,t⟩ := q
    change P.row j k=P.row l t at he
    change d (i j)=d (i l)
    by_cases hk : k=0 <;> by_cases ht : t=0
    · subst k; subst t
      rw [P.source j,P.source l] at he
      exact congrArg d he
    · subst k
      rw [P.source j] at he
      exact (P.fresh l t ht j he.symm).elim
    · subst t
      rw [P.source l] at he
      exact (P.fresh j k hk l he).elim
    · exact congrArg (fun q => d (i q)) (P.separate j k l t hk ht he).1
  exact hf.extend_apply 0 (j,k)

end PrivateRoutingBank

noncomputable def finiteBalancedVector {m : ℕ} (I : Finset (Fin m)) (b : Fin m)
    (u : Fin m → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  ∑ i ∈ I, (Pi.single i (u i) - Pi.single b (u i))

theorem finiteBalancedVector_apply {m : ℕ} (I : Finset (Fin m)) (b : Fin m) (hb : b ∉ I)
    (u : Fin m → CutRing × CutRing) (i : Fin m) (hi : i ∈ I) :
    finiteBalancedVector I b u i=u i := by
  classical
  have hib : i≠b := fun he => hb (he ▸ hi)
  simp [finiteBalancedVector,Finset.sum_apply,Pi.sub_apply,Pi.single_apply,hib,hi]

theorem finiteBalancedVector_supported {m : ℕ} (I : Finset (Fin m)) (b : Fin m)
    (u : Fin m → CutRing × CutRing) (i : Fin m) (hi : i ∉ insert b I) :
    finiteBalancedVector I b u i=0 := by
  classical
  have hib : i≠b := fun he => hi (he ▸ Finset.mem_insert_self b I)
  have hiI : i∉I := fun hh => hi (Finset.mem_insert_of_mem hh)
  simp only [finiteBalancedVector,Finset.sum_apply,Pi.sub_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i≠j := fun he => hiI (he ▸ hj)
  simp [hib,hij]

theorem finiteBalancedVector_range (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (u : Fin (m+1) → CutRing × CutRing) :
    trackTranslation (a := a) (finiteBalancedVector I b u) ∈
      (sourceLatticeFullMap a r m hm).range := by
  classical
  unfold finiteBalancedVector
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,trackTranslation_add]
    exact (sourceLatticeFullMap a r m hm).range.mul_mem
      (sourceLatticeFullMap_difference a r m hm b i (u i)) ih

theorem SlotMap_shift_injective {a m : ℕ} (V : polygonAlgebra a)
    (i : Fin 5 → Fin m) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a m V (fun j => (i j,u j))))
    (d : Fin m → CutRing × CutRing) :
    Function.Injective (SlotMap a m V (fun j => (i j,d (i j)+u j))) := by
  have he (p : Fin 5 × V.val) : (trackTranslation d).val (SlotMap a m V (fun j => (i j,u j)) p) =
      SlotMap a m V (fun j => (i j,d (i j)+u j)) p := by
    simp [SlotMap,translate_add]
  intro p q hpq
  apply hinj
  apply (trackTranslation d).val.injective
  rwa [he,he]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_zero_commute (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hz : ∀ j, d (ι j)=0) (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t k) (B.distinctSlotStar hlarge h hr ι u F V s) := by
  let G : CommonFrame a r m hm (orderedTrackAlphabet ι) 0 := {
    k := k
    d := d
    projection := hd
    common := by
      intro t ht
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
      exact hz j }
  have h₁ := B.polygonStar_frame_zero_commute hlarge h hr (orderedTrackAlphabet ι)
    (by simp [orderedTrackAlphabet]) b hb G V (universalMap (orderedTrackHom ι) s)
  have h₂ : Commute (B.t k) (B.t F.k) := (Commute.all k F.k).map B.t
  exact (h₂.mul_right h₁).mul_right h₂.inv_right

theorem privateRoutingFactor_shift_mem (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) ∈
        ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) ∈
      sourceAlignedGroup a r m hm M B.t P.alphabet := by
  have hbj : b ∉ orderedTrackAlphabet (P.row j) := fun ht => hb (P.row_subset j ht)
  let F := balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j)) b hbj (fun _ => u j)
  have he := DFunLike.congr_fun (B.frameStar_shift hlarge h hr (orderedTrackAlphabet (P.row j))
    (fun _ => u j) F k d hd V) (universalMap (orderedTrackHom (P.row j)) privateCycleStar)
  change B.distinctSlotStar hlarge h hr (P.row j) (d+(fun _ => u j)) (F.shift k d hd) V privateCycleStar =
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) at he
  rw [← he]
  constructor
  · exact B.distinctSlotStar_uniform_mem hlarge h hr (P.row j) b hbj _ (F.shift k d hd)
      (d (i j)+u j) (fun l => by simp only [Pi.add_apply,hblock l]) V privateCycleStar
  · exact sourceAlignedGroup_mono B.t (P.row_subset j)
      (B.frameStar_alphabet_mem hlarge h hr _ (by simp [orderedTrackAlphabet]) b hbj _
        (F.shift k d hd) V (universalMap (orderedTrackHom (P.row j)) privateCycleStar))

theorem privateRoutingWord_shift_mem (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ j l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) ∈
        ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
    (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) ∈
      sourceAlignedGroup a r m hm M B.t P.alphabet := by
  have he : (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) =
      ((List.finRange 5).map (fun j =>
        (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j))).prod := by
    exact (MulAut.conj (B.t k)).toMonoidHom.map_list_prod _ |>.trans (by rw [List.map_map]; rfl)
  rw [he]
  constructor
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact (B.privateRoutingFactor_shift_mem hlarge h hr i u P b hb V j k d hd (hblock j)).1
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact (B.privateRoutingFactor_shift_mem hlarge h hr i u P b hb V j k d hd (hblock j)).2

end InitialCoverSystem
end TranslationRoutingHelpers

end SimpleAmenable
end
end

end OAI
