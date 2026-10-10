import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.DistinctSlotStars
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CommonFrameTransport

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrivateBankWord

theorem perm_list_prod_fix {α X : Type*} (l : List α) (f : α → Equiv.Perm X) (x : X)
    (h : ∀ i ∈ l, f i x=x) : (l.map f).prod x=x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)),h i List.mem_cons_self]

theorem perm_list_prod_transport {α X : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (f : α → Equiv.Perm X) (j : α) (hj : j ∈ l)
    (x y : X) (he : f j x=y)
    (hs : ∀ i ∈ l, i≠j → f i x=x ∧ f i y=y) : (l.map f).prod x=y := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    have hn := (List.nodup_cons.mp hl).1
    have ht := (List.nodup_cons.mp hl).2
    by_cases hij : i=j
    · subst i
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [perm_list_prod_fix l f x (fun i hi => (hs i (List.mem_cons_of_mem _ hi)
        (fun he => hn (he ▸ hi))).1),he]
    · have hj' : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [ih ht hj' (fun k hk => hs k (List.mem_cons_of_mem _ hk)),
        (hs i List.mem_cons_self hij).2]

def bankRow {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) : Fin 5 ↪ Fin m :=
  ⟨fun i => e (j,i),fun _ _ he => congrArg Prod.snd (e.injective he)⟩

def bankColumn {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) : Fin 5 ↪ Fin m :=
  ⟨fun i => e (i,j),fun _ _ he => congrArg Prod.fst (e.injective he)⟩

noncomputable def bankAlphabet {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) : Finset (Fin m) :=
  Finset.univ.map e

theorem bankRow_subset {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) :
    orderedTrackAlphabet (bankRow e j) ⊆ bankAlphabet e := by
  intro i hi
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_map.mpr ⟨(j,k),Finset.mem_univ _,rfl⟩

theorem bankColumn_subset {m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m) (j : Fin 5) :
    orderedTrackAlphabet (bankColumn e j) ⊆ bankAlphabet e := by
  intro i hi
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_map.mpr ⟨(k,j),Finset.mem_univ _,rfl⟩

def privateCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2,by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul]
    norm_num⟩

@[simp] theorem privateCycle_apply_zero : privateCycle.val 0=1 := by
  decide

noncomputable def privateCycleStar : UniversalExtension (alternatingGroup (Fin 5)) :=
  (universalProjection_surjective _ privateCycle).choose

@[simp] theorem privateCycleStar_projection : universalProjection _ privateCycleStar=privateCycle :=
  (universalProjection_surjective _ privateCycle).choose_spec

theorem bank_other_frame_notmem {a m : ℕ} (e : (Fin 5 × Fin 5) ↪ Fin m)
    (u : Fin m → CutRing × CutRing) (V : polygonAlgebra a) (i j k : Fin 5) (hij : i≠j)
    (x : GenericSquare a) : (e (j,k),x) ∉ frameDomain (orderedTrackAlphabet (bankRow e i)) u V := by
  rintro ⟨t,ht,y,hy,he⟩
  obtain ⟨l,_,rfl⟩ := Finset.mem_map.mp ht
  have hh := e.injective (congrArg Prod.fst he)
  exact hij (congrArg Prod.fst hh).symm

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem private_bank_evacuation (e : (Fin 5 × Fin 5) ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ bankAlphabet e)
    (u : Fin (m+1) → CutRing × CutRing) (v : Fin 5 → CutRing × CutRing)
    (hu : ∀ i j, u (e (i,j))=v i) (F : OffsetFrame a r m hm (bankAlphabet e) u)
    (V : polygonAlgebra a) (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hfix : ∀ (i j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,j),translate a (u (e (i,j))) x.val) =
        (e (i,j),translate a (u (e (i,j))) x.val)) :
    ∃ w : BoundedRelationCover M (alternatingGenerator a r m hm),
      w ∈ B.geometricFrameGroup hlarge h hr F.k ∧ Commute z w ∧
      ∀ (j : Fin 5) (x : V.val),
        (coverMap M (alternatingGenerator a r m hm) w).val.val (e (j,0),translate a (u (e (j,0))) x.val) =
          (e (j,1),translate a (u (e (j,1))) x.val) := by
  classical
  let g : Fin 5 → BoundedRelationCover M (alternatingGenerator a r m hm) := fun j =>
    B.distinctSlotStar hlarge h hr (bankRow e j) u (F.restrict (bankRow_subset e j)) V privateCycleStar
  let l := List.finRange 5
  let w := (l.map g).prod
  refine ⟨w,?_,?_,?_⟩
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_mem_geometricFrameGroup hlarge h hr (bankRow e j) u
      (F.restrict (bankRow_subset e j)) V privateCycleStar
  · apply Commute.list_prod_right
    intro t ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    exact B.distinctSlotStar_uniform_fixer hlarge h hr (bankRow e j) b
      (fun hi => hb (bankRow_subset e j hi)) u (F.restrict (bankRow_subset e j)) (v j)
      (hu j) V z hz (hfix j) privateCycleStar
  · intro j x
    let q : BoundedRelationCover M (alternatingGenerator a r m hm) →* Equiv.Perm (TrackPoint a (m+1)) :=
      (polygonFullGroup a (m+1)).subtype.comp
        ((polygonAlternatingGroup a (m+1)).subtype.comp (coverMap M (alternatingGenerator a r m hm)))
    change q w (e (j,0),translate a (u (e (j,0))) x.val) = _
    change q ((l.map g).prod) _ = _
    rw [map_list_prod,List.map_map]
    apply perm_list_prod_transport l (List.nodup_finRange 5) (fun i => q (g i)) j (by simp [l])
    · have he := B.distinctSlotStar_apply hlarge h hr (bankRow e j) u
        (F.restrict (bankRow_subset e j)) V privateCycleStar 0 x
      rw [privateCycleStar_projection,privateCycle_apply_zero] at he
      exact he
    · intro i hi hij
      constructor
      · exact B.frameStar_supported hlarge h hr _ u (F.restrict (bankRow_subset e i)) V
          (universalMap (orderedTrackHom (bankRow e i)) privateCycleStar) _
          (bank_other_frame_notmem e u V i j 0 hij _)
      · exact B.frameStar_supported hlarge h hr _ u (F.restrict (bankRow_subset e i)) V
          (universalMap (orderedTrackHom (bankRow e i)) privateCycleStar) _
          (bank_other_frame_notmem e u V i j 1 hij _)

end InitialCoverSystem
end PrivateBankWord

end SimpleAmenable
end
end

end OAI
