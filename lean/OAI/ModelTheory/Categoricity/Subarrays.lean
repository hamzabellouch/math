import OAI.ModelTheory.Categoricity.ArrayEmbeddings

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

theorem small_hull (loc : ∀ a b : B, (Set.Icc a b).Countable)
    (A : Set B) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ S : Set B, A ⊆ S ∧ S.OrdConnected ∧ Nonempty S ∧
      NoMinOrder S ∧ NoMaxOrder S ∧ DenselyOrdered S ∧ #S ≤ κ := by
  classical
  let p : B := Classical.arbitrary B
  let T : Set B := A ∪ {p}
  let lo : B → B := fun x => (exists_lt x).choose
  let hi : B → B := fun x => (exists_gt x).choose
  have hlo (x : B) : lo x < x := (exists_lt x).choose_spec
  have hhi (x : B) : x < hi x := (exists_gt x).choose_spec
  let S : Set B := {x | ∃ a : T, ∃ b : T, lo a < x ∧ x < hi b}
  have hTS : T ⊆ S := fun x hx => ⟨⟨x, hx⟩, ⟨x, hx⟩, hlo x, hhi x⟩
  have hc : S.OrdConnected := by
    constructor
    rintro x ⟨a, b, hax, hxb⟩ y ⟨c, d, hcy, hyd⟩ z ⟨hxz, hzy⟩
    exact ⟨a, d, hax.trans_le hxz, hzy.trans_lt hyd⟩
  have hmin : NoMinOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hay, hyx⟩ := exists_between hax
    exact ⟨⟨y, a, b, hay, hyx.trans hxb⟩, hyx⟩⟩
  have hmax : NoMaxOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hxy, hyb⟩ := exists_between hxb
    exact ⟨⟨y, a, b, hax.trans hxy, hyb⟩, hxy⟩⟩
  have hd : DenselyOrdered S := ⟨by
    intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := exists_between hxy
    exact ⟨⟨z, hc.out x.property y.property ⟨hxz.le, hzy.le⟩⟩, hxz, hzy⟩⟩
  refine ⟨S, Set.Subset.trans Set.subset_union_left hTS, hc,
    ⟨⟨p, hTS (Or.inr rfl)⟩⟩, hmin, hmax, hd, ?_⟩
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le A {p}).trans
    simpa only [Cardinal.mk_singleton, Cardinal.add_eq_self hκ] using
      add_le_add hA (Cardinal.one_le_aleph0.trans hκ)
  have he : S = ⋃ ab : T × T, Set.Ioo (lo ab.1) (hi ab.2) := by
    ext x
    simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioo]
    exact ⟨fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩
  rw [he]
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  have hb (ab : T × T) : #(Set.Ioo (lo ab.1) (hi ab.2)) ≤ κ :=
    (Cardinal.mk_le_aleph0_iff.2 ((loc _ _).mono Set.Ioo_subset_Icc_self)).trans hκ
  apply (Cardinal.sum_le_sum _ _ hb).trans
  simp only [Cardinal.sum_const, Cardinal.mk_prod, Cardinal.lift_id]
  calc
    (#T * #T) * κ ≤ (κ * κ) * κ := mul_le_mul' (mul_le_mul' hT hT) le_rfl
    _ = κ := by rw [Cardinal.mul_eq_self hκ, Cardinal.mul_eq_self hκ]

end BaseOrders

namespace Arrays

open Tuples
open scoped symmDiff

variable (M : Data.{u})

def Data.restrict (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] : Data.{u} where
  I := J
  B := S
  indexNonempty := inferInstance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable a b := (M.locallyCountable a b).preimage Subtype.val_injective
  bits t n b := M.bits (Tuples.map (Function.Embedding.subtype J) t) n b

variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq S := Classical.decEq S

def Data.restrictMap : Map (M.restrict J S) M where
  index := Function.Embedding.subtype J
  base := OrderEmbedding.subtype S
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees _ _ _ := by simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false]; rfl

@[simp] theorem Data.restrictMap_colors (t : Tuple J) (b : M.B) :
    (M.restrictMap J S).colors t b = M.colors (Tuples.map (Function.Embedding.subtype J) t) b := by
  simp only [Map.colors, Data.restrictMap, Finset.notMem_empty, decide_false, Bool.xor_false,
    Data.colors]
  rfl

theorem Data.restrict_object (hCH : CH.{u}) (hM : M.IsObject hCH) :
    (M.restrict J S).IsObject hCH := by
  intro t
  have hc := (hM (Tuples.map (Function.Embedding.subtype J) t)).preimage
    (Subtype.val_injective (p := fun b => b ∈ S))
  apply hc.mono
  intro b hb hh
  apply hb
  exact (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp hh

theorem Data.restrict_strong (hCH : CH.{u}) (hS : S.OrdConnected)
    (hbad : ∀ t : Tuple J, {b | ¬ Tests.Test hCH
      (fun r => M.colors r b) (Tuples.map (Function.Embedding.subtype J) t)} ⊆ S) :
    (M.restrictMap J S).Strong hCH := by
  have he : Set.range (M.restrictMap J S).base = S := by
    change Set.range (Subtype.val : S → M.B) = S
    exact Subtype.range_coe_subtype
  constructor
  · rw [he]; exact hS
  · intro t b hb
    rw [he] at hb
    have ht := not_not.1 (fun h => hb (hbad t h))
    have hm := (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp ht
    exact (Tests.congr hCH t (fun _ _ => Data.restrictMap_colors J S _ b)).mpr hm

theorem Data.cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hI : #M.I ≤ κ) (hB : #M.B ≤ κ) : #M.Carrier ≤ κ := by
  let enc : M.Carrier → M.I ⊕ M.B ⊕ Finset M.B ⊕ Finset ℕ ⊕
      (Tuple M.I × ℕ × Finset M.B) ⊕ (Tuple M.I × M.B × Finset ℕ)
    | .index i => .inl i
    | .base b => .inr (.inl b)
    | .group s => .inr (.inr (.inl s))
    | .star v => .inr (.inr (.inr (.inl v)))
    | .row t n s => .inr (.inr (.inr (.inr (.inl (t, n, s)))))
    | .col t b v => .inr (.inr (.inr (.inr (.inr (t, b, v)))))
  have he : Function.Injective enc := by
    intro a b h
    cases a <;> cases b <;> simp_all [enc]
  apply (Cardinal.mk_le_of_injective he).trans
  simp only [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero,
    Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.mk_finset_of_infinite]
  have ht := Tuples.cardinal_bound κ hκ hI
  calc
    #M.I + (#M.B + (#M.B + (ℵ₀ +
      (#(Tuple M.I) * (ℵ₀ * #M.B) + #(Tuple M.I) * (#M.B * ℵ₀))))) ≤
      κ + (κ + (κ + (κ + (κ * (κ * κ) + κ * (κ * κ))))) := by gcongr
    _ = κ := by simp only [Cardinal.mul_eq_self hκ, Cardinal.add_eq_self hκ]

theorem Data.cardinal_eq : #M.Carrier = max (max #M.I #M.B) ℵ₀ := by
  apply le_antisymm
  · exact M.cardinal_le _ (le_max_right _ _) ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _))
  · apply max_le
    · exact max_le (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h))
        (Cardinal.mk_le_of_injective (fun _ _ h => Point.base.inj h))
    · have h := Cardinal.mk_le_of_injective (f := fun v : ULift.{u} (Finset ℕ) =>
          Point.star (I := M.I) (B := M.B) v.down) (fun a b h => ULift.ext _ _ (Point.star.inj h))
      simpa only [Cardinal.mk_uLift, Cardinal.mk_finset_of_infinite, Cardinal.mk_nat,
        Cardinal.lift_aleph0] using h

end Arrays

end CHObstruction

end

end OAI
