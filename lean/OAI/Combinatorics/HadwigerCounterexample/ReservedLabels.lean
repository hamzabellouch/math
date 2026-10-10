import OAI.Combinatorics.HadwigerCounterexample.FreshGeneratorCorrection

namespace OAI

/-! # Reserved Labels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
namespace StatusAnalysis
variable {I L : Type} [DecidableEq L] [DecidableEq I] {d e : ℕ}
open Club
set_option maxHeartbeats 600000 in
theorem fresh_single (C : Club I (Signal d e) L) {s : Straps L} {V}
    (h : C.travels s 4 (view d e) V) (x : Signal d e) (hx : x∈V) :
    ∃ p:Finset I,C.bundle p s∧ C.contents p=x∧1≤p.card∧p.card≤7 := by
  classical
  obtain ⟨hh,hC⟩:= C.travel_now h
  let Q:= view d e
  obtain ⟨i,hi,hI,_⟩:= C.yield_after s Q hC ∅ (by simp) (Q x)
  let p : Finset I:= {i}
  have hp := C.bundle_one s hi
  have hr : C.travels (s⊔ C.addrs p) 3 Q V := C.travel_more h (C.addrs p)
    (fun i=>card_image_le.trans (by unfold p; simp : p.card≤1)) (by norm_num)
  obtain ⟨q,hq,hQ,hT⟩ := jump_two C hr (ker_two _) (x-C.writes i) (by
    constructor
    · exact Submodule.sub_mem _ hx (hh ▸ C.band_write s hi)
    change Q (x-C.writes i)=0
    rw [map_sub,hI,sub_self])
  obtain ⟨ha,hb⟩:= C.bundle_combine hp hq
  refine ⟨p∪q,ha,?_,?_,(card_union_le ..).trans ?_⟩
  · change ∑ j∈p∪q,_=_
    rw [sum_union hb, ←show C.contents q=(∑ j∈q,_) from rfl, hT]
    simp only [sum_singleton,add_sub_cancel]
  · exact card_pos.mpr ⟨i, mem_union_left _ (by simp [p])⟩
  simp only [p,card_singleton]
  omega

variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates}
abbrev Congress (I : Grid→Type) (A B : Rates) (L : Type) := ∀ i,Club (I i) (Suite A B i) L
namespace Guild
variable (C : Congress I A B L)
def chapter (s : Straps L) : StatusSp A B := fun i=> (C i).band s
def excess (s : Straps L) := ∑ i:Grid,overage (chapter C s i)

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem excess_bound (s : Straps L) : excess C s ≤8 := by
  unfold excess
  exact (Finset.sum_le_sum (g:=fun _=>2) (fun i _=>overage_two
    (chapter C s i))).trans_eq (by norm_num [Grid,Nodes])

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem chapter_mono {s t : Straps L} (h : s≤t) (i) :
    chapter C t i ≤ chapter C s i := span_mono (fun _ ⟨a,ht,hx⟩=>
  ⟨a,(C i).zone_smaller h a ht,hx⟩)

def rich (C : Congress I A B L) :=
  ∀ i:Grid,∀ s:Straps L,sizeB s 902 → ∀ y:View (A i.1) (B i.2),∃ j,
    (C i).zone s j ∧ view _ _ ((C i).writes j)=y

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem rich_covers (h : rich C) (s : Straps L) (hs : sizeB s 902) (i) :
    coverBase (chapter C s i) := by
  intro y
  obtain ⟨j,hj,hy⟩:=h i s hs y
  exact ⟨⟨_, (C i).band_write s hj⟩,hy⟩

set_option maxHeartbeats 800000 in
omit [∀ i,DecidableEq (I i)] in
theorem stable (h : rich C) :
    ∃ s:Straps L,sizeB s 800 ∧
      ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i) := by
  classical
  have hh (k : ℕ) (hk : k≤ 8) (t : Straps L)
      (ht : sizeB t ((8-k)*100)) (hb : excess C t≤ k) :
      ∃ s:Straps L,sizeB s 800 ∧
      ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i) := by
    induction k generalizing t with
    | zero =>
      refine ⟨t,ht,fun i u hu=>?_⟩
      let v:=t⊔u
      have he : sizeB v 900:= fun i=> (card_union_le ..).trans (Nat.add_le_add (ht i) (hu i))
      constructor
      · change chapter C v i=chapter C t i
        have hm (i:Grid) : overage (chapter C t i)=0 := by
          have hy : overage (chapter C t i) ≤ 0 := le_trans (Finset.single_le_sum (s:=Finset.univ)
            (fun i _=>Nat.zero_le (overage (chapter C t i))) (Finset.mem_univ i)) hb
          exact Nat.eq_zero_of_le_zero hy
        exact eq_of_le_of_not_lt (chapter_mono C le_sup_left i) (fun hx=> Nat.not_lt_zero _
          ((overage_lt hx (rich_covers C h v (fun i=> (he i).trans (by decide)) i)).trans_eq (hm i)))
      intro w hw y
      exact h i (v⊔w) (fun i=> (card_union_le ..).trans (Nat.add_le_add (he i) (hw i))) y
    | succ k ih =>
      have hT : sizeB t 800 := fun i=> (ht i).trans (by omega)
      by_cases hE : ∃ (s:Straps L), sizeB s 100∧∃ i:Grid, chapter C (t⊔s) i < chapter C t i
      · obtain ⟨u,hu,i,hU⟩:=hE
        let s:=t⊔u
        have he : sizeB s ((8-k)*100):= fun i=> (card_union_le ..).trans
          ((Nat.add_le_add (ht i) (hu i)).trans (by omega))
        refine ih (by omega) s he ?_
        have hS : excess C s < excess C t := by
          unfold excess
          have h1 := overage_lt hU (rich_covers C h s (fun i=> (he i).trans (by omega)) i)
          exact Finset.sum_lt_sum (fun i _=> overage_mono (chapter_mono C le_sup_left i))
            ⟨i,mem_univ _,h1⟩
        omega
      refine ⟨t,hT,fun i u hu=>?_⟩
      constructor
      · exact eq_of_le_of_not_lt (chapter_mono C (s:=t) (t:=t⊔u) le_sup_left i) (fun hx =>
          hE ⟨u,hu,i,hx⟩)
      intro w hw y
      have he : sizeB (t⊔u) 900:= fun i=> (card_union_le ..).trans (Nat.add_le_add (hT i) (hu i))
      exact h i ((t⊔u)⊔w) (fun i=> (card_union_le ..).trans (Nat.add_le_add (he i) (hw i))) y
  exact hh 8 (Nat.le_refl _) ⊥ (by intro i; change (∅:Finset L).card ≤_; simp) (excess_bound C _)
end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
