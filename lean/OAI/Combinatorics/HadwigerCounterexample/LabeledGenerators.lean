import OAI.Combinatorics.HadwigerCounterexample.CoordinateDuality

namespace OAI

/-! # Labeled Generators -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I] [AddCommGroup X]
    [Module F X] [AddCommGroup Y] [Module F Y]

structure Club (I X L : Type) where
  valid : I→Prop
  writes : I→ X
  addr : I→ Bool→L

abbrev Straps (L : Type) := Bool→Finset L
variable (C : Club I X L)
namespace Club
def zone (s : Straps L) (i) := C.valid i ∧ ∀ b,C.addr i b∉s b
def band (s : Straps L) : Space X := Submodule.span F {x|∃ i, C.zone s i∧C.writes i=x}
def bundle (p : Finset I) (s : Straps L) :=
  (∀ i∈p,zone C s i) ∧ ∀ b : Bool, Set.InjOn (fun i=> C.addr i b) (p : Set I)
def contents (p : Finset I) := ∑ i∈p,C.writes i

def length3 (s : Straps L) (π : X→ₗ[F] Y) (x : X) :=
    ∃ p : Finset I,C.bundle p s ∧ p.card≤3 ∧ C.contents p=x ∧ π x=0
def ration (s : Straps L) (π : X→ₗ[F] Y) : Space X := Submodule.span F (C.length3 s π)

def yield3 (s : Straps L) (π : X→ₗ[F] Y) :=
  ∀ u:Straps L,(∀ b,(u b).card≤2) → ∀ y,∃ i,zone C (s⊔u) i ∧ π (C.writes i)=y

omit [DecidableEq L] [DecidableEq I] in
theorem band_write (s : Straps L) {i : I} (hi : C.zone s i) :
    C.writes i∈ C.band s := subset_span ⟨i,hi,rfl⟩
omit [DecidableEq L] [DecidableEq I] in
theorem band_contents (s : Straps L) {p : Finset I} (hp : C.bundle p s) :
    C.contents p∈ C.band s := Submodule.sum_mem _ fun i hi=> band_write C s (hp.1 i hi)
omit [DecidableEq L] [DecidableEq I] in
theorem length3_zero (s : Straps L) (π : X→ₗ[F] Y) :
    C.length3 s π 0 := by refine ⟨∅,⟨?_,?_⟩,?_,?_,?_⟩ <;> simp [contents]

omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem zone_smaller {s t : Straps L} (h : s≤t) (i:I) (hi : zone C t i) : zone C s i :=
  ⟨hi.1,fun b hx=> hi.2 b (h b hx)⟩
omit [DecidableEq L] [DecidableEq I] in
theorem ration_le (s : Straps L) (π : X→ₗ[F] Y) : ration C s π ≤ C.band s⊓LinearMap.ker π := by
  refine Submodule.span_le.mpr ?_
  rintro i ⟨x,ha,hb,rfl,hg⟩
  exact ⟨band_contents C s ha,hg⟩

def addrs (p : Finset I) : Straps L := fun b=>p.image (fun i=> C.addr i b)
omit [DecidableEq I] in
theorem yield_after (s : Straps L) (π : X→ₗ[F] Y) (h : yield3 C s π)
    (p : Finset I) (hp : p.card≤ 2) (y : Y) :
    ∃ i,zone C s i ∧ π (C.writes i)=y ∧
      ∀ j∈p,∀ b,C.addr i b≠C.addr j b := by
  obtain ⟨i,hi,ht⟩ := h (addrs C p) (fun i=>card_image_le.trans hp) y
  refine ⟨i,C.zone_smaller le_sup_left i hi,ht,fun j hj b h=>?_⟩
  exact hi.2 b (mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,h.symm⟩))

def different (i j : I) := ∀ b,C.addr i b≠ C.addr j b
omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem different_ne {i j : I} (h : C.different i j) : i≠j := fun hx=> h true (hx ▸ rfl)
omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem bundle_one (s : Straps L) {i} (h : zone C s i) : bundle C {i} s := by
  constructor
  · intro j hj; rwa [mem_singleton.mp hj]
  simp

omit [DecidableEq L] [AddCommGroup X] [Module F X] in
theorem bundle_insert (s : Straps L) {i} (h : zone C s i) (p : Finset I) (hp : bundle C p s)
    (he : ∀ j∈p,C.different i j) : bundle C (insert i p) s := by
  refine ⟨fun j hj=>?_,fun b y hy z hz hh=>?_⟩
  · rcases mem_insert.mp hj with h'|h'
    · exact h' ▸ h
    exact hp.1 j h'
  rcases mem_insert.mp hy with h'|h'
  · subst y; rcases mem_insert.mp hz with hz|hz
    · exact hz.symm
    exact (he _ hz b hh).elim
  rcases mem_insert.mp hz with hz|hz
  · subst z; exact (he _ h' b hh.symm).elim
  exact hp.2 b h' hz hh

set_option maxHeartbeats 900000 in
theorem ration_eq (s : Straps L) (π : X→ₗ[F] Y) (h : yield3 C s π) :
    ration C s π=C.band s⊓LinearMap.ker π := by
  classical
  let R:=ration C s π; let q:=R.mkQ

  have hr (i j:I) (hi:C.zone s i) (hj:C.zone s j) (ht : π (C.writes i)=π (C.writes j))
      (hh : C.different i j) : q (C.writes i)=q (C.writes j) := by
    have hg:=C.different_ne hh
    let W := C.writes
    apply add_right_cancel (b:=q (W j))
    rw [char_two,←map_add]
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    refine subset_span ⟨{i,j},C.bundle_insert s hi _ (C.bundle_one s hj)
      (fun z hz=> (mem_singleton.mp hz).symm ▸ hh),by simp [hg],
      by simp [contents,W,hg],?_⟩
    rw [map_add,ht,char_two]
  let f:=C.writes
  have hg (i j:I) (hi:C.zone s i) (hj:C.zone s j) (ht : π (f i)=π (f j)) :
      q (f i)=q (f j) := by
    obtain ⟨t,ht',hy,hb⟩:=C.yield_after s π h {i,j} (by
      by_cases hi : i=j <;> simp [hi]) (π (f j))
    exact (hr t i ht' hi (hy.trans ht.symm) (hb i (by simp))).symm.trans
      (hr t j ht' hj hy (hb j (by simp)))
  choose g he hG hP using fun y=>C.yield_after s π h ∅ (by simp) y
  let F (x : Y) := q (f (g x))
  have hq i (hi:C.zone s i) : F (π (f i))=q (f i) := hg _ i (he _) hi (hG _)
  have h0 : F 0=0 := by
    have hh:=he 0
    refine (Submodule.Quotient.mk_eq_zero R).mpr (subset_span ?_)
    exact ⟨{g 0},C.bundle_one s hh, by simp, by simp [f,contents], hG 0⟩
  have hh (x y) : F (x+y)=F x+F y := by
    let i:=g x
    obtain ⟨j,hj,hJ,hA⟩:=C.yield_after s π h {i} (by simp) y
    have hai:=hA i (by simp)
    have hg' : j≠i:=C.different_ne hai
    let t : Finset I := {j,i}
    have ht : t.card=2 := by simp [t,hg']
    obtain ⟨k,hk,hK,hB⟩:=C.yield_after s π h t (by omega) (x+y)
    have hkt : k∉t := fun hx=> C.different_ne (hB k hx) rfl
    have hQ :
        q (f k)+(q (f j)+q (f i))=0 := by
      have hR : C.length3 s π (f k+(f j+f i)) := by
        refine ⟨insert k t,C.bundle_insert s hk _ (C.bundle_insert s hj _ (C.bundle_one s
          (he x)) (fun i hi => hA i hi)) hB,?_,?_,?_⟩
        · rw [card_insert_of_notMem hkt,ht]
        · rw [contents, Finset.sum_insert hkt]
          simp [t,f,hg']
        rw [map_add,map_add,hK,hJ,hG]
        rw [add_comm y,char_two]
      rw [← map_add,←map_add]
      exact (Submodule.Quotient.mk_eq_zero R).mpr (subset_span hR)
    change q _+ _=0 at hQ
    have hq' (z a) (hz:zone C s a) (h : π (C.writes a)=z) : q (f a)=F z := by rw [←h]; exact (hq a hz).symm
    rw [hq' _ k hk hK,hq' _ j hj hJ,hq' x i (he x) (hG x),add_comm (F y)] at hQ
    exact add_right_cancel (hQ.trans (char_two _).symm)
  apply le_antisymm (ration_le ..)
  rintro x ⟨hy,hx⟩
  apply (Submodule.Quotient.mk_eq_zero R).mp
  have hz {x} (h : x∈C.band s) : q x=F (π x) := by
    unfold band at h; induction h using Submodule.span_induction with
    | zero => rw [map_zero,map_zero,h0]
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx; exact (hq i hi).symm
    | add a b _ _ ha hb => rw [map_add,map_add,hh,ha,hb]
    | smul a b _ hb =>
      rcases bit_cases a with ha|ha
      · rw [ha,zero_smul,map_zero,map_zero,h0]
      rw [ha,one_smul,hb]
  change q x=0; change π x=0 at hx
  rw [hz hy,hx,h0]
end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
