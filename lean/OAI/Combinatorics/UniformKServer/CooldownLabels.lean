import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                     
section

/-! Fixed finite label pools with a full preceding-step cooldown. No historical
label is globally reserved: only current and preceding record sets are excluded. -/
noncomputable section
namespace UniformKServer.CooldownLabels
open Finset
open scoped Classical
variable {I : Type*} [DecidableEq I]

abbrev Slot (M : ℕ) := Fin (4*M+4)

private def chooseSlot (M : ℕ) (S : Finset (Slot M)) : Slot M :=
  if h : ∃ a : Slot M, a∉S then Classical.choose h else ⟨0,by omega⟩

private theorem chooseSlot_not_mem (M : ℕ) (S : Finset (Slot M)) (hS : S.card<4*M+4) :
    chooseSlot M S∉S := by
  have he : ∃ a : Slot M, a∉S := by
    by_contra! h
    have hs : S=univ := eq_univ_of_forall h
    have hc : S.card=4*M+4 := by rw [hs,card_univ,Fintype.card_fin]
    omega
  exact by rw [chooseSlot,dite_eq_left he]; exact Classical.choose_spec he

structure State (I : Type*) (M : ℕ) where
  label : I → Slot M
  previous : Finset (Slot M)

def step (M : ℕ) (S : Finset I) (b : Option I) (D : State I M) : State I M where
  label := match b with
    | none => D.label
    | some n => Function.update D.label n (chooseSlot M (D.previous ∪ S.image D.label))
  previous := S.image D.label

def run (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I) : ℕ → State I M
  | 0 => ⟨fun _ => ⟨0,by omega⟩,∅⟩
  | t+1 => step M (S t) (birth t) (run M S birth t)

theorem previous_card (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) : (run M S birth t).previous.card≤M := by
  cases t with
  | zero => simp [run]
  | succ t => exact (card_image_le).trans (hS t)

theorem chosen_fresh (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) :
    chooseSlot M ((run M S birth t).previous ∪ (S t).image (run M S birth t).label)∉
      (run M S birth t).previous ∪ (S t).image (run M S birth t).label := by
  apply chooseSlot_not_mem
  have hc := card_union_le (run M S birth t).previous ((S t).image (run M S birth t).label)
  have hp := previous_card M S birth hS t
  have hi := (card_image_le (f:=(run M S birth t).label) (s:=S t)).trans (hS t)
  omega

theorem label_none (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (t : ℕ) (hb : birth t=none) : (run M S birth (t+1)).label=(run M S birth t).label := by
  simp only [run,step,hb]

theorem label_old (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (t : ℕ) (n i : I) (hb : birth t=some n) (hi : i≠n) :
    (run M S birth (t+1)).label i=(run M S birth t).label i := by
  simp only [run,step,hb,Function.update_of_ne hi]

theorem label_new_fresh (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) (n : I) (hb : birth t=some n) :
    (run M S birth (t+1)).label n∉
      (run M S birth t).previous ∪ (S t).image (run M S birth t).label := by
  simpa only [run,step,hb,Function.update_self] using chosen_fresh M S birth hS t

theorem injective (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (hzero : S 0=∅)
    (hnext : ∀ t, S (t+1)⊆match birth t with | none => S t | some n => insert n (S t))
    (_hnew : ∀ t n, birth t=some n → n∉S t) (t : ℕ) :
    Set.InjOn (run M S birth t).label (S t) := by
  induction t with
  | zero => simp only [hzero,coe_empty,Set.injOn_empty]
  | succ t ih =>
    cases hb : birth t with
    | none =>
      rw [label_none M S birth t hb]
      apply ih.mono
      intro i hi
      have hs : S (t+1)⊆S t := by simpa only [hb] using hnext t
      exact hs hi
    | some n =>
      have hs : S (t+1)⊆insert n (S t) := by simpa only [hb] using hnext t
      have hf := label_new_fresh M S birth hS t n hb
      intro i hi j hj he
      have hi' := hs hi
      have hj' := hs hj
      by_cases hin : i=n
      · subst i
        by_contra hnj
        have hjs : j∈S t := (mem_insert.mp hj').resolve_left (Ne.symm hnj)
        have hje := label_old M S birth t n j hb (Ne.symm hnj)
        exact hf (mem_union_right _ (mem_image.mpr ⟨j,hjs,by rw [←hje,he]⟩))
      · have his : i∈S t := (mem_insert.mp hi').resolve_left hin
        by_cases hjn : j=n
        · subst j
          have hie := label_old M S birth t n i hb hin
          exact (hf (mem_union_right _ (mem_image.mpr ⟨i,his,by rw [←hie,he]⟩))).elim
        · apply ih his ((mem_insert.mp hj').resolve_left hjn)
          simpa only [label_old M S birth t n i hb hin,label_old M S birth t n j hb hjn] using he

theorem common_anchor (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (hzero : S 0=∅)
    (hnext : ∀ t, S (t+1)⊆match birth t with | none => S t | some n => insert n (S t))
    (hnew : ∀ t n, birth t=some n → n∉S t)
    (t : ℕ) (i j : I) (hi : i∈S t) (hj : j∈S (t+1))
    (he : (run M S birth t).label i=(run M S birth (t+1)).label j) : i=j := by
  have hinj := injective M S birth hS hzero hnext hnew t
  cases hb : birth t with
  | none =>
    have hs : S (t+1)⊆S t := by simpa only [hb] using hnext t
    exact hinj hi (hs hj) (by simpa only [label_none M S birth t hb] using he)
  | some n =>
    have hs : S (t+1)⊆insert n (S t) := by simpa only [hb] using hnext t
    have hjn : j≠n := by
      intro h; subst j
      have hf := label_new_fresh M S birth hS t n hb
      exact hf (mem_union_right _ (mem_image.mpr ⟨i,hi,he⟩))
    apply hinj hi ((mem_insert.mp (hs hj)).resolve_left hjn)
    simpa only [label_old M S birth t n j hb hjn] using he

/-- A new label is absent not only now, but from the whole preceding map. -/
theorem one_step_cooldown (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) (n : I) (hb : birth (t+1)=some n) :
    (run M S birth (t+2)).label n∉(S t).image (run M S birth t).label := by
  have hf := label_new_fresh M S birth hS (t+1) n hb
  exact fun h => hf (mem_union_left _ h)

end UniformKServer.CooldownLabels

end


end

end OAI
