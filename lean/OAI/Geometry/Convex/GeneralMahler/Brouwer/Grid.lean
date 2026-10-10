import OAI.Geometry.Convex.GeneralMahler.Brouwer.Color

namespace OAI
/-! A colorful primitive room in grids on the standard simplex. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]
  (N:ℕ)

abbrev Grid :=
  { f : I → Fin (N+1) // ∑ i,(f i).val = N }

lemma grid_extend (g : I → ℕ) (hg : ∑ i,g i ≤ N) :
    ∃ x : Grid I N, ∀ i, g i ≤ (x.val i).val := by
  obtain ⟨i⟩ := ‹Nonempty I›
  let f (j:I) := g j + if j=i then N - ∑ j,g j else 0
  have h : ∑ j,f j = N := by
    simp [f,sum_add_distrib,hg]
  have h1 (j:I) : f j<N+1 := by
    have he : f j ≤ ∑ j, f j := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ _)
    omega
  exact ⟨⟨fun j => ⟨f j,h1 j⟩, h⟩, fun j => Nat.le_add_right _ _⟩

instance : Nonempty (Grid I N) :=
  have h := grid_extend I N (fun _=>0) (by simp); h.imp (fun _ _=>True.intro) |>
    fun he => by obtain ⟨x,hx⟩:=he; exact ⟨x⟩

private def place {X : Type*} [Fintype X] (x:X) : ℕ := (Fintype.equivFin X x).val
private lemma small {X : Type*} [Fintype X] (x:X) : place x < Fintype.card X :=
  (Fintype.equivFin X x).isLt
private lemma place_inj {X : Type*} [Fintype X] {x y:X} (h:place x=place y) : x=y :=
  (Fintype.equivFin X).injective (Fin.ext h)

def key (i : I) (x : Grid I N) : ℕ :=
    1+(x.val i).val*Fintype.card (Grid I N)+place x
omit [Nonempty I] in
lemma key_pos i x : 0<key I N i x := by unfold key; omega
omit [Nonempty I] in
lemma key_lt i x :
    key I N i x < (N+1)*Fintype.card (Grid I N)+1 := by
  have h := small x
  have he := Nat.mul_le_mul_right (Fintype.card (Grid I N)) (show (x.val i).val ≤ N from by
    have h := (x.val i).isLt; omega)
  unfold key; rw [add_mul]; omega
omit [Nonempty I] in
lemma key_order (i:I) (x y:Grid I N) (h:(x.val i).val < (y.val i).val) :
    key I N i x < key I N i y := by
  have he := Nat.mul_le_mul_right (Fintype.card (Grid I N)) h
  have hv := small x
  unfold key
  change ((x.val i).val+1)*_ ≤ _ at he
  rw [add_mul] at he; omega
omit [Nonempty I] in
lemma key_inj (i:I) : Function.Injective (key I N i) := by
  intro x y h
  rcases lt_trichotomy (x.val i).val (y.val i).val with h₁|h₁|h₁
  · exact False.elim (ne_of_lt (key_order I N i x y h₁) h)
  · apply place_inj
    unfold key at h
    rw [h₁] at h
    omega
  exact False.elim (ne_of_lt (key_order I N i y x h₁) h.symm)

def grank (i:I) : I⊕Grid I N → ℕ := Sum.elim
  (fun j => if i=j then 0 else (N+1)*Fintype.card (Grid I N)+1+place j)
  (key I N i)

omit [Nonempty I] in
lemma lkey i x : grank I N i (.inl i)<grank I N i (.inr x) := by
  simpa [grank] using key_pos I N i x
omit [Nonempty I] in
lemma hkey i j (h:i≠j) x : grank I N i (.inr x)<grank I N i (.inl j) := by
  simp only [grank,h,Sum.elim_inl,Sum.elim_inr,ite_false]
  exact lt_of_lt_of_le (key_lt I N _ _) (Nat.le_add_right ..)
omit [Nonempty I] in
lemma inex i j x : grank I N i (.inl j) ≠ grank I N i (.inr x) := by
  by_cases h:i=j
  · rw [← h]; exact ne_of_lt (lkey ..)
  exact Ne.symm (ne_of_lt (hkey _ _ i j h x))

def gridOrder : GOrders I (Grid I N) where
  rank := grank I N
  inj := by
    intro i a b
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [grank,Sum.elim_inl,Sum.inl.injEq]
        split_ifs with h ho <;> grind [place_inj]
      | inr b => exact fun h => False.elim (inex I N _ _ _ h)
    | inr a =>
      cases b with
      | inl b => exact fun h => False.elim (inex I N _ _ _ h.symm)
      | inr b => exact fun h => congrArg _ (key_inj I N _ h)
  low := lkey I N
  high := hkey I N

lemma full_approx (f : Grid I N → I) :
    ∃ b : I→ℕ, ∃ s:Finset (I⊕Grid I N),
    inside s ∧ (∀ x:Grid I N, Sum.inr x∈s → ∀ i,
      b i ≤ (x.val i).val ∧ (x.val i).val ≤ b i+Fintype.card I) ∧
      (∀ i, b i=0 ∨ ∃ x:Grid I N, Sum.inr x∈s ∧ f x=i) := by
  let r := gridOrder I N
  obtain ⟨s,h,he⟩ := full_room r f
  have hs : inside s := by
    by_contra hn
    obtain ⟨x⟩ : Nonempty (Grid I N) := inferInstance
    obtain ⟨i,hi⟩ := h.2 (.inr x)
    have hmem : Sum.inl i ∈ s := by
      have hi' := Finset.mem_image.mp (show i∈s.image (Sum.elim id f) from he.symm ▸ mem_univ _)
      obtain ⟨a,ha,hb⟩ := hi'
      cases a with
      | inl j =>
        change j=i at hb; subst j; exact ha
      | inr y => exact False.elim (hn ⟨_,ha⟩)
    exact not_lt_of_ge (hi _ hmem) (r.low _ _)
  obtain ⟨x,hx⟩ := hs
  obtain ⟨v,hv⟩ := min_nodes r.toOrders (show s.Nonempty from ⟨_,hx⟩)
  have H (i j:I) (he:v i=.inl j) : i=j := by
    by_contra he'
    have hh := (hv i).2 _ hx
    rw [he] at hh; exact not_lt_of_ge hh (r.high i j he' _)
  let b := fun i => Sum.elim (fun _=>0) (fun a:Grid I N=>(a.val i).val) (v i)
  refine ⟨b,s,⟨x,hx⟩,?_,?_⟩
  · intro y hy
    have hh (i:I) : b i ≤ (y.val i).val := by
      simp only [b]; cases e : v i with
      | inl j => simp
      | inr z =>
        have h := (hv i).2 _ hy
        rw [e] at h
        by_contra! he
        exact not_lt_of_ge h (key_order I N _ _ _ he)
    have hc : N ≤ (∑ i, b i) + Fintype.card I := by
      by_contra! hn
      have hp : ∑ i, (b i+1) ≤ N := by simpa [Finset.sum_add_distrib] using hn.le
      obtain ⟨l,hl⟩ := grid_extend I N _ hp
      obtain ⟨i,hi⟩ := h.2 (.inr l)
      have hi' := hi _ (hv i).1
      have hf := hl i
      cases e : v i with
      | inl j =>
        rw [e, ← H i j e] at hi'
        exact not_lt_of_ge hi' (r.low _ _)
      | inr w =>
        simp only [b,e, Sum.elim_inr] at hf
        rw [e] at hi'; exact not_lt_of_ge hi' (key_order I N _ _ _ hf)
    intro i
    refine ⟨hh i,?_⟩
    have hp : ∑ j, (b j+ ((y.val j).val-b j)) = ∑ j,(y.val j).val :=
      Finset.sum_congr rfl fun j _ => Nat.add_sub_of_le (hh j)
    have hhi : (y.val i).val-b i ≤ ∑ j : I, ((y.val j).val-b j) :=
      Finset.single_le_sum (f := fun j : I => ((y.val j).val-b j)) (fun _ _=>Nat.zero_le _) (mem_univ i)
    rw [Finset.sum_add_distrib,y.property] at hp
    omega
  intro i
  have hi := Finset.mem_image.mp (show i∈s.image (Sum.elim id f) from he.symm ▸ mem_univ _)
  obtain ⟨y,hy,hfy⟩ := hi
  cases y with
  | inl j =>
    change j=i at hfy; subst j
    left; unfold b
    cases e:v i with
    | inl j=>simp
    | inr t =>
      have hh := (hv i).2 _ hy
      rw [e] at hh; exact False.elim (not_lt_of_ge hh (r.low i t))
  | inr t => exact Or.inr ⟨t,hy,hfy⟩
end GeneralMahler.Scarf

end

end OAI
