import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

def lookup (e : Fin n → Fin N) (i : Fin N) : Option (Fin n) :=
  (List.finRange n).find? (fun j => e j == i)

lemma lookup_some {e : Fin n → Fin N} {i : Fin N} {j : Fin n}
    (h : lookup e i=some j) : e j=i := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma lookup_none_iff (e : Fin n → Fin N) (i : Fin N) :
    lookup e i=none ↔ ∀ j,e j≠i := by
  simp [lookup,List.find?_eq_none]

lemma lookup_self {e : Fin n → Fin N} (he : Function.Injective e) (j : Fin n) :
    lookup e (e j)=some j := by
  cases hh : lookup e (e j) with
  | none => exact False.elim ((lookup_none_iff e (e j)).mp hh j rfl)
  | some k =>
    have hk := he (lookup_some hh)
    cases hk
    rfl

def extend {β : Type*} (e : Fin n → Fin N) (base : Fin N → β) (y : Fin n → β) : Fin N → β :=
  fun i => (lookup e i).elim (base i) y

lemma extend_at {β : Type*} {e : Fin n → Fin N} (he : Function.Injective e)
    (base : Fin N → β) (y : Fin n → β) (j : Fin n) : extend e base y (e j)=y j := by
  simp [extend,lookup_self he]

lemma extend_outside {β : Type*} (e : Fin n → Fin N)
    (base : Fin N → β) (y : Fin n → β) (i : Fin N) (hi : ∀ j,e j≠i) :
    extend e base y i=base i := by
  simp [extend,(lookup_none_iff e i).mpr hi]

lemma extend_self {β : Type*} (e : Fin n → Fin N) (base : Fin N → β) :
    extend e base (fun j => base (e j))=base := by
  funext i
  unfold extend
  cases hh : lookup e i with
  | none => rfl
  | some j => simp only [Option.elim_some,lookup_some hh]

lemma map_extend {β γ : Type*} (f : β → γ) (e : Fin n → Fin N)
    (base : Fin N → β) (y : Fin n → β) :
    (fun i => f (extend e base y i))=extend e (fun i => f (base i)) (fun j => f (y j)) := by
  funext i
  unfold extend
  cases lookup e i <;> rfl

def activeIndices (x : Fin N → ℚ) : List (Fin N) :=
  (List.finRange N).filter (fun i => decide (|x i|<1))

def activeIndex (x : Fin N → ℚ) : Fin (activeIndices x).length → Fin N :=
  (activeIndices x).get

lemma activeIndices_mem (x : Fin N → ℚ) (i : Fin N) :
    i∈activeIndices x ↔ |x i|<1 := by simp [activeIndices]

lemma activeIndex_injective (x : Fin N → ℚ) : Function.Injective (activeIndex x) := by
  exact ((List.nodup_finRange N).filter _).injective_get

lemma activeIndex_range (x : Fin N → ℚ) (i : Fin N) :
    (∃ j,activeIndex x j=i) ↔ |x i|<1 := by
  rw [←activeIndices_mem]
  exact List.mem_iff_get.symm

lemma activeIndex_interior (x : Fin N → ℚ) (j : Fin (activeIndices x).length) :
    |x (activeIndex x j)|<1 := (activeIndex_range x _).mp ⟨j,rfl⟩

lemma activeIndices_length_le (x : Fin N → ℚ) : (activeIndices x).length≤N := by
  have hh := List.length_filter_le (fun i : Fin N => decide (|x i|<1)) (List.finRange N)
  simp only [List.length_finRange] at hh
  exact hh

lemma extend_cube {e : Fin n → Fin N} (x : Fin N → ℚ) (y : Fin n → ℚ)
    (hx : ∀ i,|x i|≤1) (hy : ∀ j,|y j|≤1) : ∀ i,|extend e x y i|≤1 := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hx i
  | some j => exact hy j

lemma extended_difference_bound (e : Fin n → Fin N) (x : Fin N → ℝ) (y : Fin n → ℝ)
    {r : ℝ} (hr : 0≤r) (hy : ‖y-(fun j => x (e j))‖≤r) : ‖extend e x y-x‖≤r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  have hj := (pi_norm_le_iff_of_nonneg hr).mp hy
  change ‖extend e x y i-x i‖≤r
  unfold extend
  cases hh : lookup e i with
  | none => simpa using hr
  | some j => simpa only [Option.elim_some,Pi.sub_apply,lookup_some hh] using hj j

lemma sum_lookup {β : Type*} [AddCommMonoid β] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → Fin n → β) :
    (∑ i,(lookup e i).elim 0 (f i))=∑ j,f (e j) j := by
  symm
  apply Fintype.sum_of_injective e he
  · intro i hi
    have hn : ∀ j,e j≠i := fun j hj => hi ⟨j,hj⟩
    simp only [(lookup_none_iff e i).mpr hn,Option.elim_none]
  · intro j
    simp only [lookup_self he,Option.elim_some]

lemma sum_extend {β γ : Type*} [AddCommMonoid γ] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → β → γ) (base : Fin N → β) (y : Fin n → β) :
    (∑ i,f i (extend e base y i))=
      (∑ i,(lookup e i).elim (f i (base i)) (fun _ => 0))+(∑ j,f (e j) (y j)) := by
  rw [←sum_lookup e he (fun i j => f i (y j)),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold extend
  cases lookup e i <;> simp

lemma real_active_outside_endpoint (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N)
    (hi : lookup (activeIndex x) i=none) : |(x i:ℝ)|=1 := by
  have hn : ¬|x i|<1 := by
    intro h
    obtain ⟨j,hj⟩ := (activeIndex_range x i).mpr h
    exact (lookup_none_iff _ _).mp hi j hj
  have he : |x i|=1 := le_antisymm (hx i) (le_of_not_gt hn)
  exact_mod_cast he

end CurrentKS.RationalFace

end OAI
