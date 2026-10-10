import Mathlib

namespace OAI

section
namespace SharpLogRamsey.MultiplicityClass
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

def weight (S : Finset α) (f : α→β) (y : β) : ℕ := (S.filter (fun x => f x=y)).card

def domain (U : Finset α) (f : α→β) (h : ℕ) : Finset β :=
  (U.image f).filter (fun y => h≤weight U f y)

lemma weight_mono (S U : Finset α) (hSU : S⊆U) (f : α→β) (y : β) :
    weight S f y≤weight U f y := card_le_card (filter_subset_filter _ hSU)

lemma weight_pos (S : Finset α) (f : α→β) (x : α) (hx : x∈S) :
    0<weight S f (f x) := card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩

lemma domain_card (U : Finset α) (f : α→β) (h : ℕ) :
    h*(domain U f h).card≤U.card := by
  calc
    _ = ∑ y∈domain U f h,h := by simp [mul_comm]
    _ ≤ ∑ y∈domain U f h,weight U f y :=
      sum_le_sum (fun y hy => (mem_filter.mp hy).2)
    _ ≤ ∑ y∈U.image f,weight U f y := sum_le_sum_of_subset (filter_subset _ _)
    _ = U.card := (card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem f hx)).symm

theorem exists_class (S U : Finset α) (hS : S.Nonempty) (hSU : S⊆U)
    (f : α→β) (q : ℕ) (hq : 1≤q) (hf : ∀ y,weight S f y≤q) :
    ∃ (h : ℕ) (T : Finset β), 1≤h ∧ h≤q ∧ T.Nonempty ∧
      T⊆domain U f h ∧ T⊆S.image f ∧
      (S.card:ℝ)≤2*h*(Nat.log 2 q+1:ℕ)*(T.card:ℝ) ∧
      ∀ y∈T,h≤weight S f y ∧ weight S f y<2*h := by
  let lab : α→ℕ := fun x => Nat.log 2 (weight S f (f x))
  let N := Nat.log 2 q+1
  have hN : 0<N := by dsimp [N]; omega
  have hlab : ∀ x∈S,lab x∈range N := by
    intro x hx
    apply mem_range.mpr
    have hh := Nat.log_mono_right (b := 2) (hf (f x))
    dsimp [lab,N]
    omega
  have hnz : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  obtain ⟨k,hk,hkcard⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hlab (nonempty_range_iff.mpr (by omega))
    (show (range N).card • ((S.card:ℝ)/N)≤(S.card:ℝ) by
      simp only [card_range,nsmul_eq_mul]; rw [mul_div_cancel₀ _ hnz])
  let A := S.filter (fun x => lab x=k)
  let T := A.image f
  let h := 2^k
  have hh : 1≤h := Nat.one_le_pow _ _ (by omega)
  have hkq : k≤Nat.log 2 q := by have := mem_range.mp hk; dsimp [N] at this; omega
  have hq' : h≤q :=
    (Nat.pow_le_pow_right (by omega : 0<2) hkq).trans (Nat.pow_log_le_self 2 (by omega))
  have ha : A.Nonempty := by
    apply card_pos.mp
    have hsp : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
    have hp : (0:ℝ)<A.card := lt_of_lt_of_le (div_pos hsp (by exact_mod_cast hN)) hkcard
    exact_mod_cast hp
  have hweights : ∀ y∈T,h≤weight S f y ∧ weight S f y<2*h := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    change Nat.log 2 (weight S f (f x))=k at he
    dsimp [h]
    rw [←he]
    exact ⟨Nat.pow_log_le_self 2 (by have := weight_pos S f x hx; omega),by
      simpa [pow_succ,mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1<2) (weight S f (f x))⟩
  refine ⟨h,T,hh,hq',ha.image f,?_,?_,?_,hweights⟩
  · intro y hy
    apply mem_filter.mpr
    obtain ⟨x,hx,hxy⟩ := mem_image.mp hy
    refine ⟨mem_image.mpr ⟨x,hSU (mem_filter.mp hx).1,hxy⟩,?_⟩
    exact (hweights y hy).1.trans (weight_mono S U hSU f y)
  · exact image_subset_image (filter_subset _ _)
  · have hab : A.card≤(2*h)*T.card := by
      apply card_le_mul_card_image_of_maps_to (f := f)
        (fun x hx => mem_image_of_mem f hx) (2*h)
      intro y hy
      exact (weight_mono A S (filter_subset _ _) f y).trans (hweights y hy).2.le
    have hab' : (A.card:ℝ)≤2*h*(T.card:ℝ) := by exact_mod_cast hab
    have hk' : (S.card:ℝ)≤(A.card:ℝ)*N := (div_le_iff₀ (by exact_mod_cast hN)).mp hkcard
    have hm := mul_le_mul_of_nonneg_right hab' (Nat.cast_nonneg N)
    dsimp [N] at hm hk'
    push_cast at hm hk' ⊢
    nlinarith

end
end SharpLogRamsey.MultiplicityClass

end

end OAI
