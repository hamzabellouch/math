import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerCongruences

namespace OAI

/-! Counting lifts of a residue class inside a prime-power interval. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_residue_fiber_card {n m a : ℕ} (hn : 0<n) (F : Finset ℕ)
    (hbound : ∀ x∈F, x<n*m) (hmod : ∀ x∈F, x%n=a) : F.card≤m := by
  classical
  have hinj : Set.InjOn (fun x : ℕ => x/n) (F:Set ℕ) := by
    intro x hx y hy he
    change x/n=y/n at he
    calc
      x = x%n+n*(x/n) := (Nat.mod_add_div x n).symm
      _ = y%n+n*(y/n) := by rw [hmod x hx,hmod y hy,he]
      _ = y := Nat.mod_add_div y n
  have hsub : F.image (fun x => x/n) ⊆ range m := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hn).mpr
      (by simpa only [Nat.mul_comm] using hbound x hx))
  calc
    F.card = (F.image (fun x => x/n)).card := (card_image_of_injOn hinj).symm
    _ ≤ (range m).card := card_le_card hsub
    _ = m := card_range m

lemma halasz_prime_power_residue_card {p r j a : ℕ} [Fact p.Prime] (hj : j≤r+1)
    (F : Finset (ZMod (p^(r+1))))
    (hmod : ∀ z∈F, z.val%(p^j)=a) : F.card≤p^(r+1-j) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero (p^(r+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hsize : p^j*p^(r+1-j)=p^(r+1) := by rw [← pow_add,Nat.add_sub_of_le hj]
  have hb : ∀ z∈F.image ZMod.val, z<p^j*p^(r+1-j) := by
    intro z hz
    obtain ⟨w,_,rfl⟩ := mem_image.mp hz
    rw [hsize]
    exact ZMod.val_lt w
  have hm : ∀ z∈F.image ZMod.val, z%(p^j)=a := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact hmod w hw
  calc
    F.card = (F.image ZMod.val).card :=
      (card_image_of_injective F (ZMod.val_injective (p^(r+1)))).symm
    _ ≤ p^(r+1-j) := halasz_residue_fiber_card (pow_pos hp.pos _) _ hb hm

end TwoPointCorrelations

end OAI
