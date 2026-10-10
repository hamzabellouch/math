import Mathlib

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen


theorem card_fixed_of_factor {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hr : Function.Injective r) (σ : Equiv.Perm ι)
    (f g : k[X]) (hf : f = ∏ i, (X - C (r i))) (hs : f.Separable)
    (hd : g ∣ f) (hroot : ∀ i, g.eval (r i) = 0 ↔ σ i = i) :
    Fintype.card {i : ι // σ i = i} = g.natDegree := by
  classical
  have hf0 : f ≠ 0 := by rw [hf]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hf0 hd
  have hsplit : f.Splits := by rw [hf]; exact Splits.prod (fun _ _ => Splits.X_sub_C _)
  have hgr : ∀ x : k, g.eval x = 0 → ∃ i, r i = x := by
    intro x hx
    have hx' : f.eval x = 0 := by
      obtain ⟨q, rfl⟩ := hd
      simp [eval_mul, hx]
    rw [hf, eval_prod] at hx'
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hx'
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    exact ⟨i, hi.symm⟩
  let u : {i : ι // σ i = i} → g.rootSet k :=
    fun i => ⟨r i, mem_rootSet.mpr ⟨hg0, by simpa using (hroot i).mpr i.property⟩⟩
  have hu : Function.Injective u := by
    intro i j h
    apply Subtype.ext
    apply hr
    exact congrArg Subtype.val h
  have hus : Function.Surjective u := by
    intro x
    have hx : g.eval (x : k) = 0 := by simpa using (mem_rootSet.mp x.property).2
    obtain ⟨i, hi⟩ := hgr x hx
    refine ⟨⟨i, (hroot i).mp (hi ▸ hx)⟩, ?_⟩
    exact Subtype.ext hi
  let e := Equiv.ofBijective u ⟨hu, hus⟩
  rw [Fintype.card_congr e]
  exact card_rootSet_eq_natDegree (hs.of_dvd hd) (by simpa using (hsplit.of_dvd hf0 hd))

lemma swap_of_card_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 20) (σ : Equiv.Perm ι)
    (hfix : Fintype.card {i : ι // σ i = i} = 18) : σ.IsSwap := by
  have hc : σ.support.card = 2 := by
    have h := Fintype.card_subtype_compl (fun i => σ i = i)
    rw [hcard, hfix] at h
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using h
  exact Equiv.Perm.card_support_eq_two.mp hc

lemma cycle_of_pow_eq_one_card_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 20) (σ : Equiv.Perm ι)
    (hpow : σ ^ 19 = 1) (hfix : Fintype.card {i : ι // σ i = i} = 1) :
    σ.IsCycle ∧ σ.support.card = 19 := by
  have hc : σ.support.card = 19 := by
    have h := Fintype.card_subtype_compl (fun i => σ i = i)
    rw [hcard, hfix] at h
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using h
  have hne : σ ≠ 1 := by intro h; simp [h] at hc
  have hord : orderOf σ = 19 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    have hp : Nat.Prime 19 := by decide
    exact (hp.eq_one_or_self_of_dvd _ hd).resolve_left (by simpa using hne)
  exact ⟨Equiv.Perm.isCycle_of_prime_order (by rw [hord]; decide) (by rw [hc, hord]; omega), hc⟩

end DimensionTen

end
end

end OAI
