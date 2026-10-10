import OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueFibers

namespace OAI

/-! The congruence-counting factor in the complete-system iteration.
The jth polynomial sum is fixed only modulo p^min(j,r), and the unused
digits are counted before applying the nonsingular full-modulus bound. -/
namespace TwoPointCorrelations

open Finset Polynomial

theorem halasz_mixed_congruence_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (F : Finset (Fin k → ZMod (p^(r+1)))) (b : Fin k → ℕ)
    (hnonsing : ∀ x∈F, Function.Injective
      (fun i => halaszPrimePowerReduction p r (x i)))
    (hmod : ∀ x∈F, ∀ j,
      (∑ i, (P j).eval (x i)).val % (p^(min (j.val+1) (r+1))) = b j) :
    F.card ≤ k^k * ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)) := by
  classical
  let T : (Fin k → ZMod (p^(r+1))) → (Fin k → ZMod (p^(r+1))) :=
    fun x j => ∑ i, (P j).eval (x i)
  let S := F.image T
  let R : Fin k → Finset (ZMod (p^(r+1))) := fun j => F.image (fun x => T x j)
  have hR (j : Fin k) : (R j).card ≤ p^(r+1-min (j.val+1) (r+1)) := by
    apply halasz_prime_power_residue_card (Nat.min_le_right _ _) (R j)
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact hmod x hx j
  have hS : S ⊆ Fintype.piFinset R := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_image.mpr ⟨x,hx,rfl⟩
  have hcardS : S.card ≤ ∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)) := by
    calc
      S.card ≤ (Fintype.piFinset R).card := card_le_card hS
      _ = ∏ j, (R j).card := Fintype.card_piFinset R
      _ ≤ _ := prod_le_prod (fun j _ => hR j)
  have hfiber (t : Fin k → ZMod (p^(r+1))) :
      (F.filter (fun y => T y=t)).card ≤ k^k := by
    let B := F.filter (fun y => T y=t)
    change B.card ≤ k^k
    by_cases hB : B.Nonempty
    · obtain ⟨w,hw⟩ := hB
      apply halasz_prime_power_polynomial_count hkp P hdeg hunit w
        (hnonsing w (mem_filter.mp hw).1) B
      intro y hy j
      have he : T w=T y := (mem_filter.mp hw).2.trans (mem_filter.mp hy).2.symm
      exact congrFun he j
    · simp only [not_nonempty_iff_eq_empty.mp hB,card_empty]
      exact Nat.zero_le _
  calc
    F.card = ∑ t∈S, (F.filter (fun y => T y=t)).card := card_eq_sum_card_image T F
    _ ≤ ∑ _t∈S, k^k := sum_le_sum (fun t _ => hfiber t)
    _ = S.card*k^k := by simp
    _ ≤ (∏ j : Fin k, p^(r+1-min (j.val+1) (r+1)))*k^k :=
      Nat.mul_le_mul_right _ hcardS
    _ = _ := Nat.mul_comm _ _

end TwoPointCorrelations

end OAI
