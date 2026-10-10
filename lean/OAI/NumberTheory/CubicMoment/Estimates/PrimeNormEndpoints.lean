import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormFibers

namespace OAI

/-! Endpoint and largest-prime tie corrections. At most two primary
primes have a prescribed norm, so endpoint choices cost an absolute
constant in a bounded prime sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnr : (normNat p:ℝ) = normNat q := by simpa only [normNat_cast] using hn
  have hn' : normNat p = normNat q := by exact_mod_cast hnr
  have heq : p*conjugate p = q*conjugate q := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn']
  have hd : p ∣ q*conjugate q := heq ▸ dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1
      ((hp.2.dvd_prime_iff_associated hq.2).mp hd))
  · exact Or.inr (primary_associated_eq hp.1 (primaryPrime_conjugate hq).1
      ((hp.2.dvd_prime_iff_associated (primaryPrime_conjugate hq).2).mp hd))

theorem primaryPrime_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (x : ℝ) :
    (S.filter (fun p => norm p = x)).card ≤ 2 := by
  let T := S.filter (fun p => norm p = x)
  by_cases hT : T.Nonempty
  · obtain ⟨q,hq⟩ := hT
    have hsub : T ⊆ {q,conjugate q} := by
      intro p hp
      have he := primaryPrime_eq_or_conjugate_of_norm_eq
        (hS p (Finset.mem_filter.mp hp).1) (hS q (Finset.mem_filter.mp hq).1)
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he
    apply (Finset.card_le_card hsub).trans
    calc
      ({q,conjugate q}:Finset Eisenstein).card ≤ ({conjugate q}:Finset Eisenstein).card+1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  · change T.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    norm_num

lemma primaryPrime_two_norm_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a b : ℝ) :
    (S.filter (fun p => norm p = a ∨ norm p = b)).card ≤ 4 := by
  have he : S.filter (fun p => norm p = a ∨ norm p = b) =
      S.filter (fun p => norm p = a) ∪ S.filter (fun p => norm p = b) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [he]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add (primaryPrime_norm_fiber_card S hS a)
      (primaryPrime_norm_fiber_card S hS b)).trans (by norm_num))

/-- This also covers an arbitrary fixed-order selection among equal-norm
largest primes. Away from the two boundary norms the predicates agree. -/
theorem prime_interval_endpoint_difference (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (P Q : Eisenstein → Prop) (a b : ℝ)
    (hPQ : ∀ p ∈ S, norm p ≠ a → norm p ≠ b → (P p ↔ Q p))
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S with P p, w p)-(∑ p ∈ S with Q p, w p)‖ ≤ 4*M := by
  let T := S.filter (fun p => norm p = a ∨ norm p = b)
  let f := fun p => (if P p then w p else 0)-(if Q p then w p else 0)
  have he : (∑ p ∈ S, f p) = ∑ p ∈ T, f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : norm p ≠ a ∧ norm p ≠ b := by
      simpa only [T,Finset.mem_filter,hp,true_and,not_or] using hnot
    have he := hPQ p hp hn.1 hn.2
    by_cases h : P p
    · simp [f,h,he.mp h]
    · have hq : ¬Q p := fun hq => h (he.mpr hq)
      simp [f,h,hq]
  have hf (p : Eisenstein) (hp : p ∈ T) : ‖f p‖ ≤ M := by
    have hpS := (Finset.mem_filter.mp hp).1
    by_cases hP : P p <;> by_cases hQ : Q p <;>
      simp [f,hP,hQ,hM,hw p hpS]
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  change ‖∑ p ∈ S, f p‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, M := Finset.sum_le_sum hf
    _ = (T.card:ℝ)*M := by simp
    _ ≤ 4*M := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primaryPrime_two_norm_card S hS a b)) hM

end CubicFirstMoment

end

end OAI
