import OAI.NumberTheory.Jacobsthal.Probability.StableFiniteVariance

namespace OAI

namespace Erdos970


namespace ErdosRandomVariance

theorem weighted_chebyshev {α : Type*} (C : Finset α) (w f : α → ℝ)
    (M a B : ℝ) (hw : ∀ x ∈ C, 0 ≤ w x) (ha : 0 < a)
    (hBound : weightedMoment C w (fun x => (f x-M)^2) ≤ B) :
    (∑ x ∈ C with a ≤ |f x-M|, w x) ≤ B/a^2 := by
  classical
  have hlocal (x : α) (hx : x ∈ C.filter (fun x => a ≤ |f x-M|)) :
      a^2*w x ≤ w x*(f x-M)^2 := by
    obtain ⟨hxC,hxE⟩ := Finset.mem_filter.mp hx
    have hsq : a^2 ≤ (f x-M)^2 := by
      nlinarith [sq_abs (f x-M),abs_nonneg (f x-M)]
    nlinarith [mul_le_mul_of_nonneg_right hsq (hw x hxC)]
  have hs : a^2*(∑ x ∈ C with a ≤ |f x-M|, w x) ≤ B := by
    calc
      _ = ∑ x ∈ C with a ≤ |f x-M|, a^2*w x := Finset.mul_sum ..
      _ ≤ ∑ x ∈ C with a ≤ |f x-M|, w x*(f x-M)^2 := Finset.sum_le_sum hlocal
      _ ≤ ∑ x ∈ C, w x*(f x-M)^2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x hx _ => mul_nonneg (hw x hx) (sq_nonneg _))
      _ ≤ B := hBound
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith [hs]

theorem weighted_relative_chebyshev {α : Type*} (C : Finset α) (w f : α → ℝ)
    (M eta beta : ℝ) (hw : ∀ x ∈ C, 0 ≤ w x) (hM : 0 < M) (heta : 0 < eta)
    (hBound : weightedMoment C w (fun x => (f x-M)^2) ≤ beta*M^2) :
    (∑ x ∈ C with eta*M ≤ |f x-M|, w x) ≤ beta/eta^2 := by
  classical
  have h := weighted_chebyshev C w f M (eta*M) (beta*M^2) hw (mul_pos heta hM) hBound
  have he : beta*M^2/(eta*M)^2 = beta/eta^2 := by
    field_simp [hM.ne',heta.ne']
  rwa [he] at h

end ErdosRandomVariance


end Erdos970

end OAI
