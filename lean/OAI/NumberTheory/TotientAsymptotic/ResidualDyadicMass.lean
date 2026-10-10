import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicHarmonic

namespace OAI

/-! Local residual counts integrate against their actual reciprocal totients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem residual_dyadic_mass (R : Finset ℕ) (d L : ℕ) {A : ℝ}
    (hA : 0 ≤ A)
    (hrange : ∀ r ∈ R,1 < d*r.totient ∧ ((d*r.totient:ℕ):ℝ) ≤ (2:ℝ)^L)
    (hcount : ∀ k ∈ Finset.Icc 1 L,
      ((R.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤ A*(2:ℝ)^k/k) :
    (∑ r ∈ R,(r.totient:ℝ)⁻¹) ≤ 4*d*A*(1+Real.log L) := by
  classical
  have hn : ∀ r ∈ R,Nat.clog 2 (d*r.totient) ∈ Finset.Icc 1 L := by
    intro r hr
    refine Finset.mem_Icc.mpr ⟨(dyadic_nat_bounds (hrange r hr).1).1,?_⟩
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    exact_mod_cast (hrange r hr).2
  have hlo : ∀ r ∈ R,(2:ℝ)^(Nat.clog 2 (d*r.totient))/4 ≤ ((d*r.totient:ℕ):ℝ) := by
    intro r hr
    have hh := (dyadic_nat_bounds (hrange r hr).1).2.1
    have hp : 0 < (2:ℝ)^(Nat.clog 2 (d*r.totient)) := by positivity
    linarith only [hh,hp]
  have hm := finite_dyadic_harmonic_mass R (fun r => Nat.clog 2 (d*r.totient))
    (fun r => ((d*r.totient:ℕ):ℝ)) L hA hn hlo hcount
  have he : (∑ r ∈ R,(r.totient:ℝ)⁻¹) =
      (d:ℝ)*(∑ r ∈ R,(((d*r.totient:ℕ):ℝ))⁻¹) := by
    by_cases hR : R.Nonempty
    · obtain ⟨r,hr⟩ := hR
      have hd : d≠0 := by intro h; simpa [h] using (hrange r hr).1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Nat.cast_mul,mul_inv]
      field_simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR]
      simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg d)
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
