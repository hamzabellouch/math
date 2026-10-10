import Mathlib

namespace OAI


                                             
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem principal_of_principal_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (hm : (maximalIdeal R).IsPrincipal) : IsPrincipalIdealRing R := by
  classical
  obtain ⟨t,ht⟩ := hm
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    infer_instance
  have hex : ∃ n : ℕ, ¬ I ≤ maximalIdeal R ^ (n+1) := by
    by_contra! H
    apply hI
    apply le_antisymm
    · rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top]
      apply le_iInf
      rintro (_ | n)
      · simp
      · exact H n
    · exact bot_le
  let n := Nat.find hex
  have hle : I ≤ maximalIdeal R ^ n := by
    cases hn : n with
    | zero => simp
    | succ j =>
      have hj : j < Nat.find hex := by change j < n; omega
      exact not_not.mp (Nat.find_min hex hj)
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp (Nat.find_spec hex)
  have hat : t^n ∣ a := by
    have H := hle ha
    rw [ht,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at H
    exact H
  obtain ⟨b,hb⟩ := hat
  have hbu : IsUnit b := by
    by_contra h
    have hbmem : b ∈ maximalIdeal R := h
    apply han
    change a ∉ maximalIdeal R ^ (n+1) at han
    have htn : t^n ∈ maximalIdeal R^n := by
      exact Ideal.pow_mem_pow (by rw [ht]; exact Ideal.subset_span (by simp)) n
    rw [hb]
    exact Ideal.mul_mem_mul htn hbmem
  have he : I = maximalIdeal R^n := by
    apply le_antisymm hle
    rw [ht,Ideal.span_singleton_pow,Ideal.span_le,Set.singleton_subset_iff]
    obtain ⟨u,hu⟩ := hbu
    have H := I.mul_mem_left (↑(u⁻¹) : R) ha
    rw [hb,← hu] at H
    simpa [mul_left_comm,mul_comm,mul_assoc] using H
  rw [he,ht,Ideal.span_singleton_pow]
  infer_instance

end
end MaximalSeshadri.LocalCurve

end



end OAI
