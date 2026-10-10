import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaProduct

namespace OAI

/-! An explicit finite-prime avoidance step for the level-nine Kubota
multiplication proof. No prime-distribution theorem is required. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open UniqueFactorizationMonoid
namespace CubicFirstMoment

/-- Choose the shear by multiplying exactly the prime factors of f which
do not divide a. This preserves all good residues and repairs the others. -/
theorem cubicTheta_exists_coprime_shear {a c f : Eisenstein}
    (hf : f ≠ 0) (hac : IsCoprime a (9*c)) :
    ∃ t : Eisenstein, (9:Eisenstein) ∣ t ∧ IsCoprime (a+t*c) f := by
  let m := ((normalizedFactors f).filter (fun p => ¬p ∣ a)).prod
  refine ⟨9*m,⟨m,rfl⟩,?_⟩
  apply IsCoprime.symm
  apply isCoprime_of_prime_dvd (fun h => hf h.1)
  intro p hp hpf hpsum
  by_cases hpa : p ∣ a
  · have hnot : ¬p ∣ 9*c := by
      intro hd
      exact hp.not_isUnit (hac.isRelPrime hpa hd)
    have hnm : ¬p ∣ m := by
      intro hpm
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd hpm
      obtain ⟨hqf,hqa⟩ := Multiset.mem_filter.mp hq
      have hqprime := prime_of_normalized_factor q hqf
      have hassoc := hp.irreducible.associated_of_dvd hqprime.irreducible hpq
      exact hqa (dvd_trans hassoc.symm.dvd hpa)
    have hd : p ∣ (9*c)*m := by
      have h := dvd_sub hpsum hpa
      convert h using 1
      simp only [add_sub_cancel_left, mul_assoc, mul_comm]
    rcases hp.dvd_mul.mp hd with h | h
    · exact hnot h
    · exact hnm h
  · obtain ⟨q,hqf,hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hp.irreducible hpf
    have hqa : ¬q ∣ a := by
      intro hqa
      exact hpa (dvd_trans hassoc.dvd hqa)
    have hqm : q ∣ m := Multiset.dvd_prod (Multiset.mem_filter.mpr ⟨hqf,hqa⟩)
    have hpm : p ∣ m := dvd_trans hassoc.dvd hqm
    have hpadd : p ∣ (9*m)*c := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpm 9) c
    have h := dvd_sub hpsum hpadd
    apply hpa
    simpa only [add_sub_cancel_right] using h

end CubicFirstMoment

end

end OAI
