import OAI.NumberTheory.Ostmann.HybridSieve.ShiftedGauss

namespace OAI

namespace Ostmann.HybridSieve
open LargePrimeGaps
open scoped Classical

theorem shifted_multiplicative_large_sieve (A Q N : ℕ) (a : Fin N→ℂ) :
    (∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
      (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ => χ.IsPrimitive),
        ‖shiftedCharacterSum A a χ‖^2))≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  classical
  by_cases hQ : Q=0
  · subst Q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_pow (by decide : 2≠0),
      zero_mul,add_zero]
    positivity
  have hQpos : 0<Q := Nat.pos_of_ne_zero hQ
  let s : Finset ℚ := Finset.univ.image (fareyFrequency (Q:=Q))
  have hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q := by
    intro r hr
    obtain ⟨⟨q,u⟩,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(unitFrequency_bounds u).1,(unitFrequency_bounds u).2,by
      rw [fareyFrequency,unitFrequency_den]
      omega⟩
  calc
    _ ≤ ∑ q:Fin Q,∑ u:(ZMod (q.val+1))ˣ,‖shiftedFourierSum A (q:=q.val+1) a (u:ZMod (q.val+1))‖^2 :=
      Finset.sum_le_sum (fun _ _ => shifted_primitive_energy_le A a)
    _ = ∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2 := by
      dsimp only [s]
      rw [Finset.sum_image (fareyFrequency_injective Q).injOn,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro u _
      rw [norm_shiftedFourierSum, modularFourierSum_eq_bvExp]
      rfl
    _ ≤ _ := rational_additive_large_sieve s hQpos hs N a

end Ostmann.HybridSieve

end OAI
