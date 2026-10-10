import OAI.NumberTheory.Jacobsthal.Partitions.ActualCoordinateBlocks
import OAI.NumberTheory.Jacobsthal.Partitions.EffectiveCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells ErdosInverseHits ErdosHypotheticalTag ErdosAlignedProgression

theorem effective_den_coprime_prime (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (hHp : (effectiveModulus a r qf).Coprime p) : r.den.Coprime p :=
  hHp.of_dvd_left (dvd_mul_right _ _)

theorem effective_initial_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    (r.den : ℤ)*((cofactorHit qf a : ℤ)+(qf : ℤ)*
      (intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)) =
      r.num+(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(p : ℤ)*
        intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) := by
  have hN := effectiveIntercept_identity a r qf hq
  unfold hitNumerator at hN
  have hD : (r.den : ℤ)*(qf : ℤ) =
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(effectiveModulus a r qf : ℤ) := by
    exact_mod_cast denominator_full_cofactor a r qf hq
  have hm := intervalM0_identity p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)
  linear_combination -hN+
    (intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)*hD-
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*hm

theorem effective_progression_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) (j : ℤ) :
    (r.den : ℤ)*((cofactorHit qf a : ℤ)+(qf : ℤ)*
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)+(p : ℤ)*j)) =
      r.num+(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(p : ℤ)*
        (intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)+
          (effectiveModulus a r qf : ℤ)*j) := by
  have hb := effective_initial_identity a r qf hq p hHp
  have hD : (r.den : ℤ)*(qf : ℤ) =
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(effectiveModulus a r qf : ℤ) := by
    exact_mod_cast denominator_full_cofactor a r qf hq
  linear_combination hb+(p : ℤ)*j*hD

theorem effective_initial_bounds (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p) :
    1 ≤ cofactorHit qf a+qf*intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) ∧
      cofactorHit qf a+qf*intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) ≤ p*qf := by
  have hb := cofactorHit_spec qf hq a
  have hk := intervalK_lt p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)
  constructor
  · omega
  · nlinarith [hb.2.1]

theorem effective_initial_hypothetical_hit (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hHp : (effectiveModulus a r qf).Coprime p) :
    Nat.ModEq p
      (cofactorHit qf a+qf*intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf))
      (hypotheticalClass a r p p) := by
  apply (aligned_prime_hit_iff (hypotheticalClass a r p) r p _ hp
    (hypothetical_aligns a r p hp (effective_den_coprime_prime a r qf p hHp))).mpr
  have he := effective_initial_identity a r qf hq p hHp
  simp only [Nat.cast_add,Nat.cast_mul]
  rw [he]
  change (r.num+(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*(p : ℤ)*
    intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf))%(p : ℤ) = r.num%(p : ℤ)
  simp [Int.add_emod,Int.mul_emod]

theorem effective_k_eq_parentSlope (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hqp : qf.Coprime p)
    (hHp : (effectiveModulus a r qf).Coprime p) :
    intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) =
      parentSlope p qf hqp (hypotheticalClass a r p p) (cofactorHit qf a) := by
  let : Fact p.Prime := ⟨hp⟩
  have hq0 : (qf : ZMod p) ≠ 0 := by
    intro he
    exact (hp.coprime_iff_not_dvd.mp hqp.symm) ((ZMod.natCast_eq_zero_iff _ _).mp he)
  have he := (effective_initial_hypothetical_hit a r qf hq p hp hHp).trans
    (parent_start_mod_p p qf hqp (hypotheticalClass a r p p) (cofactorHit qf a)).symm
  have heZ := (ZMod.natCast_eq_natCast_iff _ _ _).mpr he
  simp only [Nat.cast_add,Nat.cast_mul] at heZ
  have hkZ := mul_left_cancel₀ hq0 (add_left_cancel heZ)
  have hk := (ZMod.natCast_eq_natCast_iff _ _ _).mp hkZ
  change _%p = _%p at hk
  rw [Nat.mod_eq_of_lt (intervalK_lt p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf)),
    Nat.mod_eq_of_lt (parentSlope_lt p qf hqp (hypotheticalClass a r p p) (cofactorHit qf a))] at hk
  exact hk

end ErdosVarianceEffective

end

end Erdos970

end OAI
