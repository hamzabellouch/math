import OAI.NumberTheory.Jacobsthal.Partitions.EffectiveCoordinateUnits

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells

noncomputable def effectiveInteger (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (j : ℤ) : ℤ :=
  (cofactorHit qf a : ℤ)+(qf : ℤ)*
    ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℤ)+(p : ℤ)*j)

theorem effectiveInteger_nat_coordinate (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (j : ℕ) :
    ((effectiveBase a r qf p hHp+p*qf*j : ℕ) : ℤ) = effectiveInteger a r qf p hHp (j : ℤ) := by
  simp only [effectiveBase,effectiveInteger,Nat.cast_add,Nat.cast_mul]
  ring

theorem effective_avoidance_not_dvd (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p)
    (t : ℕ) (ht : t.Prime) (htH : ¬t ∣ effectiveModulus a r qf) (j : ℤ) :
    (effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
      (p : ZMod t)*(alignedCofactor (fun u => (a u : ℤ)) r qf : ZMod t)*
        ((intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
          (effectiveModulus a r qf : ZMod t)*(j : ZMod t)) ≠
        (r.den : ZMod t)*(a t : ZMod t)-(r.num : ZMod t) := by
  let : Fact t.Prime := ⟨ht⟩
  have hDH := effective_den_coprime_prime a r qf t (ht.coprime_iff_not_dvd.mpr htH).symm
  have hD0 : (r.den : ZMod t) ≠ 0 := by
    intro he
    exact (ht.coprime_iff_not_dvd.mp hDH.symm) ((ZMod.natCast_eq_zero_iff _ _).mp he)
  have hid : (r.den : ZMod t)*(effectiveInteger a r qf p hHp j : ZMod t) =
      (r.num : ZMod t)+(p : ZMod t)*(alignedCofactor (fun u => (a u : ℤ)) r qf : ZMod t)*
        ((intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
          (effectiveModulus a r qf : ZMod t)*(j : ZMod t)) := by
    have he := congrArg (fun z : ℤ => (z : ZMod t)) (effective_progression_identity a r qf hq p hHp j)
    simpa only [effectiveInteger,Int.cast_add,Int.cast_mul,Int.cast_natCast,mul_comm (p : ZMod t)] using he
  apply not_congr
  constructor
  · intro he
    rw [he] at hid
    linear_combination -hid
  · intro he
    apply mul_left_cancel₀ hD0
    linear_combination hid+he

theorem effective_avoidance_unit (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hHp : (effectiveModulus a r qf).Coprime p) (t : ℕ) (hqt : qf.Coprime t) (j : ℤ) :
    (effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ℕ) : ZMod t)+
        (p : ZMod t)*(j : ZMod t) ≠
        ((a t : ZMod t)-(cofactorHit qf a : ZMod t))*(↑((ZMod.unitOfCoprime qf hqt)⁻¹) : ZMod t) := by
  let v := ZMod.unitOfCoprime qf hqt
  have hu : (qf : ZMod t)*(↑(v⁻¹) : ZMod t) = 1 := by
    simpa only [v,ZMod.coe_unitOfCoprime] using v.mul_inv
  simp only [effectiveInteger,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  apply not_congr
  constructor
  · intro he
    have hh := congrArg (fun x : ZMod t => x*(↑(v⁻¹) : ZMod t)) he
    linear_combination hh-
      ((intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+(p : ZMod t)*(j : ZMod t))*hu
  · intro he
    have hh := congrArg (fun x : ZMod t => (qf : ZMod t)*x) he
    linear_combination hh+((a t : ZMod t)-(cofactorHit qf a : ZMod t))*hu

end ErdosVarianceEffective

end

end Erdos970

end OAI
