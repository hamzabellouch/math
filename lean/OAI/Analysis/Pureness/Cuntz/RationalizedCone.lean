import OAI.Analysis.Pureness.Cuntz.RationalizedGroup
import OAI.Analysis.Pureness.Cuntz.RationalConeStates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI
noncomputable section
namespace CuntzPureness.OrderedSemigroup
variable {G : Type*} [AddCommGroup G]

lemma rational_nat_mul (q : ℚ) (hq : 0 ≤ q) :
    (q.den : ℚ) * q = (q.num.toNat : ℚ) := by
  have hp : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  calc
    (q.den : ℚ) * q = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
      congrArg (fun t : ℚ => (q.den : ℚ)*t) (Rat.num_div_den q).symm
    _ = (q.num : ℚ) := mul_div_cancel₀ _ hd
    _ = (q.num.toNat : ℚ) := by exact_mod_cast hp.symm

def rationalCone (P : AddSubmonoid G) : PointedCone ℚ (RationalGroup G) where
  carrier := {z | ∃ n : ℕ, 0 < n ∧ ∃ g ∈ P, n • z = toRationalGroup G g}
  zero_mem' := ⟨1,by omega,0,P.zero_mem,by simp⟩
  add_mem' := by
    rintro z w ⟨n,hn,g,hg,hzg⟩ ⟨m,hm,h,hh,hwh⟩
    refine ⟨m*n,Nat.mul_pos hm hn,m • g+n • h,P.add_mem (P.nsmul_mem hg m) (P.nsmul_mem hh n),?_⟩
    calc
      (m*n) • (z+w) = m • (n • z) + n • (m • w) := by
        simp only [nsmul_add, ← mul_nsmul, Nat.mul_comm]
      _ = toRationalGroup G (m • g+n • h) := by rw [hzg,hwh,map_add,map_nsmul,map_nsmul]
  smul_mem' := by
    rintro ⟨q,hq⟩ z ⟨n,hn,g,hg,hzg⟩
    refine ⟨q.den*n,Nat.mul_pos q.den_pos hn,q.num.toNat • g,P.nsmul_mem hg _,?_⟩
    change (q.den*n) • (q • z) = _
    calc
      (q.den*n) • (q • z) = q.num.toNat • (n • z) := by
        simp only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_mul, smul_smul]
        congr 1
        rw [mul_right_comm, rational_nat_mul q hq]
      _ = toRationalGroup G (q.num.toNat • g) := by rw [hzg,map_nsmul]

lemma rationalCone_of_mem (P : AddSubmonoid G) {g : G} (hg : g ∈ P) :
    toRationalGroup G g ∈ rationalCone P := ⟨1,by omega,g,hg,by simp⟩

theorem rationalCone_of_iff (P : AddSubmonoid G) (g : G) :
    toRationalGroup G g ∈ rationalCone P ↔ ∃ n : ℕ, 0 < n ∧ n • g ∈ P := by
  constructor
  · rintro ⟨n,hn,h,hh,he⟩
    rw [← map_nsmul] at he
    obtain ⟨k,hk,hkgh⟩ := (rationalGroup_eq_iff G (n • g) h).mp he
    refine ⟨k*n,Nat.mul_pos hk hn,?_⟩
    rw [Nat.mul_comm k n, mul_nsmul, hkgh]
    exact P.nsmul_mem hh k
  · rintro ⟨n,hn,hg⟩
    exact ⟨n,hn,n • g,hg,(map_nsmul _ n g).symm⟩

theorem rationalCone_orderUnit (P : AddSubmonoid G) (u : G)
    (hbound : ∀ g : G, ∃ n : ℕ, n • u + g ∈ P)
    (z : RationalGroup G) :
    ∃ r : ℚ, r • toRationalGroup G u + z ∈ rationalCone P := by
  obtain ⟨d,hd,g,hg⟩ := rationalGroup_denominator G z
  obtain ⟨n,hn⟩ := hbound g
  refine ⟨(n : ℚ)/d,d,hd,n • u+g,hn,?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    d • (((n : ℚ)/(d : ℚ)) • toRationalGroup G u + z) =
        n • toRationalGroup G u + toRationalGroup G g := by
      rw [← Nat.cast_smul_eq_nsmul ℚ d, smul_add, smul_smul, hg]
      rw [mul_div_cancel₀ _ hd0, Nat.cast_smul_eq_nsmul]
    _ = toRationalGroup G (n • u+g) := by rw [map_add,map_nsmul]
end CuntzPureness.OrderedSemigroup

end

end OAI
