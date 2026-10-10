import OAI.Analysis.Laughlin.Operators.GramReadout
import OAI.Analysis.Laughlin.ThreeBody.GramSlice

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairCoefficient_endpoint_zero (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) :
    pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ =
      (z : ℝ)/Real.sqrt 2 * Real.sqrt ((Q.choose z : ℝ)/
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) := by
  rw [pairCoefficient_choose Q (z-1) (by omega) (by omega)]
  rw [ite_eq_left (show z+0=z-1+1 by omega)]
  simp only [Nat.cast_zero,sub_zero,
    Nat.choose_zero_right,Nat.cast_one,mul_one]
  rw [show (Q.choose z : ℝ)/(2*(Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) =
    ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)))/2 by ring]
  rw [Real.sqrt_div (by positivity)]
  ring

theorem pairCoefficient_endpoint_one (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ =
      ((z : ℝ)-1)/Real.sqrt 2 *
        Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) := by
  rw [pairCoefficient_choose Q z (by omega) (by omega)]
  simp only [ite_true,Nat.choose_one_right,Nat.cast_one]
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hr : (Q.choose z : ℝ)*Q/(2*(Q : ℝ)*((2*Q-2).choose z : ℝ)) =
      ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ))/2 := by field_simp
  rw [hr,Real.sqrt_div (by positivity)]
  ring

theorem swap_slice_first_row (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) (f : Fin (z+1) → ℝ) :
    (∑ q : Fin (z+1), (∑ t : Fin (Q+1),
      pairCoefficient Q 0 (sliceOrbital Q z hz q) t *
        pairCoefficient Q q.val ⟨z,by omega⟩ t)*f q) =
      (-pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ /Real.sqrt 2)*f ⟨z,by omega⟩ +
      (pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ /Real.sqrt 2)*f ⟨z-1,by omega⟩ := by
  let last : Fin (z+1) := ⟨z,by omega⟩
  let prev : Fin (z+1) := ⟨z-1,by omega⟩
  have hne : last ≠ prev := by intro h; have := congrArg Fin.val h; dsimp [last,prev] at this; omega
  have he (q : Fin (z+1)) :
      (∑ t : Fin (Q+1), pairCoefficient Q 0 (sliceOrbital Q z hz q) t *
        pairCoefficient Q q.val ⟨z,by omega⟩ t) =
        (if q=last then -pairCoefficient Q z ⟨z,by omega⟩ ⟨1,by omega⟩ /Real.sqrt 2 else 0) +
        (if q=prev then pairCoefficient Q (z-1) ⟨z,by omega⟩ ⟨0,by omega⟩ /Real.sqrt 2 else 0) := by
    rw [swap_base_row Q q.val hQ]
    by_cases hl : q=last
    · subst q
      simp [last,prev,sliceOrbital,show z ≠ z-1 by omega]
    · by_cases hp : q=prev
      · subst q
        simp [last,prev,sliceOrbital,show z-(z-1)=1 by omega,show z-1 ≠ z by omega]
      · have hlv : q.val ≠ z := by intro h; apply hl; exact Fin.ext h
        have hpv : q.val ≠ z-1 := by intro h; apply hp; exact Fin.ext h
        have hzero : z-q.val ≠ 0 := by omega
        have hone : z-q.val ≠ 1 := by omega
        simp [hl,hp,sliceOrbital,hzero,hone]
  simp_rw [he,add_mul,ite_mul,zero_mul]
  rw [Finset.sum_add_distrib]
  simp [last,prev]

theorem threeBodyGramSlice_first_row_pos (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hz₀ : 1 ≤ z) (f : Fin (z+1) → ℝ) :
    (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q*f q) =
      f ⟨0,by omega⟩ - f ⟨z-1,by omega⟩ * (z : ℝ) *
        Real.sqrt ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) +
      f ⟨z,by omega⟩*((z : ℝ)-1)*
        Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) := by
  simp only [threeBodyGramSlice,sub_mul,mul_assoc]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  have horb : sliceOrbital Q z hz ⟨0,by omega⟩ = ⟨z,by omega⟩ := by rfl
  rw [horb,swap_slice_first_row Q z hQ hz hz₀ f]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [pairCoefficient_endpoint_zero Q z hQ hz hz₀,pairCoefficient_endpoint_one Q z hQ hz]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp
  rw [hsq]
  ring

end Laughlin.Fock

end OAI
