import OAI.Analysis.Triangular.Auxiliary.ExponentialTail

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope
open Complex

def expDeleted (w : ℂ) (m v : ℝ) : ℂ :=
  if v=0 then exp (w*(m:ℂ))*w^2/2
  else (exp (w*((m+v:ℝ):ℂ))-exp (w*(m:ℂ))-(v:ℂ)*w*exp (w*(m:ℂ)))/(v:ℂ)^2
def expDeletedTaylor (w : ℂ) (m v : ℝ) : ℂ :=
  exp (w*(m:ℂ))*w^2*∑ j ∈ Finset.range 21, (w*(v:ℂ))^j/((j+2).factorial:ℂ)
lemma exp_sum_split (z : ℂ) :
    (∑ i ∈ Finset.range 23, z^i/(i.factorial:ℂ)) =
      1+z+z^2*∑ j ∈ Finset.range 21, z^j/((j+2).factorial:ℂ) := by
  rw [show (23:ℕ)=2+21 by norm_num,Finset.sum_range_add]
  rw [show (∑ i ∈ Finset.range 2, z^i/(i.factorial:ℂ))=1+z by
    simp [Finset.sum_range_succ]]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Nat.add_comm 2 j]
  ring
lemma expDeleted_remainder_eq (w : ℂ) (m v : ℝ) (hv : v≠0) :
    expDeleted w m v-expDeletedTaylor w m v =
      exp (w*(m:ℂ))/(v:ℂ)^2 *
        (exp (w*(v:ℂ))-∑ i ∈ Finset.range 23, (w*(v:ℂ))^i/(i.factorial:ℂ)) := by
  have hv' : (v:ℂ)≠0 := by exact_mod_cast hv
  simp only [expDeleted,ite_eq_right hv,expDeletedTaylor,ofReal_add,mul_add,exp_add,exp_sum_split]
  field_simp
  ring
lemma expDeleted_zero (w : ℂ) (m : ℝ) : expDeleted w m 0=expDeletedTaylor w m 0 := by
  simp [expDeleted,expDeletedTaylor,Finset.sum_range_succ]
  ring
lemma expDeleted_error (w : ℂ) (m v Y : ℝ) (hY : 0≤Y) (hv : |v|≤Y)
    (hr : Y*‖w‖/24<1) :
    ‖expDeleted w m v-expDeletedTaylor w m v‖ ≤
      ‖exp (w*(m:ℂ))‖*‖w‖^2*(Y*‖w‖)^21/(23).factorial/(1-Y*‖w‖/24) := by
  by_cases hv0 : v=0
  · subst v
    rw [expDeleted_zero,sub_self,norm_zero]
    positivity
  have hp : 0<1-Y*‖w‖/24 := sub_pos.mpr hr
  have hcoef : 0≤Y*‖w‖/24 := by positivity
  have hnorm : ‖w*(v:ℂ)‖≤(Y*‖w‖/24)*((23:ℝ)+1) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg w)]
  have hb := complex_exp_tail_bound (w*(v:ℂ)) 23 hcoef hr hnorm
  rw [expDeleted_remainder_eq w m v hv0,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hpos : 0 < |v| ^ 2 := sq_pos_of_pos (abs_pos.mpr hv0)
  calc
    _ ≤ (‖exp (w*(m:ℂ))‖/ |v|^2)*((‖w*(v:ℂ)‖^23/(23).factorial)/(1-Y*‖w‖/24)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖exp (w*(m:ℂ))‖*‖w‖^2*(|v| * ‖w‖)^21/(23).factorial/(1-Y*‖w‖/24) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hv (norm_nonneg w)) 21
end AtomicTriangular.Envelope
end

end OAI
