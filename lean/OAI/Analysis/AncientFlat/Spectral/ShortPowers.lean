import Mathlib

namespace OAI
noncomputable section
namespace ParabolicShort
lemma short_scale_bound (j : ℕ) (hj : j≤3) (h M α : ℝ)
    (hh : 0<h) (hM : 0≤M) (hα : α<1) :
    let q := h^((1:ℝ)/4)/24
    110*(h*M/q^j+q^(4-j)*M)/q^α ≤
      (110*(24^4+1))*h^((4-(j:ℝ)-α)/4)*M := by
  dsimp only
  let d := h^((1:ℝ)/4)
  let q := d/24
  have hd : 0<d := Real.rpow_pos_of_pos hh _
  have hq : 0<q := by dsimp [q]; positivity
  have hd4 : d^4=h := by
    dsimp [d]
    rw [←Real.rpow_mul_natCast hh.le ((1:ℝ)/4) 4]
    norm_num
  have he : h=24^4*q^4 := by dsimp [q]; rw [div_pow,←hd4]; ring
  have hp : q^4/q^j=q^(4-j) := by
    rw [show (4:ℕ)=(4-j)+j by omega,pow_add,mul_div_cancel_right₀ _ (pow_ne_zero _ hq.ne')]
    congr 1
    omega
  have hn : ((4-j:ℕ):ℝ)=4-(j:ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
  have hexp : 0≤(4-(j:ℝ)-α) := by
    have : (j:ℝ)≤3 := by exact_mod_cast hj
    linarith
  have hpow : q^(4-j)/q^α=q^(4-(j:ℝ)-α) := by
    rw [Real.rpow_sub hq,←hn,Real.rpow_natCast]
  have hqd : q≤d := by dsimp [q]; linarith
  have hdp : d^(4-(j:ℝ)-α)=h^((4-(j:ℝ)-α)/4) := by
    dsimp [d]
    rw [←Real.rpow_mul hh.le]
    congr 1
    ring
  change 110*(h*M/q^j+q^(4-j)*M)/q^α ≤ _
  calc
    _=(110*(24^4+1))*(q^(4-j)/q^α)*M := by rw [he]; rw [show 24^4*q^4*M/q^j=24^4*(q^4/q^j)*M by ring,hp]; ring
    _≤(110*(24^4+1))*d^(4-(j:ℝ)-α)*M := by rw [hpow]; gcongr
    _=_ := by rw [hdp]
end ParabolicShort

end

end OAI
