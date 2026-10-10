import Mathlib

namespace OAI

noncomputable section

namespace KKVariableUltra

theorem dyadic_rank_trace (d m j : ℕ) (hd : 0<d) (hm : m≤j) :
    ((d*2^j:ℕ):ℂ)⁻¹*((d*2^(j-m):ℕ):ℂ)=(((2:ℝ)^m)⁻¹:ℝ) := by
  have hd0 : (d:ℂ)≠0 := Nat.cast_ne_zero.mpr hd.ne'
  have h2 : (2:ℂ)≠0 := by norm_num
  have hpow : (2:ℂ)^j=(2:ℂ)^m*(2:ℂ)^(j-m) := by
    rw [← pow_add,Nat.add_sub_of_le hm]
  push_cast
  rw [hpow]
  field_simp

end KKVariableUltra
end

end OAI
