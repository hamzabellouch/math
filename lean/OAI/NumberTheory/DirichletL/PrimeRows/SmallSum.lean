import OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma small_dyadic_square_sum : ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
    (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^(2:ℝ))≤C*H^(2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound 2 3 (by norm_num) (by norm_num)
  refine ⟨8*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^(2:ℝ)≤8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^3≤(2:ℝ)^3 := pow_le_pow_left₀ hd.le (by linarith) 3
    unfold CompletedDyadic.kernelTerm
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd 3)).mpr
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ((2:ℝ)^n))
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ ∑n∈F,8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := Finset.sum_le_sum hpoint
    _ = 8*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ 2 3 n := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*∑'n,CompletedDyadic.kernelTerm H⁻¹ 2 3 n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by norm_num)
    _ ≤ 8*(C*(H⁻¹)^(-2:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
