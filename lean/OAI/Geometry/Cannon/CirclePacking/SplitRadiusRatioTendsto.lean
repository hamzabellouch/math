import Mathlib
import OAI.Geometry.Cannon.Flows.DyadicBin

namespace OAI

section
section
section
noncomputable section
section
section
namespace CannonPairs

open Filter Topology CannonNode

lemma split_radius_ratio_tendsto (Q n k : ℕ) (hQ : 0 < Q) (hn : 0 < n)
    {ell : ℝ} (hell : 0 < ell) :
    Tendsto (fun g : ℕ => radius ell (k+160*(Q+1)*n*g) /
      radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1))))) atTop (𝓝 0) := by
  have ht := (radius_tendsto hell).comp
    (depth_difference_tendsto (pair_split_ratio Q hQ) (by positivity : 0 < 160*(Q+1)*n) k)
  convert ht using 1
  funext g
  have hm : 160*(Q+1)*n*(g/(160*Q*(Q+1))) ≤ k+160*(Q+1)*n*g :=
    (Nat.mul_le_mul_left _ (Nat.div_le_self _ _)).trans (Nat.le_add_left _ _)
  simp only [Function.comp_def,radius,← Real.exp_sub,Nat.cast_sub hm]
  congr 1
  ring

lemma eventually_near_class_threshold {q : ℕ} (hq : 0 < q)
    {ell : ℝ} (hell : 0 < ell) (n : ℕ) (hn : 0 < n)
    (N K J k D : ℝ) (hK : 0 < K) (hJ : 0 ≤ J) (hk : 0 ≤ k) (hD : 0 ≤ D) :
    ∀ᶠ g : ℕ in atTop, 2*N*Real.exp (-ell*n)^(g/q) ≤
      1/(K*(J*(k+D*g)+1)) := by
  have hc : 0 < ell*n := mul_pos hell (Nat.cast_pos.mpr hn)
  have ht := (division_exp_tail hq hc (J*k+1) (J*D) (by positivity) (by positivity)).const_mul (2*N*K)
  have ht' : Tendsto (fun g : ℕ => (2*N*Real.exp (-ell*n)^(g/q))*(K*(J*(k+D*g)+1)))
      atTop (𝓝 0) := by
    convert ht using 1 <;> try simp only [mul_zero]
    funext g
    rw [neg_mul]
    ring
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with g hg
  exact (le_div_iff₀ (mul_pos hK (by positivity : 0 < J*(k+D*g)+1))).mpr hg

lemma radius_inverse_pow (ell : ℝ) (k Q : ℕ) :
    (radius ell k)⁻¹^Q = Real.exp ((Q:ℝ)*ell*k) := by
  rw [radius,← Real.exp_neg,← Real.exp_nat_mul]
  congr 1
  ring

theorem pair_cost_exponential_bound (Q n g : ℕ) (hQ : 0 < Q)
    {ell c lam CP Cs H mass k : ℝ} (hell : 0 ≤ ell)
    (hc : 0 < c) (hlam : 0 < lam) (hCP : 0 ≤ CP) (hCs : 0 ≤ Cs)
    (hH : 0 < H) (hmass : 0 ≤ mass) (M : ℕ)
    (hcost : (1/2:ℝ)*c*(lam*Real.exp (ell*n*g))^2 ≤
      (2*(CP*(Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q*M))*mass*k^2) :
    Real.exp ((ell*n)*g) ≤
      ((2*CP*(Cs/H)^Q*M*mass)/(c*lam^2/2))*k^2 := by
  let e := Real.exp (ell*n*g)
  have he : 0 < e := Real.exp_pos _
  have hover : (Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q ≤
      (Cs/H)^Q*e := by
    rw [div_eq_mul_inv,mul_pow,radius_inverse_pow]
    exact mul_le_mul_of_nonneg_left (pair_overlap_exponential hell Q n g hQ) (by positivity)
  have hh : (c*lam^2/2)*e^2 ≤ (2*CP*(Cs/H)^Q*M*mass)*e*k^2 := by
    calc _ = (1/2:ℝ)*c*(lam*e)^2 := by ring
         _ ≤ (2*(CP*(Cs/H/radius ell (160*(Q+1)*n*(g/(160*Q*(Q+1)))))^Q*M))*mass*k^2 := hcost
         _ ≤ (2*(CP*((Cs/H)^Q*e)*M))*mass*k^2 := by gcongr
         _ = _ := by ring
  have hh' : ((c*lam^2/2)*e)*e ≤ ((2*CP*(Cs/H)^Q*M*mass)*k^2)*e := by
    nlinarith only [hh]
  have hc' : 0 < c*lam^2/2 := div_pos (mul_pos hc (sq_pos_of_pos hlam)) (by norm_num)
  have hh'' := (mul_le_mul_iff_left₀ he).mp hh'
  calc _ = e := rfl
       _ ≤ ((2*CP*(Cs/H)^Q*M*mass)*k^2)/(c*lam^2/2) :=
         (le_div_iff₀ hc').mpr (by simpa only [mul_comm] using hh'')
       _ = _ := by ring

end CannonPairs

end

end
end
end
end
end

end OAI
