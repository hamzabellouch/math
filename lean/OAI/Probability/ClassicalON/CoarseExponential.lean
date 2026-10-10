import OAI.Probability.ClassicalON.CoarseTail

namespace OAI

noncomputable section
open scoped Classical
namespace ClassicalON

theorem siteDistance_nonneg (x y : Site) : 0 ≤ siteDistance x y := Real.sqrt_nonneg _

theorem siteDistance_le_radius_twice (x y : Site) : siteDistance x y ≤ 2*(siteRadius x y:ℝ) := by
  have hi := siteRadius_nonneg x y
  have h1 : |(y.1:ℝ)-(x.1:ℝ)| ≤ (siteRadius x y:ℝ) := by
    exact_mod_cast (le_max_left |y.1-x.1| |y.2-x.2|)
  have h2 : |(y.2:ℝ)-(x.2:ℝ)| ≤ (siteRadius x y:ℝ) := by
    exact_mod_cast (le_max_right |y.1-x.1| |y.2-x.2|)
  have hr : (0:ℝ) ≤ siteRadius x y := by exact_mod_cast hi
  rw [abs_sub_comm] at h1 h2
  have hs1 := mul_self_le_mul_self (abs_nonneg _) h1
  have hs2 := mul_self_le_mul_self (abs_nonneg _) h2
  have hab1 := sq_abs ((x.1:ℝ)-(y.1:ℝ))
  have hab2 := sq_abs ((x.2:ℝ)-(y.2:ℝ))
  unfold siteDistance
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

theorem half_pow_exp (t : ℕ) : (1/2:ℝ)^t=Real.exp (-Real.log 2*(t:ℝ)) := by
  rw [mul_comm,Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

namespace LatticeGraph

theorem connection_exponential (β : ℝ) (hβ : 0 ≤ β) :
    ∃ m : ℝ,0 < m  ∧  ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0 ≤ b e  ∧  b e ≤ β) →
      ∀ x y : G.vertices,G.connectionProbability b x y ≤ 4*Real.exp (-m*siteDistance x.val y.val) := by
  obtain ⟨N,hN,ht⟩ := connection_geometric_tail β hβ
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let m := Real.log 2/(50*(N:ℝ))
  refine ⟨m,by positivity,?_⟩
  intro G b hb x y
  let f := siteDistance x.val y.val/(50*(N:ℝ))
  have hf : 0 ≤ f := div_nonneg (siteDistance_nonneg _ _) (by positivity)
  let t : ℕ := Nat.floor f-1
  have hft : f < (t:ℝ)+2 := by
    have h1 := Nat.lt_floor_add_one f
    have h2 : Nat.floor f ≤ t+1 := by dsimp [t]; omega
    have h3 : (Nat.floor f:ℝ) ≤ (t:ℝ)+1 := by exact_mod_cast h2
    linarith
  have hp : G.connectionProbability b x y ≤ (1/2:ℝ)^t := by
    by_cases ht0 : t=0
    · simpa only [ht0,pow_zero] using G.connectionProbability_le_one b (fun e => (hb e).1) x y
    · apply ht G b hb x y t
      have he : Nat.floor f=t+1 := by dsimp [t] at *; omega
      have hfl := Nat.floor_le hf
      rw [he,Nat.cast_add,Nat.cast_one] at hfl
      have hmul := (le_div_iff₀ (show (0:ℝ) < 50*(N:ℝ) by positivity)).mp hfl
      have hd := siteDistance_le_radius_twice x.val y.val
      have hr : (N:ℝ)*((25*t:ℕ)+4) ≤ (siteRadius x.val y.val:ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast hr
  apply le_trans hp
  rw [half_pow_exp]
  calc
    _ ≤ Real.exp (Real.log 2*(2-f)) := Real.exp_le_exp.mpr (by nlinarith)
    _=4*Real.exp (-m*siteDistance x.val y.val) := by
      have he : Real.exp (Real.log 2*2)=(4:ℝ) := by
        rw [mul_comm,show (2:ℝ)=(2:ℕ) by norm_num,Real.exp_nat_mul]
        norm_num [Real.exp_log]
      rw [show Real.log 2*(2-f)=Real.log 2*2+(-Real.log 2*f) by ring,Real.exp_add,he]
      congr 2
      dsimp [f,m]
      ring

end LatticeGraph
end ClassicalON

end

end OAI
