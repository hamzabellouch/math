import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma subexponential_enlargement (v : ℕ → ℕ) (hv : ∀ n, 0<v n)
    (hg : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N, Real.log (v n : ℝ) ≤ ε*n)
    (t R : ℕ) : ∃ n≥R, v (n+t) ≤ 2*v n := by
  by_contra! hbad
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  let ε := Real.log 2/(2*((t:ℝ)+1))
  have hd : 0<2*((t:ℝ)+1) := by positivity
  have hε : 0<ε := div_pos hc hd
  have hεeq : ε*(2*((t:ℝ)+1)) = Real.log 2 := div_mul_cancel₀ _ hd.ne'
  obtain ⟨N,hN⟩ := hg ε hε
  let n₀ := max R N
  have hnR : R≤n₀ := le_max_left _ _
  have hnN : N≤n₀ := le_max_right _ _
  have hstep (n : ℕ) (hn : R≤n) :
      Real.log (v n : ℝ)+Real.log 2 < Real.log (v (n+t) : ℝ) := by
    have hp : (0:ℝ)<v n := Nat.cast_pos.mpr (hv n)
    have hh : (2:ℝ)*(v n:ℝ) < (v (n+t):ℝ) := by exact_mod_cast hbad n hn
    have hl := Real.log_lt_log (mul_pos (by norm_num) hp) hh
    rwa [Real.log_mul (by norm_num) hp.ne',add_comm] at hl
  have hlow : ∀ k : ℕ, (k:ℝ)*Real.log 2 ≤ Real.log (v (n₀+k*t) : ℝ) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,Nat.cast_zero,zero_mul]
      exact Real.log_nonneg (by exact_mod_cast hv n₀)
    | succ k ih =>
      have hs := hstep (n₀+k*t) (hnR.trans (Nat.le_add_right _ _))
      have he : n₀+(k+1)*t = n₀+k*t+t := by ring
      rw [he,Nat.cast_add,Nat.cast_one]
      nlinarith
  let k := n₀+1
  have hboth : (k:ℝ)*Real.log 2 ≤ ε*(n₀+k*t : ℕ) :=
    (hlow k).trans (hN _ (hnN.trans (Nat.le_add_right _ _)))
  have hnum : (k:ℝ)*(2*((t:ℝ)+1)) ≤ (n₀+k*t : ℕ) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      _ = ((k:ℝ)*Real.log 2)*(2*((t:ℝ)+1)) := by ring
      _ ≤ (ε*(n₀+k*t : ℕ))*(2*((t:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hboth hd.le
      _ = _ := by rw [mul_right_comm,hεeq]; ring
  dsimp only [k] at hnum
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hnum
  nlinarith [(Nat.cast_nonneg n₀ : (0:ℝ)≤n₀),(Nat.cast_nonneg t : (0:ℝ)≤t),mul_nonneg (Nat.cast_nonneg n₀ : (0:ℝ)≤n₀)
    (Nat.cast_nonneg t : (0:ℝ)≤t)]

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SubexponentialGrowth : Prop :=
  ∀ o : V, ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N,
    Real.log ((G.vertexBall o n).ncard : ℝ) ≤ ε*n

lemma subexponential_ball_enlargement (hlocal : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (o : V) (t R : ℕ) :
    ∃ n≥R, (G.vertexBall o (n+t)).ncard ≤ 2*(G.vertexBall o n).ncard := by
  apply subexponential_enlargement _ _ (hg o)
  intro n
  exact (Set.ncard_pos (G.vertexBall_finite hlocal o n)).mpr ⟨o,G.mem_vertexBall_self o n⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
