import OAI.MeasureTheory.Falconer.Estimates.CommonTubePower
import OAI.MeasureTheory.Falconer.Recursion.FiniteCountingPotential
import OAI.MeasureTheory.Falconer.Estimates.TubeSecondMoment

namespace OAI

/-! The elementary incidence bound at one dyadic scale. This is the baseline
bound, before the strict gain from regular scales in the Furstenberg proof. -/
namespace Falconer
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planar_baseline_incidence (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (N M : ℕ) (hP : P.Nonempty) (hM : 0 < M) {K b f : ℝ}
    (hK : 1 ≤ K) (hb : 0 ≤ b) (hbf : b < f) (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P)
    (hT : ∀ x ∈ P, (T x).card = M ∧ InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) b K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (M : ℝ) ≤ ((P.biUnion T).card : ℝ)*
      (K*(80*(1/(2:ℝ)^N))^b*(1+K*planarPotentialConstant b f)) := by
  let δ := 1/(2:ℝ)^N
  let C := planarPotentialConstant b f
  let A := K*(80*δ)^b*(1+K*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC : 0 < C := planarPotentialConstant_pos hbf
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card : ℝ)) ≤ A*(M : ℝ)*(P.card : ℝ) := by
    have hc := hT x hx
    have hpot := finite_dyadic_truncated_potential_real P x N hK hb hbf hPball
    calc
      _ ≤ ∑ y ∈ P, (K*(80*δ)^b*(M : ℝ))*(1+(1/max (dist x y) δ)^b) := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [hc.1] using intersect_tube_power_bound hδ hδ1 hb hK (T x) (T y)
          x y (hPchart x hx).1 hc.2.1 hc.2.2.2 (hT y hy).2.2.2 hc.2.2.1
      _ = (K*(80*δ)^b*(M : ℝ))*((P.card : ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^b) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ (K*(80*δ)^b*(M : ℝ))*((P.card : ℝ)+K*C*(P.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hE : (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ)) ≤
      A*(M : ℝ)*(P.card : ℝ)^2 := by
    calc
      _ ≤ ∑ _x ∈ P, A*(M : ℝ)*(P.card : ℝ) := Finset.sum_le_sum hrow
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hI : (∑ x ∈ P, ((T x).card : ℝ)) = (M : ℝ)*(P.card : ℝ) := by
    simp only [Finset.sum_congr rfl (fun x hx => congrArg (Nat.cast : ℕ → ℝ) (hT x hx).1)]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  have hh := (tube_union_second_moment P T).trans
    (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg (P.biUnion T).card))
  rw [hI] at hh
  have hfactor : 0 < (M : ℝ)*(P.card : ℝ)^2 := by
    have hmp : (0 : ℝ) < M := by exact_mod_cast hM
    have hpp : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    positivity
  have hcancel : (M : ℝ)*((M : ℝ)*(P.card : ℝ)^2) ≤
      (((P.biUnion T).card : ℝ)*A)*((M : ℝ)*(P.card : ℝ)^2) := by
    convert hh using 1 <;> ring
  exact (mul_le_mul_iff_left₀ hfactor).mp hcancel

end Falconer

end OAI
