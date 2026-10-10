import OAI.Analysis.Cotype.TypeExtrapolation
import OAI.Analysis.Cotype.BConvexBlocking

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem not_uniformL1_of_nontrivialType (ht : NontrivialType X) : ¬ UniformL1 X := by
  classical
  obtain ⟨p,hp,hp2,D,hD,ht⟩ := ht
  have hp0 : 0 < p := by linarith
  let α : ℝ := 1-1/p
  have hα : 0 < α := by
    dsimp [α]
    have hi : 1/p < (1 : ℝ) := (div_lt_one hp0).mpr hp
    linarith
  rintro ⟨c,hc,hx⟩
  let R : ℝ := (D/c+1)^(1/α)
  have hb0 : 0 < D/c+1 := by positivity
  have hR : 0 < R := Real.rpow_pos_of_pos hb0 _
  obtain ⟨n,hn⟩ := exists_nat_gt (max R 1)
  have hn0 : (0 : ℝ) < n := lt_trans (by norm_num : (0 : ℝ) < 1) ((le_max_right _ _).trans_lt hn)
  have hRn : R < n := (le_max_left _ _).trans_lt hn
  have hlarge : D/c+1 < (n : ℝ)^α := by
    have hh := Real.rpow_lt_rpow hR.le hRn hα
    have he : R^α = D/c+1 := by
      dsimp [R]
      rw [← Real.rpow_mul hb0.le,div_mul_cancel₀ 1 (ne_of_gt hα),Real.rpow_one]
    rwa [he] at hh
  obtain ⟨x,hx⟩ := hx n
  have hl (ε : Cube n) : c*n ≤ ‖rademacherSum X x ε‖ := by
    have hh := hx.2 (fun i => sign (ε i))
    have hs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
    simpa only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,rademacherSum] using hh
  have hlow : c*n ≤ cubeL2 X (rademacherSum X x) := by
    have hh := cubeL2_mono (fun ε : Cube n => show ‖(c*n : ℝ)‖ ≤ ‖rademacherSum X x ε‖ by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact hl ε)
    simpa only [cubeL2_const,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ c*n)] using hh
  have hmass : (∑ i, ‖x i‖^p) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => Real.rpow_le_one (norm_nonneg _) (hx.1 i) hp0.le)
      _ = _ := by simp
  have hu : c*n ≤ D*(n : ℝ)^(1/p) := hlow.trans ((ht n x).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) _)) hmass (by positivity)) hD))
  have he : (n : ℝ)^α*(n : ℝ)^(1/p) = n := by
    rw [← Real.rpow_add hn0]
    have hαeq : α+1/p = 1 := by dsimp [α]; ring
    rw [hαeq,Real.rpow_one]
  have hsmall : c*(n : ℝ)^α ≤ D := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn0 (1/p))).mp
    rw [mul_assoc,he]
    exact hu
  have hsmall' : (n : ℝ)^α ≤ D/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hsmall)
  linarith

theorem nontrivialType_iff_not_uniformL1 : NontrivialType X ↔ ¬ UniformL1 X :=
  ⟨not_uniformL1_of_nontrivialType,fun h => nontrivialType_of_bConvex (bConvex_of_not_uniformL1 h)⟩

theorem nontrivialType_iff_bConvex : NontrivialType X ↔ BConvex X :=
  nontrivialType_iff_not_uniformL1.trans bConvex_iff_not_uniformL1.symm

end Cotype

end

end OAI
