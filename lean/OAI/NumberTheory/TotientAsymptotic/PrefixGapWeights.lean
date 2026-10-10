import OAI.NumberTheory.TotientAsymptotic.PrefixWeights

namespace OAI

/-! Signed simplex weights for an adjacent-coordinate gap. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def prefixGapWeight (N : ℕ) (i : Fin (N+1)) (j : Fin (N+2)) : ℝ :=
  prefixWeight (N+2) i.castSucc j-rho*prefixWeight (N+2) i.succ j

lemma prefix_gap_coordinate (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+1)) :
    (u i.castSucc-u i.succ)/rho^(i.val+1)=
      ∑ j,prefixGapWeight N i j*prefixSimplexMap (N+2) u j := by
  have hi := prefixSimplexMap_coordinate (N+2) u i.castSucc
  have hj := prefixSimplexMap_coordinate (N+2) u i.succ
  simp only [prefixGapWeight,sub_mul,Finset.sum_sub_distrib,mul_assoc]
  rw [←Finset.mul_sum,←hi,←hj]
  simp only [Fin.val_castSucc,Fin.val_succ,pow_succ]
  field_simp [rho_pos.ne']

theorem prefix_gap_weight_bounds : ∃ M K : ℝ,1 ≤ M ∧ 0 < K ∧
    ∀ (N : ℕ) (i : Fin (N+1)),
      (∀ j,-M ≤ prefixGapWeight N i j ∧ prefixGapWeight N i j ≤ M) ∧
      (1-rho)*(N+2-i.val:ℕ)-2*K ≤ ∑ j,prefixGapWeight N i j ∧
      (∑ j,(prefixGapWeight N i j)^2) ≤ 4*M*((N+2-i.val:ℕ)+K) := by
  obtain ⟨M,K,hM,hK,hbound⟩ := prefixWeight_bounds
  refine ⟨M,K,hM,hK,?_⟩
  intro N i
  obtain ⟨ha,hsa,hqa⟩ := hbound (N+2) i.castSucc
  obtain ⟨hb,hsb,hqb⟩ := hbound (N+2) i.succ
  have hρ := rho_pos
  have hρ1 := rho_lt_one
  have hmeanA := (abs_le.mp hsa).1
  have hmeanB := (abs_le.mp hsb).2
  have hn : N+2-(i.val+1)=N+2-i.val-1 := by omega
  have hreal : ((N+2-(i.val+1):ℕ):ℝ)=((N+2-i.val:ℕ):ℝ)-1 := by
    rw [hn,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]
  refine ⟨?_,?_,?_⟩
  · intro j
    obtain ⟨ha0,haM⟩ := ha j
    obtain ⟨hb0,hbM⟩ := hb j
    dsimp [prefixGapWeight]
    constructor <;> nlinarith only [ha0,haM,hb0,hbM,hρ,hρ1,hM]
  · simp only [prefixGapWeight,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp only [Fin.val_castSucc,Fin.val_succ] at hmeanA hmeanB
    rw [hreal] at hmeanB
    nlinarith only [hmeanA,hmeanB,hρ,hρ1,hK]
  · have hsq : (∑ j,(prefixGapWeight N i j)^2) ≤
        2*(∑ j,(prefixWeight (N+2) i.castSucc j)^2)+
          2*rho^2*(∑ j,(prefixWeight (N+2) i.succ j)^2) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      dsimp [prefixGapWeight]
      nlinarith only [sq_nonneg (prefixWeight (N+2) i.castSucc j+
        rho*prefixWeight (N+2) i.succ j)]
    simp only [Fin.val_castSucc,Fin.val_succ] at hqa hqb
    rw [hreal] at hqb
    have hqb0 : 0 ≤ ∑ j,(prefixWeight (N+2) i.succ j)^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right
      (show rho^2 ≤ 1 by nlinarith only [hρ,hρ1]) hqb0
    nlinarith only [hsq,hqa,hqb,hh,hM,hK]

end TotientAsymptotic

end

end OAI
