import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMass
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! The ramified coefficient mass is an explicit geometric series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRamifiedRatio (σ : ℝ) : ℝ := 3^(-2-3*σ)

lemma cubicThetaRamifiedRatio_pos (σ : ℝ) : 0 < cubicThetaRamifiedRatio σ := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma cubicThetaRamifiedRatio_lt_one {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaRamifiedRatio σ < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma cubicThetaRamifiedMass_power (σ : ℝ) (k : ℕ) (j : Fin 3) :
    (3:ℝ)^(8-2*(((k*3+j.val)/3:ℕ):ℝ)-((k*3+j.val:ℕ):ℝ)*σ) =
      3^(8-(j.val:ℝ)*σ) * cubicThetaRamifiedRatio σ^k := by
  have hd : (k*3+j.val)/3=k := by omega
  rw [hd,cubicThetaRamifiedRatio,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    ←Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  push_cast
  congr 1
  ring

lemma cubicThetaRamifiedMass_class_zero (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3)) =
      6*3^(8:ℝ)*cubicThetaRamifiedRatio σ^k - (if k=0 then 6*3^(8:ℝ) else 0) := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hp := cubicThetaRamifiedMass_power σ k (0:Fin 3)
  simp only [Fin.val_zero,Nat.add_zero,Nat.cast_zero,zero_mul,sub_zero] at hp
  rw [hp]
  by_cases hk : k=0
  · subst k
    norm_num
  · have h3 : 3 ≤ k*3 := by omega
    simp only [Nat.mul_mod_left,h3,true_and,ite_true,ite_eq_right hk,sub_zero]
    ring

lemma cubicThetaRamifiedMass_class_one (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+1)) =
      2*3^(8-σ)*cubicThetaRamifiedRatio σ^k := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hp := cubicThetaRamifiedMass_power σ k (1:Fin 3)
  norm_num only [Fin.val_one,Nat.cast_one,one_mul] at hp
  rw [hp]
  have hm : (k*3+1)%3=1 := by omega
  simp only [hm,one_ne_zero,false_and,ite_false,ite_true]
  ring

lemma cubicThetaRamifiedMass_class_two (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+2)) = 0 := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hm : (k*3+2)%3=2 := by omega
  norm_num [hm]

lemma cubicThetaRamifiedMass_class_hasSum {σ : ℝ} (hσ : 0 < σ) (j : Fin 3) :
    HasSum (fun k : ℕ => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+j.val))
      (if j.val=0 then 6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1)
       else if j.val=1 then 2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ else 0) := by
  have hg := hasSum_geometric_of_lt_one (cubicThetaRamifiedRatio_pos σ).le
    (cubicThetaRamifiedRatio_lt_one hσ)
  fin_cases j
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false,Nat.add_zero]
    convert (hg.mul_left (6*3^(8:ℝ))).sub (hasSum_ite_eq (0:ℕ) (6*3^(8:ℝ))) using 1
    · ext k
      exact cubicThetaRamifiedMass_class_zero σ k
    · ring
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false]
    simpa only [cubicThetaRamifiedMass_class_one] using hg.mul_left (2*3^(8-σ))
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false]
    simp only [cubicThetaRamifiedMass_class_two]
    exact hasSum_zero

lemma cubicThetaRamifiedMass_nonneg (σ : ℝ) (u : Eisensteinˣ) (k : ℕ) :
    0 ≤ cubicThetaRamifiedMass σ u k := by
  unfold cubicThetaRamifiedMass
  split_ifs <;> positivity

lemma cubicThetaRamifiedMass_sum_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun k : ℕ => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) := by
  let e := (Nat.divModEquiv 3).trans (Equiv.prodComm ℕ (Fin 3))
  apply (e.symm.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => tsum_nonneg
    (fun u => cubicThetaRamifiedMass_nonneg σ u _))).2
  constructor
  · intro j
    exact (cubicThetaRamifiedMass_class_hasSum hσ j).summable
  · exact Summable.of_finite

lemma cubicThetaRamifiedMass_sum {σ : ℝ} (hσ : 0 < σ) :
    (∑' k : ℕ, ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) =
      6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
      2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ := by
  let e := (Nat.divModEquiv 3).trans (Equiv.prodComm ℕ (Fin 3))
  rw [←e.symm.tsum_eq (fun k => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k)]
  have he := ((e.symm.summable_iff).mpr (cubicThetaRamifiedMass_sum_summable hσ)).tsum_prod
  dsimp only [Function.comp_def] at he
  rw [he]
  change (∑' j : Fin 3, ∑' k : ℕ, ∑' u : Eisensteinˣ,
    cubicThetaRamifiedMass σ u (k*3+j.val)) = _
  simp_rw [(cubicThetaRamifiedMass_class_hasSum hσ _).tsum_eq]
  rw [tsum_fintype]
  simp [Fin.sum_univ_succ]

end CubicFirstMoment

end

end OAI
