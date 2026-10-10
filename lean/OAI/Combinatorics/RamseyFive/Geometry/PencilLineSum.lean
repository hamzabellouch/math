import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

lemma pencil_line_sum_le (hdim : finrank K V=5)
    (F : Finset (ℙ K (Dual K V))) (f : RadialLine x→ℝ) (hf : ∀ d,0 ≤ f d) :
    (∑ H : F,∑ d∈pencilLines x F H,f d) ≤
      (pencilAlphabet (Nat.card K) 3:ℝ)*∑ d,f d := by
  have he : (∑ H : F,∑ d∈pencilLines x F H,f d) =
      ∑ d : RadialLine x,((Finset.univ.filter fun H : F => d∈pencilLines x F H).card:ℝ)*f d := by
    calc
      _ = ∑ H : F,∑ d : RadialLine x,if d∈pencilLines x F H then f d else 0 := by
        apply Finset.sum_congr rfl
        intro H _
        simp only [←Finset.sum_filter]
        congr 1
        ext d
        simp
      _ = ∑ d : RadialLine x,∑ H : F,if d∈pencilLines x F H then f d else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_right _ (hf d)
  exact Nat.cast_le.mpr (by simpa only [hdim,Nat.reduceSub,pencilAlphabet] using one_anchor_count x F d)

lemma independent_sum_le (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (base D A : ℝ) (R J : ℕ) (hR : 2 ≤ R/2)
    (hdev : ∀ H : F,|mass (radialWeight x X δ) (pencilLines x F H)-base| ≤ 1)
    (hvar : (∑ H : F,(mass (radialWeight x X δ) (pencilLines x F H)-base)^2) ≤ D)
    (hpow : (∑ d : RadialLine x,(radialWeight x X δ d:ℝ)^J) ≤ A)
    (hA : 0 ≤ A) :
    (∑ H : F,SingletonEnumeration.independentWeight (radialWeight x X δ)
      (fun d => L*radialWeight x X δ d) (pencilLines x F) R J base H) ≤
      D+(pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^J*A := by
  have hv : (∑ H : F,|mass (radialWeight x X δ) (pencilLines x F H)-base|^(R/2)) ≤ D := by
    apply le_trans (Finset.sum_le_sum fun H _ => ?_) hvar
    simpa only [sq_abs] using pow_le_pow_of_le_one (abs_nonneg _) (hdev H) hR
  simp only [SingletonEnumeration.independentWeight,Finset.sum_add_distrib]
  apply add_le_add hv
  by_cases hRJ : R < J
  · simp only [ite_eq_left hRJ,Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _)) hA
  · simp only [ite_eq_right hRJ]
    have he (d : RadialLine x) : ((R:ℝ)*((L*radialWeight x X δ d:ℝ≥0):ℝ))^J =
        ((R:ℝ)*(L:ℝ))^J*(radialWeight x X δ d:ℝ)^J := by
      simp only [NNReal.coe_mul,←mul_assoc,mul_pow]
    simp_rw [he]
    calc
      _ ≤ (pencilAlphabet (Nat.card K) 3:ℝ)*
          ∑ d : RadialLine x,((R:ℝ)*(L:ℝ))^J*(radialWeight x X δ d:ℝ)^J :=
        pencil_line_sum_le x hdim F _ (fun d => mul_nonneg
          (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _) (pow_nonneg (NNReal.coe_nonneg _) _))
      _ = (pencilAlphabet (Nat.card K) 3:ℝ)*((R:ℝ)*(L:ℝ))^J*
          ∑ d : RadialLine x,(radialWeight x X δ d:ℝ)^J := by rw [←Finset.mul_sum,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) _))

end SharpRamseyFive.ScoreGeometry

end OAI
