import OAI.NumberTheory.JointDickman.Amplification.CoarseFeatureBounds
import OAI.NumberTheory.JointDickman.Amplification.GeometricFeatureBounds

namespace OAI

/-! # Quantitative variation of the actual geometric coarse coefficients -/
namespace JointDickman
open Finset Classical

theorem primeCoarseCoefficient_sub (m B : ℕ)
    (K L : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (a b : Fin m) :
    primeCoarseCoefficient m B K a b-primeCoarseCoefficient m B L a b =
      primeCoarseCoefficient m B (fun i j => K i j-L i j) a b := by
  simp only [primeCoarseCoefficient,groupedKernelCoefficient,sum_sub_distrib,mul_sub]

theorem geometricWindowKernel_sub (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (i j : Fin (channelFineCount m B)) :
    geometricWindowKernel m B t L U S V i j-geometricWindowKernel m B t L U S W i j =
      geometricWindowKernel m B t L U S (fun k i j => V k i j-W k i j) i j := by
  unfold geometricWindowKernel
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem geometric_coarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ D) (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hwidth : 0 ≤ U-L+1 := by linarith
  have hoverlap : 0 ≤ (1+U-L)/t+1 := by
    apply add_nonneg _ zero_le_one
    exact div_nonneg (by linarith) ht.le
  have hM : 0 ≤ ((1+U-L)/t+1)*D := mul_nonneg hoverlap hD
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hLU hD S V hV
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  apply primeCoarseCoefficient_bound hm hBpos _ _ a b
  intro i
  convert hr i using 1
  ring

theorem geometric_coarseCoefficient_difference {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, i ∈ geometricHistogramWindow m B t L U k →
      j ∈ geometricHistogramWindow m B t L U k → |V k i j-W k i j| ≤ D)
    (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b-
      primeCoarseCoefficient m B (geometricWindowKernel m B t L U S W) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  let Z := fun k i j => if i ∈ geometricHistogramWindow m B t L U k ∧
    j ∈ geometricHistogramWindow m B t L U k then V k i j-W k i j else 0
  have hZ : ∀ k ∈ S, ∀ i j, |Z k i j| ≤ D := by
    intro k hk i j
    by_cases hh : i ∈ geometricHistogramWindow m B t L U k ∧ j ∈ geometricHistogramWindow m B t L U k
    · simpa [Z,hh] using hV k hk i j hh.1 hh.2
    · simpa [Z,hh] using hD
  rw [primeCoarseCoefficient_sub]
  have he : (fun i j => geometricWindowKernel m B t L U S V i j-
      geometricWindowKernel m B t L U S W i j) = geometricWindowKernel m B t L U S Z := by
    funext i j
    rw [geometricWindowKernel_sub]
    unfold geometricWindowKernel
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [Z]
    split_ifs <;> rfl
  rw [he]
  exact geometric_coarseCoefficient_bound hm hB ht hLU hD S Z hZ a b

end JointDickman

end OAI
