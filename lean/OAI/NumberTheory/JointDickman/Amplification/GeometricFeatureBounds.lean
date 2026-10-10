import OAI.NumberTheory.JointDickman.Amplification.CoarseFeatureBounds
import OAI.NumberTheory.JointDickman.Probability.GeometricCoarseKernel

namespace OAI

/-! # Bounds for the actual box-summed finite-feature kernel -/

namespace JointDickman
open Finset

theorem geometric_primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t β a b D M₁ M₂ M₀ : ℝ} (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k| ≤ D)
    (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B
      (geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t β d w₁ w₂ w)) x y| ≤
      (m : ℝ)^2*(2*((((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)))*
        (Real.log b-Real.log a+2))/channelMesh m := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogs := Real.log_le_log ha hab
  let M := ((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)
  have hoverlap : 0 ≤ (1+Real.log b-Real.log a)/t+1 :=
    add_nonneg (div_nonneg (by linarith) ht.le) zero_le_one
  have hM : 0 ≤ M := mul_nonneg hoverlap (by positivity)
  have hwidth : 0 ≤ Real.log b-Real.log a+1 := by linarith
  have hwidth' : 0 ≤ Real.log b-Real.log a+2 := by linarith
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hlogs
    (by positivity : 0 ≤ D*M₁*M₂*M₀) S (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight_bound m B t β S d w₁ w₂ w hD hM₁ hM₂ hd hw₁ hw₂ hw)
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  have hh := primeCoarseKernel_bound hm hBpos
    (geometricWindowKernel m B t (Real.log a) (Real.log b) S
      (endpointSpatialWeight m B t β d w₁ w₂ w)) (by positivity : 0 ≤ 2*M*(Real.log b-Real.log a+2))
    (by intro i; convert hr i using 1; ring) x y
  simpa only [M,sub_add_eq_add_sub,add_assoc] using hh

end JointDickman

end OAI
