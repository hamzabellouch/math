import OAI.Combinatorics.Progressions.Dynamics.MixedAccuracyBudget
import OAI.Combinatorics.Progressions.Geometry.SpatialChoiceEnvelope

namespace OAI

section

namespace Erdos3

theorem mixedSpatialCap_le_exp (d n : ℕ) {m C P Q : ℝ}
    (hm : 0 ≤ m) (hC : 0 ≤ C) (hmP : m ≤ Real.exp P) (hCQ : C ≤ Real.exp Q) :
    (m^n*C)^d ≤ Real.exp (d*(n*P+Q)) := by
  calc
    _ ≤ ((Real.exp P)^n*Real.exp Q)^d :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul (pow_le_pow_left₀ hm hmP n) hCQ hC (by positivity)) d
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

theorem smoothSpatialMixtureCap_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B m d : ℕ) {P R : ℝ}
    (hm : (m : ℝ) ≤ Real.exp P) (hU : scalarSpatialInverseAllowance I B ≤ Real.exp R) :
    ((m : ℝ)^Fintype.card (Unit ⊕ I)*smoothSpatialDensityCap s B)^d ≤
      Real.exp (d*(Fintype.card (Unit ⊕ I)*P+
        ((Fintype.card (Unit ⊕ I) : ℝ)^2+Fintype.card (Unit ⊕ I)*R+2*Fintype.card (UnselectedColumn s)))) :=
  mixedSpatialCap_le_exp d (Fintype.card (Unit ⊕ I)) (Nat.cast_nonneg m)
    (smoothSpatialDensityCap_nonneg s B) hm (smoothSpatialDensityCap_le_exp s B hU)

theorem jointMixedTolerances_inverse_le_exp (n : ℕ) {C G S τ P : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hS : 0 ≤ S) (hτ : 0 < τ) (hP : 0 ≤ P)
    (hCP : C ≤ Real.exp P) (hGP : G ≤ Real.exp P) (hSP : S ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (vectorSpatialAccuracy n (2+G*C) (mixedCoefficientAccuracy S τ))⁻¹ ≤
        Real.exp ((n+1)*(2*P+4)+n+1) ∧
      (jointQuadratureAccuracy n G (mixedCoefficientAccuracy S τ))⁻¹ ≤
        Real.exp ((n+1)*(2*P+5)+n+1) := by
  have hGC : G*C ≤ Real.exp (2*P) := by
    calc
      _ ≤ Real.exp P*Real.exp P := mul_le_mul hGP hCP hC (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by positivity)
  have hA : 2+G*C ≤ Real.exp (2*P+4) := by
    calc
      _ ≤ 3*Real.exp (2*P) := by linarith
      _ ≤ Real.exp 4*Real.exp (2*P) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hμ := mixedCoefficientAccuracy_pos hS hτ
  have hi := mixedCoefficientAccuracy_inverse_le_exp hS hτ hP hSP hτP
  refine ⟨vectorSpatialAccuracy_inverse_le_exp n (by positivity) hμ hA hi, ?_⟩
  have hG' : G ≤ Real.exp (2*P+4) := hGP.trans (Real.exp_le_exp.mpr (by linarith))
  have hq := jointQuadratureAccuracy_inverse_le_exp n hG hμ (by positivity : 0 ≤ 2*P+4) hG' hi
  simpa only [show (2*P+4)+1 = 2*P+5 by ring] using hq

end Erdos3

end

end OAI
