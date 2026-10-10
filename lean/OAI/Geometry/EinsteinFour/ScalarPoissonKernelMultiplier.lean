import OAI.Geometry.EinsteinFour.ScalarPoissonKernelDerivative

namespace OAI

/-! Smooth compactly supported coefficients preserve every nonnegative
integer Sobolev order.  The proof uses the actual distributional product
rule and the coordinate-derivative characterization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

private theorem scalar_schwartz_coordinate_product (a φ : 𝓢(V, ℂ)) (i : Fin 4) :
    ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (SchwartzMap.smulLeftCLM ℂ a φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) φ +
        SchwartzMap.smulLeftCLM ℂ a (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply a.hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

/-- Leibniz's rule for the actual tempered-distribution coordinate derivative. -/
theorem scalarCoordinateDerivative_multiplier (a : 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ))
    (i : Fin 4) :
    scalarCoordinateDerivative i (smulLeftCLM ℂ a u) =
      smulLeftCLM ℂ (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) u +
        smulLeftCLM ℂ a (scalarCoordinateDerivative i u) := by
  ext φ
  simp only [scalarCoordinateDerivative, lineDerivOp_apply_apply,
    smulLeftCLM_apply_apply, add_apply]
  rw [← map_add]
  congr 1
  rw [scalar_schwartz_coordinate_product]
  simp only [map_neg]
  module

private theorem scalar_memSobolev_zero_multiplier (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM ℂ a u) := by
  obtain ⟨v, hv⟩ := memSobolev_zero_iff.mp hu
  have ha : MemLp (a : V → ℂ) ∞ (volume : Measure V) := a.memLp ∞ volume
  refine memSobolev_zero_iff.mpr ⟨ha.toLp • v, ?_⟩
  rw [hv]
  exact (Lp.toTemperedDistribution_smul_eq a.hasTemperateGrowth ha v).symm

/-- Every Schwartz coefficient preserves each integer Sobolev space. -/
theorem scalar_memSobolev_schwartz_multiplier (n : ℕ) (a : 𝓢(V, ℂ))
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev (n : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ a u) := by
  induction n generalizing a u with
  | zero =>
      simpa only [Nat.cast_zero] using
        scalar_memSobolev_zero_multiplier a u (by simpa only [Nat.cast_zero] using hu)
  | succ n ih =>
      have hu' : MemSobolev (n : ℝ) 2 u ∧
          ∀ i : Fin 4, MemSobolev (n : ℝ) 2 (scalarCoordinateDerivative i u) := by
        apply (scalar_memSobolev_succ_iff (n : ℝ) u).mp
        simpa only [Nat.cast_add, Nat.cast_one] using hu
      have hbase := ih a u hu'.1
      have hderiv : ∀ i : Fin 4, MemSobolev (n : ℝ) 2
          (scalarCoordinateDerivative i (smulLeftCLM ℂ a u)) := by
        intro i
        rw [scalarCoordinateDerivative_multiplier]
        exact (ih (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)) u hu'.1).add
          (ih a (scalarCoordinateDerivative i u) (hu'.2 i))
      simpa only [Nat.cast_add, Nat.cast_one] using
        (scalar_memSobolev_succ_iff (n : ℝ) (smulLeftCLM ℂ a u)).mpr ⟨hbase, hderiv⟩

/-- The compactly supported smooth coefficient form used for local cutoffs. -/
theorem scalar_memSobolev_compact_multiplier (n : ℕ) (a : V → ℂ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (u : 𝓢'(V, ℂ)) (hu : MemSobolev (n : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ a u) :=
  scalar_memSobolev_schwartz_multiplier n (hc.toSchwartzMap ha) u hu

end
end PositiveEinsteinFour.Geometry

end OAI
