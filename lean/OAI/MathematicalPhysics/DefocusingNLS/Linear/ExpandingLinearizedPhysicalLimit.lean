import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothFilter
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization

namespace OAI

/-! # The actual linearized reaction passes to the physical limit -/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingLinearizedPotential_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (q v : FourierL2) (y : E) :
    expandingPhysicalContinuous a k L ha ha1 hk hL
      (expandingLinearizedPotential a k L ha ha1 hk hL m q v) y =
      -Complex.I * oddPowerDerivative m
        (expandingPhysicalContinuous a k L ha ha1 hk hL q y)
        (expandingPhysicalContinuous a k L ha ha1 hk hL v y) := by
  simp only [expandingPhysicalContinuous_apply, expandingLinearizedPotential,
    smul_apply]
  rw [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_smul]
  simp only [← expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL,
    smul_eq_mul, expandingOddPower_fderiv_pointwise]

theorem tendsto_expandingLinearizedPotential_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (q v : ℕ → FourierL2)
    (Q V : HomogeneousY a k) (y : E)
    (hq : Tendsto (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (q n) y)
      atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk Q y)))
    (hv : Tendsto (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (v n) y)
      atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk V y))) :
    Tendsto (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n)
      (expandingLinearizedPotential a k (L n) ha ha1 hk (hL n) m (q n) (v n)) y)
      atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousLinearizedPotential a k ha ha1 hk m Q V) y)) := by
  have hc : Continuous (fun p : ℂ × ℂ => -Complex.I * oddPowerDerivative m p.1 p.2) := by
    simp only [oddPowerDerivative, add_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul]
    fun_prop
  have h := hc.continuousAt.tendsto.comp (hq.prodMk_nhds hv)
  simpa only [Function.comp_def, expandingLinearizedPotential_physical,
    homogeneousLinearizedPotential_physical] using h

end DefocusingNLS

end OAI
