import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation

namespace OAI

/-! # Continuous identification with a fixed Fourier Sobolev space

Inverse weight transfer keeps physical Fourier coefficients unchanged.
It permits strong time derivatives to be stated in one fixed Banach space.
-/

open Set Filter Topology

namespace DefocusingNLS

noncomputable def expandingPhysicalPath (a k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := expandingInverseTransfer a k (expandingRadius L t) ha hk
    (hL.trans (expandingRadius_ge L t hL t.2.1)) (u t)
  continuous_toFun :=
    ((continuous_expandingInverseTransfer a k ha hk).comp
      (expandingRadiusCurve L T hL).continuous).clm_apply u.continuous

theorem expandingPhysicalPath_coefficient (a k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) (n : frequencyLattice) :
    expandingPhysicalPath a k L T ha hk hL u t n =
      (expandingSobolevWeight a k 1 n : ℂ) *
        expandingFourierCoefficient a k (expandingRadius L t) (u t) n := by
  change (expandingInverseRatio a k (expandingRadius L t) n : ℂ) * u t n = _
  unfold expandingInverseRatio expandingFourierCoefficient
  push_cast
  rw [div_eq_mul_inv, mul_assoc]

/-- A physical Fourier-coordinate derivative transports into the fixed weighted model. -/
theorem hasDerivAt_expandingPhysicalPath_coordinate (a k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : ℝ) (ht : t ∈ Ioo 0 T)
    (n : frequencyLattice) (d : ℂ)
    (hd : HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s)
      (u (projIcc 0 T hT s)) n) d t) :
    HasDerivAt (fun s => expandingPhysicalPath a k L T ha hk hL u (projIcc 0 T hT s) n)
      ((expandingSobolevWeight a k 1 n : ℂ) * d) t := by
  apply (hd.const_mul _).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩,
    expandingPhysicalPath_coefficient a k L T ha hk hL u ⟨s, hs.1.le, hs.2.le⟩ n]

end DefocusingNLS

end OAI
