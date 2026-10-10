import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalDerivativeBound

namespace OAI

/-! # Finite physical Fourier sums along a continuous expanding trajectory -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingPhysicalPolynomial (a k L T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (S : Finset frequencyLattice) (y : E) (τ : ℝ) : ℂ :=
  let s := projIcc 0 T hT τ
  ∑ n ∈ S, expandingFourierCoefficient a k (expandingRadius L s) (u s) n *
    spatialFourierCharacter n ((expandingRadius L s)⁻¹ • y)

theorem continuous_expandingPhysicalPolynomial (a k L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (S : Finset frequencyLattice) (y : E) :
    Continuous (expandingPhysicalPolynomial a k L T hT u S y) := by
  apply continuous_finsetSum
  intro n _
  have hc : Continuous (fun τ : ℝ =>
      expandingFourierCoefficient a k (expandingRadius L (projIcc 0 T hT τ))
        (u (projIcc 0 T hT τ)) n) := (continuous_expandingFourierCoefficient a k n).comp
    (((expandingRadiusCurve L T hL).continuous.comp continuous_projIcc).prodMk
      (u.continuous.comp continuous_projIcc))
  have hi : Continuous (fun τ : ℝ => (expandingRadius L τ)⁻¹) :=
    continuous_iff_continuousAt.mpr (fun τ => (hasDerivAt_expandingRadius_inv L τ).continuousAt)
  have hy : Continuous (fun τ : ℝ => spatialFourierCharacter n
      ((expandingRadius L (projIcc 0 T hT τ))⁻¹ • y)) :=
    (continuous_spatialFourierCharacter n).comp
    ((hi.comp (continuous_subtype_val.comp continuous_projIcc)).smul continuous_const)
  exact hc.mul hy

theorem hasDerivAt_expandingPhysicalPolynomial (a b k L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (g : ℝ → FourierL2)
    (S : Finset frequencyLattice) (y : E) (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hmode : ∀ n : frequencyLattice,
      HasDerivAt (fun τ => expandingFourierCoefficient a k (expandingRadius L τ) (u (projIcc 0 T hT τ)) n)
        (expandingModeRate a b L t n * expandingFourierCoefficient a k (expandingRadius L t)
          (u (projIcc 0 T hT t)) n + expandingFourierCoefficient a k (expandingRadius L t) (g t) n) t) :
    HasDerivAt (expandingPhysicalPolynomial a k L T hT u S y)
      (∑ n ∈ S, (physicalModeRate a b (expandingRadius L t) n y *
        expandingFourierCoefficient a k (expandingRadius L t) (u (projIcc 0 T hT t)) n +
          expandingFourierCoefficient a k (expandingRadius L t) (g t) n) *
            spatialFourierCharacter n ((expandingRadius L t)⁻¹ • y)) t := by
  have hd := HasDerivAt.sum (u := S) (fun n _ =>
    hasDerivAt_expandingPhysicalMode a b k L t hL n y
      (fun τ => u (projIcc 0 T hT τ)) _ (hmode n))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  simp only [expandingPhysicalPolynomial, Finset.sum_apply, projIcc_of_mem hT ⟨hτ.1.le, hτ.2.le⟩]

end DefocusingNLS

end OAI
