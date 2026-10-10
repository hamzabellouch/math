import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourier
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevMultiplication

namespace OAI

/-! # Uniform point observation for the expanding-torus norm

Torus coordinates are normalized by the expanding scale. The coefficient norm
is exactly the volume-weighted `Y_L` norm, with no change of Fourier weight.
-/

open Filter Topology

namespace DefocusingNLS

noncomputable def expandingTorusTerm (a k L : ℝ) (f : FourierL2)
    (n : frequencyLattice) : C(SchrodingerTorus, ℂ) :=
  expandingFourierCoefficient a k L f n • torusCharacter n

theorem summable_expandingTorusTerm (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    Summable (expandingTorusTerm a k L f) := by
  apply Summable.of_norm
  simpa [expandingTorusTerm, norm_smul] using
    summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f

noncomputable def expandingTorusFunction (a k L : ℝ) (f : FourierL2) :
    C(SchrodingerTorus, ℂ) := ∑' n, expandingTorusTerm a k L f n

theorem expandingTorusFunction_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L f x =
      ∑' n, expandingFourierCoefficient a k L f n * torusCharacter n x := by
  have h := (summable_expandingTorusTerm a k L ha ha1 hk hL f).hasSum.mapL
    (ContinuousMap.evalCLM (R := ℂ) x)
  have h' : HasSum (fun n => expandingFourierCoefficient a k L f n * torusCharacter n x)
      (expandingTorusFunction a k L f x) := by
    simpa [expandingTorusTerm, expandingTorusFunction, smul_eq_mul] using h
  exact h'.tsum_eq.symm

/-- Uniform convergence of the actual Fourier polynomials in normalized coordinates. -/
theorem tendstoUniformly_expandingFourierSeries (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    TendstoUniformly
      (fun S : Finset frequencyLattice => fun x : SchrodingerTorus =>
        ∑ n ∈ S, expandingFourierCoefficient a k L f n * torusCharacter n x)
      (expandingTorusFunction a k L f) atTop := by
  have h := (ContinuousMap.isometryEquivBoundedOfCompact SchrodingerTorus ℂ).continuous.continuousAt.tendsto.comp
    (summable_expandingTorusTerm a k L ha ha1 hk hL f).hasSum
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h
  change TendstoUniformly
    (fun S x => (∑ n ∈ S, expandingTorusTerm a k L f n) x)
    (expandingTorusFunction a k L f) atTop at hu
  simpa [expandingTorusTerm, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using hu

/-- The observation constant is independent of the torus radius. -/
theorem expandingTorusFunction_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    ‖expandingTorusFunction a k L f‖ ≤ expandingEmbeddingBound a k * ‖f‖ := by
  have hs : Summable (fun n => ‖expandingTorusTerm a k L f n‖) := by
    simpa [expandingTorusTerm, norm_smul] using
      summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f
  calc
    _ ≤ ∑' n, ‖expandingTorusTerm a k L f n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖expandingFourierCoefficient a k L f n‖ := by
      simp [expandingTorusTerm, norm_smul]
    _ ≤ _ := tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL f

theorem expandingTorusFunction_point_bound (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (x : SchrodingerTorus) :
    ‖expandingTorusFunction a k L f x‖ ≤ expandingEmbeddingBound a k * ‖f‖ :=
  (ContinuousMap.norm_coe_le_norm _ x).trans
    (expandingTorusFunction_norm_le a k L ha ha1 hk hL f)

end DefocusingNLS

end OAI
