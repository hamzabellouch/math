import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateProfileFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileHeightIdentity

namespace OAI

/-! # Exact increments for the actual polynomial horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

theorem exp_basis_horizontal_flow
    {L D : Type*} [LieRing L] [LieAlgebra ℝ L] [Group D] {n c : ℕ}
    (Exp : L → D) (b : Basis (Fin n) ℝ L) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r t : ℝ) (v : L) (z : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinFlowMap a (basisBracket b) (b.equivFun (r • v)) (z, t))) =
      Exp (b.equivFun.symm z) * Exp ((r * t) • v) := by
  change Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) z
    (t • b.equivFun (r • v)))) = _
  rw [exp_basis_dynkinProduct b Exp a hm]
  simp only [map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm t r]

/-- The profile and occupation chart use identical scaling and basepoints,
so their horizontal increments agree exactly before passing to a limit. -/
theorem coordinate_rescaled_profile_increment
    {G N D LN LD W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G] [Group N] [Group D]
    [LieRing LN] [LieAlgebra ℝ LN] [LieRing LD] [LieAlgebra ℝ LD]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n m c : ℕ} {Λ : ℝ≥0}
    (π : G →* Multiplicative W) (p : NormalizedPair G Λ) (x : G)
    (ι : N →* G) (κ : D →* G) (ExpN : LN → N) (ExpD : LD → D)
    (bN : Basis (Fin n) ℝ LN) (bD : Basis (Fin m) ℝ LD) (k : N)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (v : LD) (s T : ℝ) (y : Fin n → ℝ) (z : Fin m → ℝ) :
    let φ := fun z => κ (ExpD (bD.equivFun.symm z))
    let flow := dynkinFlowMap a (basisBracket bD) (bD.equivFun (Real.exp s • v))
    let f := rescaledMapProfile (fun g => (π (p.val.1 g)).toAdd) x
      (ι (ExpN (bN.equivFun.symm y)) * ι k) s φ
    (Real.exp s * T)⁻¹ • pairHeight π (κ (ExpD ((Real.exp s * T) • v)))
      (coordinateChartPoint p x ι κ ExpN ExpD bN bD k (y, z)) =
        T⁻¹ • (f (flow (z, T)) - f z) := by
  dsimp only
  symm
  apply rescaledMapProfile_increment_eq_pairHeight π p x
    (ι (ExpN (bN.equivFun.symm y))) (ι k) s T
    (fun z => κ (ExpD (bD.equivFun.symm z)))
  rw [exp_basis_horizontal_flow ExpD bD a hm, map_mul]

end PolycyclicRecognition

end

end OAI
