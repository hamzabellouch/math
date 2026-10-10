import OAI.Analysis.Mahler.BoundaryJet
import OAI.Analysis.Mahler.SphereNormalization
import OAI.Analysis.Mahler.NormExteriorPower
import OAI.Analysis.Mahler.LogUniform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology BigOperators

namespace Mahler

/-- Reassociate the two leading real slots to preserve the interleaved order. -/
def sphereFrameSlots (k : ℕ) :
    Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k) ≃ WedgePowerSlots (k+1) where
  toFun s := match s with
    | .inl _ => .inl 0
    | .inr (.inl _) => .inl 1
    | .inr (.inr j) => .inr j
  invFun s := match s with
    | .inl i => if i = 0 then .inl 0 else .inr (.inl 0)
    | .inr j => .inr (.inr j)
  left_inv := by intro s; rcases s with i | (i | j) <;> simp; all_goals fin_cases i ; rfl
  right_inv := by intro s; rcases s with i | j; fin_cases i <;> rfl; rfl

/-- The positive frame is exactly x_1,y_1,...,x_n,y_n. -/
noncomputable def sphereFluxFrame (k : ℕ) :
    Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k) → ComplexEuclidean (k+1) :=
  interleavedBasis ∘ sphereFrameSlots k

lemma sphereFluxFrame_positive (k : ℕ) :
    (interleavedVolume (k+1)).domDomCongr (sphereFrameSlots k).symm (sphereFluxFrame k) = 1 := by
  convert interleavedVolume_basis (k+1) using 1
  simp [AlternatingMap.domDomCongr_apply, sphereFluxFrame, Function.comp_def]

/-- The real metric dual of the outward unit normal, with complex-valued output. -/
noncomputable def sphereNormal {n : ℕ} (z : ComplexEuclidean n) :
    ComplexEuclidean n [⋀^Fin 1]→ₗ[ℝ] ℂ :=
  (oneForm (fun _ => Complex.ofRealCLM.comp (innerSL ℝ z)) z).toAlternatingMap

/-- Surface density of a top degree form: evaluate normal^flat wedge omega
on the positively oriented Euclidean coordinate frame. -/
noncomputable def sphereDensity (k : ℕ) (z : ComplexEuclidean (k+1))
    (a : ComplexEuclidean (k+1) [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ) : ℂ :=
  wedge (sphereNormal z) a (sphereFluxFrame k)

noncomputable def sphereJetDensity (k : ℕ)
    (p : ComplexEuclidean (k+1) × RealComplexTwoJet (ComplexEuclidean (k+1))) : ℂ :=
  sphereDensity k p.1 (boundaryJet p.2 k)

lemma continuous_sphereJetDensity (k : ℕ) : Continuous (sphereJetDensity k) := by
  apply continuous_wedge_eval
  · intro v
    change Continuous (fun p : ComplexEuclidean (k+1) × RealComplexTwoJet _ =>
      (inner ℝ p.1 (v 0) : ℂ))
    exact Complex.continuous_ofReal.comp (continuous_fst.inner continuous_const)
  · intro v
    exact (continuous_boundaryJet_eval k v).comp continuous_snd

/-- Actual complex Bochner integral against Euclidean unit-sphere area. -/
noncomputable def unitSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) : ℂ :=
  ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
    sphereDensity k z (boundaryForm u k z) ∂sphereArea (k+1)

/-- Radius-r sphere flux in the positive radial parametrization. The surface
Jacobian is r^(2k+1); the normal is z, directed out of the ball. -/
noncomputable def smallSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) (r : ℝ) : ℂ :=
  ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
    (r : ℂ)^(2*k+1) * sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))
      ∂sphereArea (k+1)

lemma boundaryForm_pullback_scale {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (u : E → ℂ) (k : ℕ) (x : E) (r : ℝ) :
    (boundaryForm u k x).compLinearMap (realDilation r).toLinearMap =
      ((r : ℂ)^(2*k+1)) • boundaryForm u k x := by
  ext v
  change boundaryForm u k x (fun i => r • v i) = _
  rw [AlternatingMap.map_smul_univ]
  simp [AlternatingMap.smul_apply, smul_eq_mul, Complex.real_smul,
    Fintype.card_sum, card_wedgePowerSlots, add_comm]

/-- Pointwise pullback proves equality of the actual sphere integrals. -/
theorem smallSphereFlux_eq_unit {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ} {r : ℝ}
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 u (r • (z : ComplexEuclidean (k+1)))) (c : ℂ) :
    smallSphereFlux k u r = unitSphereFlux k (fun y => u (r • y) - c) := by
  apply integral_congr_ae
  filter_upwards [] with z
  rw [boundaryForm_dilation (hu z) c k, boundaryForm_pullback_scale]
  unfold sphereDensity
  rw [wedge_smul_right]
  rfl

end Mahler

end OAI
