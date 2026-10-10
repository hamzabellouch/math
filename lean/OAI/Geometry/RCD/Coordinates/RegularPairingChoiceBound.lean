import OAI.Geometry.RCD.Coordinates.RegularPairingShiftedBound
import OAI.Geometry.RCD.Coordinates.RegularHessianCore

namespace OAI

/-! # The shifted estimate on every Dirichlet test

The finite regular-family estimate applies to the actual dense core of a
local Hessian pairing, and continuity then gives the full Dirichlet bound.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_pairing_shifted_bound_any_core {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (p : X) {R : ℝ} (hR : 0<R)
    (df : SobolevSpace (hausdorff n X) hX.quadratic) (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (A : ℝ≥0) (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    (c : ℝ) (hc : SobolevSpace.toLp (hausdorff n X) hX.quadratic df
      =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => c)
    {J : ℝ} (hJK : J≤K)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure))
    {t : ℝ} (ht : t≤R)
    (d : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p t) f.val c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p t) a.val d)
    (G : LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) f.val a.val)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t), localGamma (hausdorff n X) hX.quadratic a.val a.val x≤B) :
    ∀ (b : ℝ) (φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p t)),
      (G.hessian φ-b*energyForm (hausdorff n X) hX.quadratic a.val φ.val)^2≤
        (B*(σ.real (ball p t)-(2*b*c-(n:ℝ)*b^2)*(hausdorff n X).real (ball p t)))*
          energyForm (hausdorff n X) hX.quadratic φ.val φ.val := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨H,hcore,_,hess⟩ := hX.hessian_pairing_regular_core hn p isOpen_ball f a c d hf ha G
  have hmem (φ : H.core) : φ.val.val∈compactLaplacianCore μ hQ univ := by
    have hp : φ.val∈regularDirichletCore μ hQ (ball p t) := by
      rw [← hcore]
      exact φ.property
    change φ.val.val∈compactLaplacianCore μ hQ (ball p t) at hp
    obtain ⟨⟨v,L,hv,hvc,_,hrep⟩,hlap⟩ := hp
    exact ⟨⟨v,L,hv,hvc,subset_univ _,hrep⟩,hlap⟩
  have hh := hX.regular_pairing_shifted_bound hn hscalar f a p hR df qf hqf A hdf hsf c hc
    hJK F₀ σ hF₀ hσ ht H hmem B hB hgrad
  simpa only [hess] using hh

end RegularPointCoordinates

end

end OAI
