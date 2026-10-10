import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingLocal

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {E : ∀ p : A.centers, ParametrixData J α ht p.val}
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
  {r ρ : ℝ} {hr : 0 < r} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD r hr)
  (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
attribute [local irreducible] framePairing

include hE in
lemma actual_gram_eq_of_smooth_tests (T : ℝ) (hT : 0 ≤ T)
    (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (htest : ∀ a b : PreL2 A J α hs ht true,
      (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, (framePairing A J α ht E b.val x
        (K x y (frameEncode J α ht A E y (a.val y))) +
        B.pairingGammaTail T hT r a b x y) ∂geometricVolume A J α ∂geometricVolume A J α)
    (a b : PreL2 A J α hs ht true) (x y : X) :
    ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫ =
      framePairing A J α ht E b.val x (K x y (frameEncode J α ht A E y (a.val y))) +
        B.pairingGammaTail T hT r a b x y := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  let F : X → X → ℝ := fun x y => ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
  let G : X → X → ℝ := fun x y =>
    framePairing A J α ht E b.val x (K x y (frameEncode J α ht A E y (a.val y))) +
      B.pairingGammaTail T hT r a b x y
  have hF : Continuous (fun p : X × X => F p.1 p.2) :=
    ((C.pairingEvaluationVector_continuous b).comp continuous_fst).inner
      ((C.pairingEvaluationVector_continuous a).comp continuous_snd)
  have hG : Continuous (fun p : X × X => G p.1 p.2) :=
    (frame_kernel_pairing_continuous A J α hs ht E hE K hK b.val a.val b.property a.property).add
      (B.pairingGammaTail_continuous T hT r a b)
  have hlocal (φ ψ : X → ℝ) (hφ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ)
      (hψ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ) :
      (∫ x, ∫ y, φ x*ψ y*F x y ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, φ x*ψ y*G x y ∂geometricVolume A J α ∂geometricVolume A J α := by
    let a' : PreL2 A J α hs ht true := ⟨fun y => ψ y • a.val y,Smooth.fun_smul hψ a.property⟩
    let b' : PreL2 A J α hs ht true := ⟨fun x => φ x • b.val x,Smooth.fun_smul hφ b.property⟩
    have heF (x y : X) : ⟪C.pairingEvaluationVector b' x,C.pairingEvaluationVector a' y⟫ =
        φ x*ψ y*F x y := by
      rw [C.pairingEvaluationVector_smul_of b' b x (φ x) rfl,
        C.pairingEvaluationVector_smul_of a' a y (ψ y) rfl,
        real_inner_smul_left,real_inner_smul_right,mul_assoc]
    have heK (x y : X) : framePairing A J α ht E b'.val x
        (K x y (frameEncode J α ht A E y (a'.val y))) =
        φ x*ψ y*framePairing A J α ht E b.val x
          (K x y (frameEncode J α ht A E y (a.val y))) := by
      change framePairing A J α ht E (fun x => φ x • b.val x) x
        (K x y (frameEncode J α ht A E y (ψ y • a.val y))) = _
      erw [framePairing_fun_smul,map_smul,map_smul,map_smul]
      simp only [smul_eq_mul]
      ring
    have heG (x y : X) : framePairing A J α ht E b'.val x
        (K x y (frameEncode J α ht A E y (a'.val y))) + B.pairingGammaTail T hT r a' b' x y =
        φ x*ψ y*G x y := by
      rw [heK,B.pairingGammaTail_smul_of T hT r a a' b b' x y (ψ y) (φ x) rfl rfl]
      exact (mul_add _ _ _).symm
    simpa only [heF,heG] using htest a' b'
  apply le_antisymm
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) F G hF hG
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).le) x y
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) G F hG hF
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).ge) x y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
