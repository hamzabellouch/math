import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexFactorLocalChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegratedCartanRotations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealTorusSmoothRepresentation

namespace OAI

/-! # Joint smoothness of the compact action along a smooth representation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
  (hβ : ∀ z (x : T.kernelIdeal) d,
    β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)
  (q : G → realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
  (R : G → E →L[ℝ] E)
  (hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞ R)
  (hReq : ∀ g x, R g x = realTorusOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H (q g) x)

include hβ hReq in
theorem action_factor_eq (g : G) (x : T.kernelIdeal) (d : F.D.carrier) :
    β (q g) (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.kernelParameter (R g x.1))) * F.inclusionD d := by
  have he : F.kernelParameter (R g x.1) = F.N.equiv (T.nilradicalRotation H (q g) x) := by
    change F.N.equiv (T.kernelComponent H (R g x.1)) = _
    exact (congrArg (fun y : E => F.N.equiv (T.kernelComponent H y)) (hReq g x.1)).trans
      (congrArg F.N.equiv (T.kernelComponent_of_mem H (T.nilradicalRotation H (q g) x)))
  calc
    _ = F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H (q g) x))) *
        F.inclusionD d := hβ (q g) x d
    _ = _ := congrArg (fun v => F.inclusionN (F.ExpN v) * F.inclusionD d) he.symm

include hExp hβ hR hReq in
theorem contMDiff_action_factor (x : T.kernelIdeal) (d : F.D.carrier) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞
      (fun g => β (q g) (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d)) := by
  have he : (fun g => β (q g) (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d)) =
      (fun g => F.inclusionN (F.ExpN (F.kernelParameter (R g x.1))) * F.inclusionD d) :=
    funext (fun g => F.action_factor_eq β hβ q R hReq g x d)
  rw [he]
  let xE : E := x.1
  have hc : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun _ : G => xE) :=
    contMDiff_const (M := G) (M' := E) (c := xE)
  have hr := hR.clm_apply hc
  have hn := F.contMDiff_expN.comp (F.kernelParameter.contDiff.contMDiff.comp hr)
  exact ((F.contMDiff_inclusionN hExp).comp hn).mul contMDiff_const

include hExp hβ hR hReq in
theorem contMDiff_action_fixed (g₀ : G) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun g => β (q g) g₀) := by
  let p : F.N.carrier × F.D.carrier := (F.surjective g₀).choose
  have hp : F.inclusionN p.1 * F.inclusionD p.2 = g₀ := (F.surjective g₀).choose_spec
  let x : T.kernelIdeal := (F.expN_surjective p.1).choose
  have hx : F.ExpN (F.N.equiv x) = p.1 := (F.expN_surjective p.1).choose_spec
  have he : F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD p.2 = g₀ := by
    rw [hx]
    exact hp
  have hh := F.contMDiff_action_factor hExp β hβ q R hR hReq x p.2
  have he' : (fun g => β (q g) (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD p.2)) =
      (fun g => β (q g) g₀) := funext (fun g => congrArg (fun u => β (q g) u) he)
  exact he' ▸ hh

include hExp hβ hR hReq in
theorem contMDiff_action_parameters :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : G × E => β (q p.1) (F.factorParameter p.2)) := by
  let k : E →L[ℝ] E :=
    (show E →ₗ[ℝ] E from T.kernelIdeal.incl.toLinearMap.comp (T.kernelComponent H)).toContinuousLinearMap
  have he : (fun p : G × E => β (q p.1) (F.factorParameter p.2)) =
      (fun p => F.inclusionN (F.ExpN (F.kernelParameter (R p.1 (k p.2)))) *
        F.inclusionD (F.ExpD (F.cartanParameter p.2))) := by
    funext p
    exact F.action_factor_eq β hβ q R hReq p.1 (T.kernelComponent H p.2)
      (F.ExpD (F.cartanParameter p.2))
  rw [he]
  have hr := (hR.comp contMDiff_fst).clm_apply (k.contDiff.contMDiff.comp contMDiff_snd)
  have hn := F.contMDiff_expN.comp (F.kernelParameter.contDiff.contMDiff.comp hr)
  have hc : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,F.D.modelSpace)) ∞
      (fun p : G × E => F.cartanParameter p.2) :=
    F.cartanParameter.contDiff.contMDiff.comp contMDiff_snd
  have hd := F.contMDiff_expD.comp hc
  exact ((F.contMDiff_inclusionN hExp).comp hn).mul ((F.contMDiff_inclusionD hExp).comp hd)

include hExp hβ hR hReq in
theorem contMDiff_translated_action_parameters (c : G) :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun z : G × E => β (q z.1) (c * F.factorParameter z.2)) := by
  have hh := ((F.contMDiff_action_fixed hExp β hβ q R hR hReq c).comp
    (contMDiff_fst : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (Prod.fst : G × E → G))).mul
    (F.contMDiff_action_parameters hExp β hβ q R hR hReq)
  exact hh.congr (fun z => (β (q z.1)).map_mul c (F.factorParameter z.2))

include hExp hβ hR hReq in
theorem contMDiffAt_translated_action (g c : G) :
    ContMDiffAt ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun z : G × G => β (q z.1) (c * z.2)) (g,1) := by
  have hp := F.contMDiff_translated_action_parameters hExp β hβ q R hR hReq c
  have hh := contMDiffAt_from_right_parameters
    (f := fun z : G × G => β (q z.1) (c * z.2)) (w₀ := g)
    (d := ContinuousLinearEquiv.refl ℝ E)
    (F.contMDiff_factorParameter hExp).contMDiffAt
    (F.hasMFDerivAt_factorParameter hExp) (hp.contMDiffAt (x := (g,0)))
  simpa only [F.factorParameter_zero] using hh

include hExp hβ hR hReq in
theorem contMDiff_action :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : G × G => β (q p.1) p.2) := by
  apply contMDiff_of_smooth_mul_right
  intro g c
  exact F.contMDiffAt_translated_action hExp β hβ q R hR hReq g c

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
