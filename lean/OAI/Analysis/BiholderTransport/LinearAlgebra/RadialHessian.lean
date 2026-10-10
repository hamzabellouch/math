import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ReverseRegular
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.Volume.ExponentialJacobian

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma exp_reverseRay_line (z : TangentBundle 𝓘(ℝ,Model n) M) (s : ℝ) :
    riemannianExp (reverseRay z).1 ((1-s) • (reverseRay z).2)=
      riemannianExp z.1 (s • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul]
  change (sprayFlow (1-s) (tangentScale (-1) (sprayFlow 1 z))).1=(sprayFlow s z).1
  rw [sprayFlow_scale,←sprayFlow_add]
  change (sprayFlow ((-1)*(1-s)+1) z).1=(sprayFlow s z).1
  congr 2
  ring

lemma normal_log_fderiv_injective {x y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q 0)
    (hqr : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a) :
    Function.Injective (fderiv ℝ q 0) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  apply (injective_iff_map_eq_zero (fderiv ℝ q 0)).mpr
  intro v hv
  have he := (contMDiff_riemannianExp_fiber y (q 0)).mdifferentiableAt (by simp)
  have hD := (he.hasMFDerivAt.comp 0 hq.hasFDerivAt.hasMFDerivAt)
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 0] riemannianExp x := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hV : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v=0 := by
    rw [hE]
    change mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp (n := n) y)
      (q 0) (fderiv ℝ q 0 v)=0
    rw [hv]
    exact (mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp (n := n) y) (q 0)).map_zero
  have hN : ‖mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v‖=0 := by
    rw [hV,norm_zero]
  rw [mfderiv_exp_zero_norm] at hN
  exact norm_eq_zero.mp hN
end RadialHessian
end WeakMTWTransport

end

end

end

end OAI
