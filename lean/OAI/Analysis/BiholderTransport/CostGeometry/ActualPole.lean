import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates
import OAI.Analysis.BiholderTransport.LinearAlgebra.PrefixActionJets
import OAI.Analysis.BiholderTransport.Contact.EnvelopePole

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.hopfPole_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    hopfLax t u z=u (hopfPole (n := n) t u z)+cost (hopfPole (n := n) t u z) z/t := by
  rw [hdual.1] at hu ⊢
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  have He : hopfPole (n := n) t (cTransform v) z=q.1.1 := by
    change hopfPole (n := n) t (cTransform v) (graphProjection (cTransform v) t q)=q.1.1 at H
    rwa [hq] at H
  rw [He,←hq]
  exact hmtw.hopfLax_graph_value hv ht ht1 q

lemma WeakMTW.prefix_hopfLax_differentiable (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x:M) :
    Differentiable ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) := by
  intro q
  have he := (contMDiff_riemannianExp_fiber (n := n) x (t • q)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) (fun q => t • q) q :=
    (show ContDiffAt ℝ ∞ (fun q : TangentSpace 𝓘(ℝ,Model n) x => t • q) q from by
      fun_prop).contMDiffAt.mdifferentiableAt (by simp)
  exact ((hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _).comp q
    (he.comp q hl)).differentiableAt

lemma WeakMTW.actualPole_supports (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    (ha : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    ∀ᶠ q in 𝓝 p, ∀ᶠ w in 𝓝 q,
      hopfLax t u (riemannianExp x (t • w))≤
        hopfLax t u (riemannianExp x (t • q))+
          prefixAction x t (a q,w)-prefixAction x t (a q,q) := by
  filter_upwards [ha] with q hq
  apply Filter.Eventually.of_forall
  intro w
  have H := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • q))
  rw [←hq] at H
  have Hw := hopfLax_le hu t (riemannianExp x (t • w)) (riemannianExp x (a q))
  dsimp [prefixAction]
  linarith

lemma WeakMTW.actualPole_second_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasFDerivAt (fderiv ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))))
      (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply envelope_pole_second_derivative hC ha ha0
    (Filter.Eventually.of_forall (hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x))
    (hmtw.actualPole_supports hu hv hdual ht ht1 harep)
    (prefixAction_endpoint_hessian hp)
  intro d e
  rw [hC.isSymmSndFDerivAt (by norm_num) |>.eq]
  rw [prefixAction_mixed ht.ne' hp]
  exact congrArg Neg.neg (real_inner_comm d e)

end WeakMTWTransport

end

end OAI
