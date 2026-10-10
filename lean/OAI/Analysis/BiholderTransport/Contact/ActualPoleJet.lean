import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeTaylor
import OAI.Analysis.BiholderTransport.CostGeometry.ActualPole
import OAI.Analysis.BiholderTransport.Calculus.PoleJetAlgebra

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

lemma WeakMTW.actualPole_fixed_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    hopfLax t u (riemannianExp x (t • p))=u x+t*(‖p‖^2/2) ∧
    ∀ᶠ q in 𝓝 p, hopfLax t u (riemannianExp x (t • q))≤
      hopfLax t u (riemannianExp x (t • p))+t*(‖q‖^2/2-‖p‖^2/2) := by
  have He := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • p))
  rw [hpole] at He
  have hb : cost x (riemannianExp x (t • p))/t=t*(‖p‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using prefixAction_axis hp
  rw [hb] at He
  refine ⟨He,?_⟩
  filter_upwards [prefixAction_axis_near hp] with q hq
  have H := hopfLax_le hu t (riemannianExp x (t • q)) x
  have hbq : cost x (riemannianExp x (t • q))/t=t*(‖q‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using hq
  rw [hbq] at H
  rw [He]
  linarith

lemma WeakMTW.actualPole_first_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    HasFDerivAt (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) (t • innerSL ℝ p) p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun q => hopfLax t u (riemannianExp x (t • q))
  have hd := hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x p
  have hsup := (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).2
  have hg : HasFDerivAt (fun q : V => f p+t*(‖q‖^2/2-‖p‖^2/2))
      (t • innerSL ℝ p) p := by
    convert! (((half_norm_sq_hasFDerivAt p).sub_const (‖p‖^2/2)).const_smul t).const_add (f p) using 1
  have he := upper_contact_fderiv hd hg.differentiableAt hsup (by simp only [sub_self,mul_zero,add_zero]; rfl)
  exact hd.hasFDerivAt.congr_fderiv (he.trans hg.fderiv)

lemma WeakMTW.actualPole_taylor (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasSecondTaylor (fun h : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • (p+h))))
      (t • innerSL ℝ p) (t • (innerSL ℝ (E := TangentSpace 𝓘(ℝ,Model n) x))-(innerSL ℝ).comp R) ∧
    (∀ d:TangentSpace 𝓘(ℝ,Model n) x, 0 ≤ inner ℝ (R d) d) ∧
    (∀ d e:TangentSpace 𝓘(ℝ,Model n) x, inner ℝ (R d) e=inner ℝ d (R e)) := by
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have H := harep.self_of_nhds
    rw [ha0,riemannianExp_zero] at H
    exact H.symm
  have hD := hmtw.actualPole_second_derivative hu hv hdual ht ht1 hp ha ha0 harep
  have hnear : ∀ᶠ q in 𝓝 p, HasFDerivAt
      (fun w : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • w)))
      (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • w))) q) q :=
    Filter.Eventually.of_forall (fun q =>
      (hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x q).hasFDerivAt)
  have HT := hasSecondTaylor_of_second_derivative hnear hD
  rw [(hmtw.actualPole_first_derivative hu hv hdual ht ht1 hp hpole).fderiv] at HT
  refine ⟨HT,pole_nonneg_of_envelope_taylor HT
    (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).2,?_⟩
  intro d e
  have H := second_derivative_symmetric_of_eventually hnear hD d e
  change t*inner ℝ d e-inner ℝ (R d) e=t*inner ℝ e d-inner ℝ (R e) d at H
  rw [real_inner_comm e d,real_inner_comm d (R e)] at H
  linarith

end WeakMTWTransport

end

end OAI
