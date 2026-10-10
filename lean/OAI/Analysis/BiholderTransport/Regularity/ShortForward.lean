import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.LiftedSections
import OAI.Analysis.BiholderTransport.Coordinates.ChartGradientMap
import OAI.Analysis.BiholderTransport.Calculus.ShortSmoothFamily

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

def shortForward (a : M) (ψ : Model n → ℝ) (q : ℝ×Model n) : Model n :=
  extChartAt 𝓘(ℝ,Model n) a (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2))

def shortEnergy (a : M) (ψ : Model n → ℝ) (y : Model n) : ℝ :=
  fderiv ℝ ψ y ((riemannianCoordinateMetric a y).inverse (fderiv ℝ ψ y))/2

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma shortEnergy_eq_norm {a : M} {y : Model n}
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).target) (ψ : Model n → ℝ) :
    shortEnergy a ψ y=‖chartGradientVector a y (fderiv ℝ ψ y)‖^2/2 := by
  have H := (riemannianCoordinateMetric_isInvertible hy).self_apply_inverse (fderiv ℝ ψ y)
  have He := congrArg (fun L : Model n →L[ℝ] ℝ =>
    L ((riemannianCoordinateMetric a y).inverse (fderiv ℝ ψ y))) H
  rw [riemannianCoordinateMetric_apply,real_inner_self_eq_norm_sq] at He
  exact congrArg (fun t : ℝ => t/2) He.symm

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma shortForward_zero {a : M} {ψ : Model n → ℝ} {y : Model n}
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).target) : shortForward a ψ (0,y)=y := by
  simp only [shortForward,zero_smul,coordinateBackward,map_zero,smul_zero]
  rw [movingNormal_zero hy,(extChartAt 𝓘(ℝ,Model n) a).right_inv hy]

omit [Nonempty M] in
lemma shortForward_action {a : M} {ψ : Model n → ℝ} {q : ℝ×Model n}
    (hq : q.2∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.2 (q.1 • fderiv ℝ ψ q.2)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)) :
    cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)
      (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2))=q.1^2*shortEnergy a ψ q.2 ∧
    HasFDerivAt (chartCost a (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2)))
      (-(q.1 • fderiv ℝ ψ q.2)) q.2 := by
  refine ⟨?_,chartCost_gradient_at_contact hq hp⟩
  rw [coordinateBackward_eq_exp_chartGradient hq,
    cost_minimizingVector (injectivityDomain_subset_minimizingVectors _ hp),shortEnergy_eq_norm hq]
  simp only [chartGradientVector,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
end WeakMTWTransport

end



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
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

def parametricShortForward (a : M) (ψ : P×Model n → ℝ) (q : (P×ℝ)×Model n) : Model n :=
  shortForward a (fun y => ψ (q.1.1,y)) (q.1.2,q.2)

def parametricShortEnergy (a : M) (ψ : P×Model n → ℝ) (q : P×Model n) : ℝ :=
  shortEnergy a (fun y => ψ (q.1,y)) q.2

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [CompleteSpace P] in
lemma parametricShortEnergy_contDiffAt {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ContDiffAt ℝ ∞ (parametricShortEnergy a ψ) (p,x) := by
  have hD := ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ
  have hg := ((contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hx)).comp (f := Prod.snd) (p,x) contDiffAt_snd
  have hi := (riemannianCoordinateMetric_isInvertible hx).contDiffAt_map_inverse.comp
    (f := fun q : P×Model n => riemannianCoordinateMetric a q.2) (p,x) hg
  exact (hD.clm_apply (hi.clm_apply hD)).div_const 2

omit [Nonempty M] [CompleteSpace P] in
lemma parametricShortForward_contDiffAt {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ContDiffAt ℝ ∞ (parametricShortForward a ψ) ((p,0),x) := by
  have hD := ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ
  let A : (P×ℝ)×Model n → (ℝ×Model n×(Model n →L[ℝ] ℝ)) := fun q =>
    (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)
  have hA : ContDiffAt ℝ ∞ A ((p,0),x) :=
    contDiffAt_const.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_fst.snd.smul (hD.comp (f := fun q : (P×ℝ)×Model n => (q.1.1,q.2))
        ((p,0),x) (contDiffAt_fst.fst.prodMk contDiffAt_snd))))
  have hC : ContMDiffAt 𝓘(ℝ,(P×ℝ)×Model n) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a ∘ A) ((p,0),x) :=
    (coordinateBackward_contMDiffAt (q := A ((p,0),x)) hx).comp
      (f := A) ((p,0),x) hA.contMDiffAt
  have he : coordinateBackward a (A ((p,0),x))=(extChartAt 𝓘(ℝ,Model n) a).symm x := by
    simp only [A,coordinateBackward,zero_smul,map_zero,smul_zero,movingNormal_zero hx]
  have hc : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ (extChartAt 𝓘(ℝ,Model n) a)
      (coordinateBackward a (A ((p,0),x))) := by
    rw [he]
    exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hx)
  exact (hc.comp (f := coordinateBackward a ∘ A) ((p,0),x) hC).contDiffAt

omit [Nonempty M] [CompleteSpace P] in
lemma parametricShortForward_regular_near {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∀ᶠ q : (P×ℝ)×Model n in 𝓝 ((p,0),x),
      q.2∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      chartGradientVector a q.2 (q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) ∧
      coordinateBackward a (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        (extChartAt 𝓘(ℝ,Model n) a).source := by
  have hD := (ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ).continuousAt
  let A : (P×ℝ)×Model n → Model n×(Model n →L[ℝ] ℝ) := fun q =>
    (q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)
  have hA : ContinuousAt A ((p,0),x) := continuousAt_snd.prodMk
    (continuousAt_fst.snd.smul (hD.comp (x := ((p,0),x))
      (continuousAt_fst.fst.prodMk continuousAt_snd)))
  have hp : chartGradientVector a (A ((p,0),x)).1 (A ((p,0),x)).2∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm x) := by
    simpa only [A,chartGradientVector,zero_smul,map_zero] using zero_mem_injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm x)
  have ha := hA.eventually (chartGradientVector_regular_near hx hp)
  have hs : ∀ᶠ q : (P×ℝ)×Model n in 𝓝 ((p,0),x),
      q.2∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := ((coordinateBackward_contMDiffAt (q := (-1,A ((p,0),x))) hx).continuousAt.comp
    (x := ((p,0),x)) (continuousAt_const.prodMk hA))
  have he : coordinateBackward a (-1,A ((p,0),x))=(extChartAt 𝓘(ℝ,Model n) a).symm x := by
    simp only [A,coordinateBackward,zero_smul,map_zero,smul_zero,movingNormal_zero hx]
  have hb := hc.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds
    (he.symm ▸ (extChartAt 𝓘(ℝ,Model n) a).map_target hx))
  exact hs.and (ha.and hb)

omit [Nonempty M] in
lemma geometric_parametric_short_family {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ (B : (P×ℝ)×Model n → Model n) (U : (P×ℝ)×Model n → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),parametricShortForward a ψ (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2) ∧
      (∀ q,U q=ψ (q.1.1,B q)+q.1.2*parametricShortEnergy a ψ (q.1.1,B q)) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  apply parametric_smooth_short_action (parametricShortForward_contDiffAt hx hψ) _ hψ
    (parametricShortEnergy_contDiffAt hx hψ)
  filter_upwards [(isOpen_extChartAt_target a).mem_nhds hx] with y hy
  exact shortForward_zero hy

end WeakMTWTransport

end

end OAI
