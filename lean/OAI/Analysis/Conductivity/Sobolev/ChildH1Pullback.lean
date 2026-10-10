import Mathlib
import OAI.Analysis.Conductivity.Variational.WholeBallJetFormula
import OAI.Analysis.Conductivity.Branching.ChildTransportFormula

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma sourceChildEuclidean_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceChildEuclidean σ : R3 → R3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    ((sourceChildCoordinates_contDiff σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma sourceChildEuclidean_gradient (σ : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (x : R3) (i : Fin 3) :
    gradient (f ∘ sourceChildEuclidean σ) x i=
      sourceScale*gradient f (sourceChildEuclidean σ x) (childAxis i) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hD := E.symm.hasFDerivAt.comp (E x) (sourceChildCoordinates_hasFDeriv σ (E x))
  have hC := (hf.differentiable (by simp) (sourceChildEuclidean σ x)).hasFDerivAt.comp x
    (hD.comp x E.hasFDerivAt)
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  have hj : E.symm.toContinuousLinearMap (Pi.single (childAxis i) 1)=EuclideanSpace.single (childAxis i) 1 := rfl
  rw [gradient_apply_single,gradient_apply_single]
  rw [hC.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,hi,sourceChildDerivative_single,map_smul,hj,map_smul,smul_eq_mul]

def childPullbackComponentCLM (k : Fin 2) (i : Fin 4) : JetSpace →L[ℝ] Lp ℝ 2 (volume : Measure Coord3) :=
  Fin.cases ((sourceChildPullbackCLM (actualChildSign k)).comp (ballWholePiComponentCLM 0))
    (fun j => sourceScale • ((sourceChildPullbackCLM (actualChildSign k)).comp
      (ballWholePiComponentCLM (childAxis j).succ))) i

def childPullbackJetCLM (k : Fin 2) : JetSpace →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childPullbackComponentCLM k))

lemma childPullbackComponentCLM_ae (k : Fin 2) (z : JetSpace) (i : Fin 4) :
    childPullbackComponentCLM k i z=ᵐ[volume] fun y => Fin.cases
      (if WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈ball then
        z (WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)) 0 else 0)
      (fun j => sourceScale*(if WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)∈ball then
        z (WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) y)) (childAxis j).succ else 0)) i := by
  have he (i : Fin 4) := ballWholePiComponentCLM_ae_of_ae i z
    (fun y => z (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  have hp (i : Fin 4) := (sourceChildPullbackCLM_ae (actualChildSign k) (ballWholePiComponentCLM i z)).trans
    ((sourceChildCoordinates_quasi _).ae_eq_comp (he i))
  refine Fin.cases (hp 0) (fun j => ?_) i
  apply (Lp.coeFn_smul _ _).trans
  filter_upwards [hp (childAxis j).succ] with y hy
  exact congrArg (fun t : ℝ => sourceScale*t) hy

lemma childPullbackJetCLM_ae (k : Fin 2) (z : JetSpace) :
    childPullbackJetCLM k z=ᵐ[ballMeasure] fun x => WithLp.toLp 2 (Fin.cases
      (z (sourceChildEuclidean (actualChildSign k) x) 0)
      (fun j => sourceScale*z (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ)) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childPullbackComponentCLM_ae k z i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childPullbackComponentCLM k i z),ae_all_iff.mpr hi,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hi hxb
  change physicalFourJetCLM (fun i => childPullbackComponentCLM k i z) x=_
  rw [hx]
  have hb : sourceChildEuclidean (actualChildSign k) x∈ball := sourceChildEuclidean_ball k ⟨x,hxb,rfl⟩
  ext i
  have hh := hi i
  change childPullbackComponentCLM k i z (WithLp.ofLp x)=Fin.cases
    (if sourceChildEuclidean (actualChildSign k) x∈ball then z (sourceChildEuclidean (actualChildSign k) x) 0 else 0)
    (fun j => sourceScale*(if sourceChildEuclidean (actualChildSign k) x∈ball then
      z (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ else 0)) i at hh
  simpa only [ite_eq_left hb] using hh

lemma sourceChildEuclidean_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean σ) volume volume :=
  (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.comp
    ((sourceChildCoordinates_quasi σ).comp (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving)

lemma sourceChildEuclidean_ball_quasi (k : Fin 2) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean (actualChildSign k)) ballMeasure ballMeasure := by
  exact (sourceChildEuclidean_quasi _).restrict fun x hx => sourceChildEuclidean_ball k ⟨x,hx,rfl⟩

lemma childPullbackJetCLM_smooth (k : Fin 2) (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    childPullbackJetCLM k (smoothH1 f hf).val=
      (smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _))).val := by
  apply Lp.ext
  have hh := (sourceChildEuclidean_ball_quasi k).ae_eq_comp (smoothJet_memLp hf).coeFn_toLp
  filter_upwards [childPullbackJetCLM_ae k (smoothH1 f hf).val,hh,
    (smoothJet_memLp (hf.comp (sourceChildEuclidean_contDiff (actualChildSign k)))).coeFn_toLp] with x hx hh hg
  change (smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _))).val x=_ at hg
  rw [hx,hg]
  ext i
  cases i using Fin.cases with
  | zero =>
    change (smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x) 0=f (sourceChildEuclidean (actualChildSign k) x)
    exact congrArg (fun v : JetFiber => v 0) hh
  | succ j =>
    change sourceScale*(smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x) (childAxis j).succ=_
    change (smoothH1 f hf).val (sourceChildEuclidean (actualChildSign k) x)=_ at hh
    rw [hh]
    exact (sourceChildEuclidean_gradient _ hf x j).symm

lemma childPullbackJetCLM_H1 (k : Fin 2) {z : JetSpace} (hz : z∈H1Space) :
    childPullbackJetCLM k z∈H1Space := by
  let T := H1Space.comap (childPullbackJetCLM k).toLinearMap
  have ht : IsClosed (T : Set JetSpace) := H1_isClosed.preimage (childPullbackJetCLM k).continuous
  have hs : Submodule.span ℝ smoothJets≤T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f,hf,hm,rfl⟩
    have he : hm.toLp (smoothJet f)=(smoothH1 f hf).val := by
      apply Lp.ext; exact hm.coeFn_toLp.trans (smoothJet_memLp hf).coeFn_toLp.symm
    change childPullbackJetCLM k (hm.toLp (smoothJet f))∈H1Space
    rw [he,childPullbackJetCLM_smooth k f hf]
    exact (smoothH1 _ _).property
  exact (Submodule.topologicalClosure_minimal _ hs ht) hz

def childH1Pullback (k : Fin 2) : H1 →L[ℝ] H1 :=
  ((childPullbackJetCLM k).comp H1Space.subtypeL).codRestrict H1Space
    (fun u => childPullbackJetCLM_H1 k u.property)

lemma childH1Pullback_smooth (k : Fin 2) (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    childH1Pullback k (smoothH1 f hf)=
      smoothH1 (f ∘ sourceChildEuclidean (actualChildSign k)) (hf.comp (sourceChildEuclidean_contDiff _)) :=
  Subtype.ext (childPullbackJetCLM_smooth k f hf)

end ScalarConductivity

end
end

end OAI
