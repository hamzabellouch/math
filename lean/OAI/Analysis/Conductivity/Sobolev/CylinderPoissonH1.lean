import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CylinderSobolevGraph

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma axialDecayField_smooth (m : ℝ) (a : ℂ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (axialDecayField m a) := by
  unfold axialDecayField
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)).mul contDiff_const

lemma axialDecayField_deriv (m : ℝ) (a : ℂ) :
    deriv (axialDecayField m a)=axialDecayField m (-(m:ℂ)*a) := by
  funext t
  have he : HasDerivAt (fun t : ℝ => (Real.exp (-m*t):ℂ))
      ((Real.exp (-m*t)*(-m):ℝ):ℂ) t := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id t).const_mul (-m)).exp).ofReal_comp
  have H := (he.mul_const a).deriv
  change deriv (fun t : ℝ => (Real.exp (-m*t):ℂ)*a) t=_
  rw [H]
  simp only [axialDecayField,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

lemma axialDecayField_smoothLp (m R : ℝ) (a : ℂ) :
    smoothFiniteAxisLp (axialDecayField_smooth m a).continuous R=finiteDecayLp m R a := by
  apply Lp.ext
  exact (smoothFiniteAxisLp_ae (axialDecayField_smooth m a).continuous R).trans
    (finiteDecayLp_ae m R a).symm

lemma axialDecayField_derivLp (m R : ℝ) (a : ℂ) :
    smoothFiniteAxisLp ((axialDecayField_smooth m a).continuous_deriv (by simp)) R=
      finiteDecayLp m R (-(m:ℂ)*a) := by
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae ((axialDecayField_smooth m a).continuous_deriv (by simp)) R,
    finiteDecayLp_ae m R (-(m:ℂ)*a)] with t ht hu
  rw [ht,hu,axialDecayField_deriv]

lemma endPoissonModeJet_smooth (s : Fin 3 → ℝ) (R : ℝ) (h : TorusModes) (a : ℂ) :
    endPoissonModeJet s R h a=
      smoothCylinderModeJet (axialDecayField_smooth (torusRate s h) a) R h := by
  apply PiLp.ext
  intro j
  fin_cases j
  · change cylinderMode _ _ (finiteDecayLp _ _ a)=cylinderMode _ _ (smoothFiniteAxisLp _ _)
    rw [axialDecayField_smoothLp]
  · change cylinderMode _ _ (finiteDecayLp _ _ (-(torusRate s h:ℂ)*a))=
      cylinderMode _ _ (smoothFiniteAxisLp _ _)
    rw [axialDecayField_derivLp]
  · change cylinderMode _ _ (finiteDecayLp _ _ ((Complex.I*(h 0:ℂ))*a))=
      cylinderMode _ _ ((Complex.I*(h 0:ℂ))•smoothFiniteAxisLp _ _)
    rw [axialDecayField_smoothLp,finiteDecayLp_smul]
  · change cylinderMode _ _ (finiteDecayLp _ _ ((Complex.I*(h 1:ℂ))*a))=
      cylinderMode _ _ ((Complex.I*(h 1:ℂ))•smoothFiniteAxisLp _ _)
    rw [axialDecayField_smoothLp,finiteDecayLp_smul]

lemma smoothCylinderModeJet_mem_H1 {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) : smoothCylinderModeJet hq R h∈cylinderH1Space R := by
  apply Submodule.le_topologicalClosure
  refine ⟨Finsupp.single h (⟨q,hq⟩ : smoothComplexAxis),?_⟩
  rw [cylinderPolynomialJetL,Finsupp.lsum_single]
  exact cylinderJetMode_smooth hq R h

theorem endPoissonJet_mem_cylinderH1 (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR f∈cylinderH1Space R := by
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (endPoissonJet_hasSum s hs R hR f)
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  rw [endPoissonModeJet_smooth]
  exact smoothCylinderModeJet_mem_H1 _ R h

end ScalarConductivity

end

end OAI
