import OAI.Geometry.Relativity.CKS.FoliationCurvatureOperator
import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma covectorDiv_rescale (q : Jet) (E : CovectorJet) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    covectorDiv (rescale c q) (d • E) = (d/c)*covectorDiv q E := by
  simp only [covectorDiv,inverse_rescale c q hc,christoffel_rescale c q hc,
    Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma tensorDiv_rescale (q : Jet) (T : CovariantTensorJet) {c : ℝ} (hc : c ≠ 0) (d : ℝ) (a : I) :
    tensorDiv (rescale c q) (d • T) a = (d/c)*tensorDiv q T a := by
  simp only [tensorDiv,inverse_rescale c q hc,christoffel_rescale c q hc,
    Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma covectorPair_rescale (q : Jet) (E B : I → ℝ) {c : ℝ} (hc : c ≠ 0) (d e : ℝ) :
    covectorPair (rescale c q) (d • E) (e • B) = (d*e/c)*covectorPair q E B := by
  simp only [covectorPair,inverse_rescale c q hc,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma tensorPair_rescale (q : Jet) (X T : Mat) {c : ℝ} (hc : c ≠ 0) (d e : ℝ) :
    tensorPair (rescale c q) (d • X) (e • T) = (d*e/c^2)*tensorPair q X T := by
  simp only [tensorPair,inverse_rescale c q hc,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  ring
lemma covectorLie_smul (S E : CovectorJet) (c d : ℝ) (a : I) :
    covectorLie (c • S) (d • E) a = c*d*covectorLie S E a := by
  simp only [covectorLie,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Fin.sum_univ_two]
  ring

def physicalLJet (p : MomentumInput) : ScalarJet := constantJet (1+mw p*mz p^2)+mz p^3 • mc p 2
def physicalTJet (p : MomentumInput) : ScalarJet := constantJet 1+mz p^3 • mc p 1

def coordinateQ (p : MomentumInput) : ℝ :=
  normalMomentum (rescale (1/mz p^2) (mq p)) (normalizedMean p)
    (physicalLJet p).1 (physicalTJet p).1
    (2*normalizedSpeed p*mz p^3*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a))
    (mz p • mX p) (mz p • ((fun i k => (mT p i k).1) : Mat)) (mz p^2 • mE p)
    (mz p^3 • accelerationCoefficient p)

def coordinateZ (p : MomentumInput) (a : I) : ℝ :=
  angularMomentum (rescale (1/mz p^2) (mq p)) (normalizedMean p) (normalizedSpeed p/mz p)
    (physicalLJet p) (physicalTJet p) (mz p^5 • mS p) (mz p^2 • mE p)
    (mz p • mT p) (mz p^3 • mEr p) (mz p^3 • accelerationCoefficient p) a

theorem coordinateQ_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    coordinateQ p = normalizedMean p*mw p*mz p^2+mz p^3*normalResidual p := by
  have hc : 1/mz p^2 ≠ 0 := one_div_ne_zero (pow_ne_zero _ hz)
  unfold coordinateQ normalMomentum
  erw [tensorPair_rescale _ _ _ hc,covectorDiv_rescale _ _ hc]
  have hE : (fun a => ((mz p^2 • mE p) a).1) = mz p^2 • (fun a => (mE p a).1) := rfl
  rw [hE,covectorPair_rescale _ _ _ hc]
  simp only [physicalLJet,physicalTJet,constantJet,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
  unfold normalResidual
  field_simp
  ring

theorem coordinateZ_factor {p : MomentumInput} (hz : mz p ≠ 0) (a : I) :
    coordinateZ p a = mz p^2*angularResidual p a := by
  have hc : 1/mz p^2 ≠ 0 := one_div_ne_zero (pow_ne_zero _ hz)
  unfold coordinateZ angularMomentum
  rw [covectorLie_smul,tensorDiv_rescale _ _ hc]
  simp only [inverse_rescale _ _ hc,physicalLJet,physicalTJet,constantJet,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Pi.add_apply,
    Pi.zero_apply,smul_eq_mul,zero_add]
  unfold angularResidual
  simp only [Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
