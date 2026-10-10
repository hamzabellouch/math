import OAI.Geometry.Relativity.CKS.FoliationCurvatureOperator
import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def nullD (p : MomentumInput) : ℝ := 1+mz p^3*(mc p 4).1

def nullRatio (p : MomentumInput) : ℝ :=
  (1+mz p^3*(mc p 1).1)/(normalizedSpeed p*nullD p)

def lapseResidual (p : MomentumInput) : ℝ :=
  ∑ i, ∑ k, inverse (mq p).1 i k *
    (2*mz p^3*accelerationCoefficient p i*accelerationCoefficient p k-
      (mc p 0).2.2 i k/(1+mz p^3*(mc p 0).1)+
      ∑ a, christoffel (mq p) a i k*accelerationCoefficient p a)

def nullQuadratic (p : MomentumInput) : ℝ :=
  -(tensorPair (mq p) (mX p) (mX p)+
    tensorPair (mq p) (fun i k => (mT p i k).1) (fun i k => (mT p i k).1))/2+
    nullRatio p*tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)-
    covectorPair (mq p) (fun i => (mE p i).1) (fun i => (mE p i).1)

def nullMomentumRegion : Set MomentumInput := {p | p ∈ momentumRegion ∧ nullD p ≠ 0}
lemma nullD_smooth : ContDiff ℝ ∞ nullD := by unfold nullD; fun_prop
lemma nullMomentumRegion_open : IsOpen nullMomentumRegion :=
  momentumRegion_open.inter (isOpen_ne_fun nullD_smooth.continuous continuous_const)
lemma nullRatio_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ nullRatio p := by
  have hs : normalizedSpeed p ≠ 0 := mul_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)) hp.1.2
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => 1+mz p^3*(mc p 1).1) p).div
    (normalizedSpeed_smooth.contDiffAt.mul nullD_smooth.contDiffAt) (mul_ne_zero hs hp.2)
lemma lapseResidual_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ lapseResidual p := by
  unfold lapseResidual
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.add
  · exact (((by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => 2*mz p^3) p).mul
      (accelerationCoefficient_smooth hp i)).mul (accelerationCoefficient_smooth hp k)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => (mc p 0).2.2 i k) p).div
        (by fun_prop) hp.2)
  · apply ContDiffAt.sum; intro a _
    exact (momentChristoffel_smooth hp a i k).mul (accelerationCoefficient_smooth hp a)

lemma momentTensorPair_fields_smooth {p : MomentumInput} (hp : p ∈ momentumRegion)
    {X T : MomentumInput → Mat} (hX : ContDiffAt ℝ ∞ X p) (hT : ContDiffAt ℝ ∞ T p) :
    ContDiffAt ℝ ∞ (fun p => tensorPair (mq p) (X p) (T p)) p := by
  unfold tensorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply ContDiffAt.sum; intro a _
  apply ContDiffAt.sum; intro b _
  exact (((momentInverse_smooth hp i a).mul (momentInverse_smooth hp k b)).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hX i) k)).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hT a) b)
lemma momentCovectorPair_fields_smooth {p : MomentumInput} (hp : p ∈ momentumRegion)
    {E B : MomentumInput → I → ℝ} (hE : ContDiffAt ℝ ∞ E p) (hB : ContDiffAt ℝ ∞ B p) :
    ContDiffAt ℝ ∞ (fun p => covectorPair (mq p) (E p) (B p)) p := by
  unfold covectorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact ((momentInverse_smooth hp i k).mul (contDiffAt_pi.mp hE i)).mul (contDiffAt_pi.mp hB k)
lemma nullQuadratic_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ nullQuadratic p := by
  unfold nullQuadratic
  exact ((((momentTensorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop)).add
    (momentTensorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop))).neg.div_const 2).add
    ((nullRatio_smooth hp).mul (momentTensorPair_smooth hp.1))).sub
    (momentCovectorPair_fields_smooth hp.1 (by fun_prop) (by fun_prop))

abbrev NullInput := MomentumInput × ScalarJet × ℝ
abbrev nP (p : NullInput) := p.1
abbrev nF (p : NullInput) := p.2.1
abbrev nFr (p : NullInput) := p.2.2

def nullResidual (p : NullInput) : ℝ :=
  2*(nFr p-mz (nP p)^3*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)-
  mz (nP p)*(mc (nP p) 4).1*(2-6*mz (nP p)*(nF p).1)/nullD (nP p)-
  mz (nP p)*lapseResidual (nP p)+mz (nP p)^2*nullQuadratic (nP p)-
  nullRatio (nP p)*(covectorDiv (mq (nP p)) (mE (nP p))-
    2*mz (nP p)^3*covectorPair (mq (nP p)) (fun a => (mE (nP p) a).1)
      (accelerationCoefficient (nP p)))

def nullRegion : Set NullInput := nP ⁻¹' nullMomentumRegion
lemma nullRegion_open : IsOpen nullRegion := nullMomentumRegion_open.preimage (by fun_prop)
lemma nullResidual_smooth {p : NullInput} (hp : p ∈ nullRegion) :
    ContDiffAt ℝ ∞ nullResidual p := by
  have hproj : ContDiffAt ℝ ∞ nP p := by fun_prop
  have hD := nullD_smooth.contDiffAt.comp p hproj
  have hR := (nullRatio_smooth hp).comp p hproj
  have hLap := (lapseResidual_smooth hp.1).comp p hproj
  have hQ := (nullQuadratic_smooth hp).comp p hproj
  have hdiv := (momentCovectorDiv_smooth hp.1).comp p hproj
  have hpair : ContDiffAt ℝ ∞ (fun p : NullInput =>
      covectorPair (mq (nP p)) (fun a => (mE (nP p) a).1)
      (accelerationCoefficient (nP p))) p := by
    have h0 := momentCovectorPair_fields_smooth hp.1
      (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => fun a => (mE p a).1) (nP p))
      (contDiffAt_pi.mpr fun a => accelerationCoefficient_smooth hp.1 a)
    exact h0.comp p hproj
  unfold nullResidual
  exact (((((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput =>
    2*(nFr p-mz (nP p)^3*∑ a, (mS (nP p) a).1*(nF p).2.1 a)) p).div hD hp.2).sub
    ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput =>
      mz (nP p)*(mc (nP p) 4).1*(2-6*mz (nP p)*(nF p).1)) p).div hD hp.2)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => mz (nP p)) p).mul hLap)).add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => mz (nP p)^2) p).mul hQ)).sub
    (hR.mul (hdiv.sub ((by fun_prop : ContDiffAt ℝ ∞ (fun p : NullInput => 2*mz (nP p)^3) p).mul hpair)))

end
end CKSAngularGeometry

end

end OAI
