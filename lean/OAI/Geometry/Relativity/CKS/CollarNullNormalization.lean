import OAI.Geometry.Relativity.CKS.CollarMomentumNormalization
import OAI.Geometry.Relativity.CKS.CollarNullMap

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma lapseResidual_factor {p : MomentumInput} (_hp : p ∈ momentumRegion) :
    lapseLaplacian (mq p) (constantJet 1+mz p^3 • mc p 0) = mz p^3*lapseResidual p := by
  simp only [lapseLaplacian,lapseResidual,accelerationCoefficient,constantJet,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.zero_apply,Pi.add_apply,
    Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,zero_add,Fin.sum_univ_two]
  field_simp

def physicalNullQuadratic (p : MomentumInput) : ℝ :=
  -(tensorPair (rescale (1/mz p^2) (mq p)) (mz p • mX p) (mz p • mX p)+
    tensorPair (rescale (1/mz p^2) (mq p))
      (mz p • ((fun i k => (mT p i k).1) : Mat))
      (mz p • ((fun i k => (mT p i k).1) : Mat)))/2+
  nullRatio p*tensorPair (rescale (1/mz p^2) (mq p))
    (mz p • mX p) (mz p • ((fun i k => (mT p i k).1) : Mat))-
  covectorPair (rescale (1/mz p^2) (mq p))
    (mz p^2 • (fun a => (mE p a).1)) (mz p^2 • (fun a => (mE p a).1))

def physicalNullEta (p : MomentumInput) : ℝ :=
  covectorDiv (rescale (1/mz p^2) (mq p)) (mz p^2 • mE p)-
    2*covectorPair (rescale (1/mz p^2) (mq p))
      (mz p^2 • (fun a => (mE p a).1)) (mz p^3 • accelerationCoefficient p)

lemma radius_ratios {z : ℝ} (hz : z ≠ 0) :
    z*z/(1/z^2)^2=z^6 ∧ z^2*z^2/(1/z^2)=z^6 ∧
      z^2/(1/z^2)=z^4 ∧ z^2*z^3/(1/z^2)=z^7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp

lemma quadratic_rescale (q : Jet) (X T : Mat) (E : I → ℝ) (a z : ℝ) (hz : z ≠ 0) :
    -(tensorPair (rescale (1/z^2) q) (z • X) (z • X)+
      tensorPair (rescale (1/z^2) q) (z • T) (z • T))/2+
      a*tensorPair (rescale (1/z^2) q) (z • X) (z • T)-
      covectorPair (rescale (1/z^2) q) (z^2 • E) (z^2 • E) =
    z^6*(-(tensorPair q X X+tensorPair q T T)/2+a*tensorPair q X T-covectorPair q E E) := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  rw [tensorPair_rescale q X X hc,tensorPair_rescale q T T hc,
    tensorPair_rescale q X T hc,covectorPair_rescale q E E hc]
  rw [(radius_ratios hz).1,(radius_ratios hz).2.1]
  ring

lemma physicalNullQuadratic_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    physicalNullQuadratic p = mz p^6*nullQuadratic p := by
  exact quadratic_rescale (mq p) (mX p) (fun i k => (mT p i k).1)
    (fun a => (mE p a).1) (nullRatio p) (mz p) hz
lemma physicalNullEta_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    physicalNullEta p = mz p^4*(covectorDiv (mq p) (mE p)-
      2*mz p^3*covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)) := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  unfold physicalNullEta
  erw [covectorDiv_rescale _ _ hc,covectorPair_rescale _ _ _ hc]
  rw [(radius_ratios hz).2.2.1,(radius_ratios hz).2.2.2]
  ring

def coordinateSmallNull (p : NullInput) (r : ℝ) : ℝ :=
  2*(mw (nP p)/(r*Real.sqrt r)+mz (nP p)^2*nFr p-
    mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2+
  (scalarCurvature (rescale (1/mz (nP p)^2) (mq (nP p)))/2-mz (nP p)^2)+
  (1/nullD (nP p)-1)*(2-6*mz (nP p)*(nF p).1)*mz (nP p)^2-
  lapseLaplacian (rescale (1/mz (nP p)^2) (mq (nP p)))
    (constantJet 1+mz (nP p)^3 • mc (nP p) 0)+
  physicalNullQuadratic (nP p)-nullRatio (nP p)*physicalNullEta (nP p)

lemma null_mass_algebra (z w r s Fr SF F D : ℝ) (hd : 1+z^3*D ≠ 0) :
    2*(w/(r*s)+z^2*Fr-z^5*SF)/(1+z^3*D)*z^2+
      (1/(1+z^3*D)-1)*(2-6*z*F)*z^2 =
    2*w/(r*s)/(1+z^3*D)*z^2+
      z^4*(2*(Fr-z^3*SF)/(1+z^3*D)-z*D*(2-6*z*F)/(1+z^3*D)) := by
  field_simp
  ring

lemma coordinateSmallNull_factor_z {p : NullInput} (r : ℝ)
    (hz : mz (nP p) ≠ 0) (hp : p ∈ nullRegion) :
    coordinateSmallNull p r =
      2*mw (nP p)/(r*Real.sqrt r)/nullD (nP p)*mz (nP p)^2+
      (scalarCurvature (mq (nP p))/2-1)*mz (nP p)^2+
      mz (nP p)^4*nullResidual p := by
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  have hm := null_mass_algebra (mz (nP p)) (mw (nP p)) r (Real.sqrt r) (nFr p)
    (∑ a, (mS (nP p) a).1*(nF p).2.1 a) (nF p).1 (mc (nP p) 4).1 hp.2
  change 2*(mw (nP p)/(r*Real.sqrt r)+mz (nP p)^2*nFr p-
    mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2+
    (1/nullD (nP p)-1)*(2-6*mz (nP p)*(nF p).1)*mz (nP p)^2 = _ at hm
  unfold coordinateSmallNull
  rw [scalar_rescale _ _ hc,lapse_rescale _ _ _ hc,lapseResidual_factor hp.1,
    physicalNullQuadratic_factor hz,physicalNullEta_factor hz]
  simp only [div_div_eq_mul_div,div_one]
  unfold nullResidual
  unfold nullD at hm ⊢
  linear_combination hm

theorem coordinateSmallNull_factor {p : NullInput} {r : ℝ}
    (hr : 0 < r) (hz : mz (nP p) = 1/r) (hp : p ∈ nullRegion) :
    coordinateSmallNull p r =
      2*mw (nP p)/(r^3*Real.sqrt r)/nullD (nP p)+
      (scalarCurvature (mq (nP p))/2-1)/r^2+nullResidual p/r^4 := by
  have hzn : mz (nP p) ≠ 0 := by rw [hz]; positivity
  rw [coordinateSmallNull_factor_z r hzn hp,hz]
  ring

end
end CKSAngularGeometry

end

end OAI
