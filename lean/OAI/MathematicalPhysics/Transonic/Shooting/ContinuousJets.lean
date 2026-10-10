import Mathlib.Topology.Algebra.Polynomial
import OAI.MathematicalPhysics.Transonic.Shooting.ParametricJets

namespace OAI

section
noncomputable section

namespace SepticProfile.ParametricJets
open Polynomial
variable {K : Type*} [CommRing K]

def prefP (sigma : K) : Polynomial K := (1+X)*(1-C sigma*(1+X)^2)
def denQuotP (sigma : K) (p1 : Polynomial K) : Polynomial K := prefP sigma*(-2*p1-X*p1^2)
def transP (kappa : K) (p : Polynomial K) : Polynomial K :=
  C kappa*(1+X)*(1-p^2)+3*((1+X)-p)
def linP (sigma kappa c : K) (p : Polynomial K) : Polynomial K :=
  -2*prefP sigma*p*p.derivative+2*C c*p*transP kappa p+
    (1-C c*p^2)*(2*C kappa*(1+X)*p+3)

 theorem split_polynomial {p : Polynomial K} {s : K}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) :
    ∃ p1 : Polynomial K, p=1+X*p1 ∧ p1.coeff 0=s := by
  have hd : (X : Polynomial K) ∣ p-1 := X_dvd_iff.mpr (by simp [hp0])
  obtain ⟨p1,hp1'⟩ := hd
  have he : p=1+X*p1 := by linear_combination hp1'
  refine ⟨p1,he,?_⟩
  rw [he] at hp1
  simpa [coeff_one] using hp1

 theorem coeff_denQuotP {p1 : Polynomial K} {s : K} (h : p1.coeff 0=s) (sigma : K) :
    (denQuotP sigma p1).coeff 0 = -2*(1-sigma)*s := by
  rw [coeff_zero_eq_eval_zero]
  have he : p1.eval 0=s := by simpa only [coeff_zero_eq_eval_zero] using h
  simp [denQuotP, prefP, he]
  ring

 theorem coeff_linP {p : Polynomial K} {s : K}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) (sigma kappa c : K) :
    (linP sigma kappa c p).coeff 0 = -2*(1-sigma)*s+(1-c)*(2*kappa+3) := by
  rw [coeff_zero_eq_eval_zero]
  have he0 : p.eval 0=1 := by simpa only [coeff_zero_eq_eval_zero] using hp0
  have he1 : p.derivative.eval 0=s := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simpa using hp1
  simp [linP, prefP, transP, he0, he1]

 theorem split_linearization {p p1 : Polynomial K} {s rho sigma kappa c : K}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) (hp10 : p1.coeff 0=s)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s) :
    ∃ e : Polynomial K, C rho*denQuotP sigma p1+linP sigma kappa c p=X*e := by
  apply X_dvd_iff.mpr
  rw [coeff_add, coeff_C_mul, coeff_denQuotP hp10,
    coeff_linP hp0 hp1]
  linear_combination -hrho


end SepticProfile.ParametricJets

namespace SepticProfile.ParametricJets
open Polynomial
variable {A : Type*} [TopologicalSpace A]

/-- Nowhere vanishing continuous scalar coefficients are units in the exact
coefficient ring. This avoids choosing unrelated discontinuous finite jets. -/
lemma isUnit_continuous {f : C(A,ℝ)} (h : ∀ a, f a ≠ 0) : IsUnit f := by
  let g : C(A,ℝ) := ⟨fun a => (f a)⁻¹,f.continuous.inv₀ h⟩
  refine ⟨⟨f,g,?_,?_⟩,rfl⟩
  · ext a
    change f a*(f a)⁻¹=1
    exact mul_inv_cancel₀ (h a)
  · ext a
    change (f a)⁻¹*f a=1
    exact inv_mul_cancel₀ (h a)

def specialize (a : A) : Polynomial C(A,ℝ) →+* Polynomial ℝ :=
  Polynomial.mapRingHom (ContinuousMap.evalAlgHom ℝ ℝ a).toRingHom

@[simp] lemma coeff_specialize (p : Polynomial C(A,ℝ)) (a : A) (i : ℕ) :
    (specialize a p).coeff i=p.coeff i a := by
  simp [specialize]

@[simp] lemma specialize_C (f : C(A,ℝ)) (a : A) : specialize a (C f)=C (f a) := by
  simp [specialize]

@[simp] lemma specialize_derivative (p : Polynomial C(A,ℝ)) (a : A) :
    specialize a p.derivative=(specialize a p).derivative := by
  simp [specialize,Polynomial.derivative_map]

lemma specialize_residual (sigma kappa c : C(A,ℝ)) (p : Polynomial C(A,ℝ)) (a : A) :
    specialize a (residualP sigma kappa c p)=
      SourceJets.residualP (sigma a) (kappa a) (c a) (specialize a p) := by
  simp [residualP,SourceJets.residualP,specialize,Polynomial.derivative_map]

lemma continuous_aeval_specialize (p : Polynomial C(A,ℝ)) :
    Continuous (fun v : A × ℂ => aeval v.2 (specialize v.1 p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    funext v
    simp only [Pi.add_apply,map_add]
  | monomial n f =>
    have he : (fun v : A × ℂ => aeval v.2 (specialize v.1 (monomial n f)))=
        (fun v : A × ℂ => (f v.1:ℂ)*v.2^n) := by
      funext v
      simp [specialize]
    rw [he]
    exact (Complex.continuous_ofReal.comp (f.continuous.comp continuous_fst)).mul
      (continuous_snd.pow n)

/-- A single finite jet over the ring of continuous parameter functions yields
all members of the family, with the exact source residual divisibility. -/
theorem exists_continuous_jet (sigma kappa c s rho : C(A,ℝ))
    (hs : ∀ a, 2*(1-sigma a)*(s a)^2-(1-c a)*(2*kappa a+3)*s a+3*(1-c a)=0)
    (hd : ∀ a, 2*(1-sigma a)*s a ≠ 0)
    (hrho : ∀ a, rho a*(2*(1-sigma a)*s a)=
      (1-c a)*(2*kappa a+3)-2*(1-sigma a)*s a)
    (hnr : ∀ a (n : ℕ), rho a ≠ (n:ℝ)+2) (m : ℕ) :
    ∃ p p1 S E : Polynomial C(A,ℝ),
      p.coeff 0=1 ∧ p.coeff 1=s ∧ p=1+X*p1 ∧ p1.coeff 0=s ∧
      residualP sigma kappa c p=X^(m+3)*S ∧
      C rho*denQuotP sigma p1+linP sigma kappa c p=X*E := by
  have hs' : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0 := by
    ext a
    exact hs a
  have hn (n : ℕ) : IsUnit ((1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3)) := by
    apply isUnit_continuous
    intro a he
    change (1-c a)*(2*kappa a+3)-2*(1-sigma a)*s a*((n:ℝ)+3)=0 at he
    have hz : (2*(1-sigma a)*s a)*(rho a-((n:ℝ)+2))=0 := by
      linear_combination hrho a + he
    exact hnr a n (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hd a)))
  obtain ⟨p,hp0,hp1,S,hS⟩ := exists_finite_jet_divisible sigma kappa c s hs' (m+1) (fun n _ => hn n)
  obtain ⟨p1,hp,hp10⟩ := split_polynomial hp0 hp1
  have hrho' : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s := by
    ext a
    exact hrho a
  obtain ⟨E,hE⟩ := split_linearization hp0 hp1 hp10 hrho'
  exact ⟨p,p1,S,E,hp0,hp1,hp,hp10,by simpa only [Nat.add_assoc] using hS,hE⟩

end SepticProfile.ParametricJets

end
end

end OAI
