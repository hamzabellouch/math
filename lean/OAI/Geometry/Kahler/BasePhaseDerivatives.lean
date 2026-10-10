import OAI.Geometry.Kahler.BaseWeightedDerivative

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_derivative (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseChar n (Circle.exp t))
      ((n:ℂ)*Complex.I*phaseChar n (Circle.exp θ)) θ := by
  have hh : HasDerivAt (fun t : ℝ => (n:ℂ)*(t:ℂ)*Complex.I) ((n:ℂ)*Complex.I) θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (n:ℂ)).mul_const Complex.I
  simpa only [phaseChar_exp,mul_comm] using hh.cexp

lemma phaseSum_derivative (s : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseSum s a (Circle.exp t))
      (phaseSum s (fun n => (n:ℂ)*Complex.I*a n) (Circle.exp θ)) θ := by
  have hh := HasDerivAt.sum (u := s) (fun n _ => (phaseChar_derivative n θ).const_mul (a n))
  convert! hh using 1
  · ext t; simp only [phaseSum,Finset.sum_apply]
  · unfold phaseSum
    apply Finset.sum_congr rfl
    intro n hn
    ring

lemma phase_curve_derivative (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (Circle.exp t:ℂ) • z)
      (Complex.I • ((Circle.exp θ:ℂ) • z)) θ := by
  have hh : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I))
      (Complex.exp ((θ:ℂ)*Complex.I)*Complex.I) θ := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
  simpa only [Circle.coe_exp,smul_smul,mul_comm] using hh.smul_const z

lemma phaseDerivative_curve {W : Base → ℝ} (hW : Differentiable ℝ W) (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => W ((Circle.exp t:ℂ) • z))
      (phaseDerivative W ((Circle.exp θ:ℂ) • z)) θ := by
  exact (hW _).hasFDerivAt.comp_hasDerivAt θ (phase_curve_derivative z θ)

lemma phaseDerivative_expansion {W : Base → ℝ} (hW : Differentiable ℝ W) (p : Sphere)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s a z) (z : Circle) :
    (phaseDerivative W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s (fun n => (n:ℂ)*Complex.I*a n) z := by
  obtain ⟨θ,rfl⟩ := Circle.exp_surjective z
  have hleft := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ (phaseDerivative_curve hW (p:Base) θ)
  have hfun : (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ)) =
      (fun t : ℝ => phaseSum s a (Circle.exp t)) := funext (fun t => he _)
  change HasDerivAt (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ))
    (phaseDerivative W ((Circle.exp θ:ℂ) • (p:Base)):ℂ) θ at hleft
  rw [hfun] at hleft
  exact hleft.unique (phaseSum_derivative s a θ)

lemma phaseBandwidth_derivative {W : Base → ℝ} {ℓ : ℕ} (hW : Differentiable ℝ W)
    (hb : PhaseBandwidth W ℓ) : PhaseBandwidth (phaseDerivative W) ℓ := by
  intro p
  obtain ⟨s,a,hs,he⟩ := hb p
  exact ⟨s,fun n => (n:ℂ)*Complex.I*a n,hs,phaseDerivative_expansion hW p s a he⟩

end PinchedHartogs.BaseConstruction

end

end OAI
