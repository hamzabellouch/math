import OAI.Geometry.Kahler.BaseRootAveraging

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phase_mean_derivative {W : Base → ℝ} {ℓ : ℕ} (hd : Differentiable ℝ W)
    (hb : PhaseBandwidth W ℓ) (p : Sphere) :
    (∫ z : Circle, phaseDerivative W ((z:ℂ) • (p:Base)) ∂circleMeasure)=0 := by
  obtain ⟨s,b,hs,he⟩ := hb p
  have hd' := phaseDerivative_expansion hd p s b he
  have hi : (∫ z : Circle, (phaseDerivative W ((z:ℂ) • (p:Base)):ℂ) ∂circleMeasure)=0 := by
    simp_rw [hd']
    rw [phaseSum_mean]
    split_ifs <;> simp
  rw [integral_complex_ofReal] at hi
  exact Complex.ofReal_injective hi

lemma phase_average_product {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {W : Base → ℝ} (hb : PhaseBandwidth W ℓ) (p : Sphere)
    {V : Circle → ℝ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z) :
    (∫ z, V z*W ((z:ℂ) • (p:Base)) ∂circleMeasure) =
      (∫ z, V z ∂circleMeasure)*(∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure) := by
  obtain ⟨s,b,hs,he⟩ := hb p
  have hvi : Integrable (fun z : Circle => (V z:ℂ)) circleMeasure := hi.ofReal
  have hh := root_invariant_phaseSum hk hl hvi (fun z => congrArg (fun t : ℝ => (t:ℂ)) (hV z)) s b hs
  simp_rw [← he,← Complex.ofReal_mul] at hh
  rw [integral_complex_ofReal,integral_complex_ofReal,integral_complex_ofReal,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

def phaseAction (z : Circle) (ξ : Sphere) : Sphere := sphereAction (phaseIsometry z z.norm_coe) ξ

@[simp] lemma phaseAction_coe (z : Circle) (ξ : Sphere) : (phaseAction z ξ : Base)=(z:ℂ) • (ξ:Base) := rfl

lemma phaseAction_continuous : Continuous (fun p : Circle × Sphere => phaseAction p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)

lemma sigma_phase_average {V : Sphere → ℝ} (hV : Continuous V) :
    (∫ ξ, V ξ ∂sigma) = ∫ ξ, ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure ∂sigma := by
  have hc : Continuous (fun p : Circle × Sphere => V (phaseAction p.1 p.2)) := hV.comp phaseAction_continuous
  have hi := compact_continuous_integrable (μ := circleMeasure.prod sigma) hc
  have hunit : ∀ z : Circle, (∫ ξ, V (phaseAction z ξ) ∂sigma)=∫ ξ, V ξ ∂sigma := by
    intro z
    exact sigma_integral_unitary (phaseIsometry z z.norm_coe) V
  rw [← integral_integral_swap hi]
  simp_rw [hunit]
  simp

lemma sigma_root_average {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {W V : Base → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hb : PhaseBandwidth W ℓ) (hm : OrbitMeanOne W)
    (hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base))=V ξ) :
    (∫ ξ : Sphere, V ξ*W ξ ∂sigma)=∫ ξ : Sphere, V ξ ∂sigma := by
  have hc : Continuous (fun ξ : Sphere => V ξ*W ξ) := (hV.mul hW).comp continuous_subtype_val
  have hcV : Continuous (fun ξ : Sphere => V ξ) := hV.comp continuous_subtype_val
  rw [sigma_phase_average hc,sigma_phase_average hcV]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    change (∫ z : Circle, V ((z:ℂ) • (ξ:Base))*W ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=_
    have hi : Integrable (fun z : Circle => V ((z:ℂ) • (ξ:Base))) circleMeasure :=
      by
        have hcZ : Continuous (fun z : Circle => V ((z:ℂ) • (ξ:Base))) := by fun_prop
        exact compact_continuous_integrable hcZ
    rw [phase_average_product hk hl hb ξ hi
      (fun z => by simpa only [Circle.coe_mul,mul_smul,phaseAction_coe] using hroot (phaseAction z ξ)),hm ξ,mul_one]
    rfl)

end PinchedHartogs.BaseConstruction

end

end OAI
