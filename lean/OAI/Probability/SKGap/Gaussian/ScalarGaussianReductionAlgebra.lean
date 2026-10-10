import Mathlib
import OAI.Probability.SKGap.Matrix.GOERegression
import OAI.Probability.SKGap.Brownian.ContinuousKernel

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma radialDensity_translate (a c : ℝ) (x m : ι → ℝ) :
    radialDensity a (x+c • m)=radialDensity a x*
      exp (-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by
  unfold radialDensity
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x]
  have he : -(x⬝ᵥx+c*(x⬝ᵥm)+c*(x⬝ᵥm+c*(m⬝ᵥm)))/(2*a^2)=
      -(x⬝ᵥx)/(2*a^2)+(-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by ring
  rw [he,exp_add]
  ring

lemma gaussian_density_shift (d : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : ι → ℝ) :
    (∏ i,gaussianPDFReal d (NNReal.mk s hs) (y i))=
      radialDensity (sqrt s) (fun i => y i-d) := by
  have he (i : ι) : gaussianPDFReal d (NNReal.mk s hs) (y i)=
      gaussianPDFReal 0 (NNReal.mk s hs) (y i-d) := by simp [gaussianPDFReal]
  simp only [he]
  have hv : NNReal.mk s hs=NNReal.mk ((sqrt s)^2) (sq_nonneg (sqrt s)) := by
    ext
    exact (sq_sqrt hs).symm
  rw [hv,product_gaussianPDF_radial (sqrt_nonneg _)]

lemma scalar_gaussian_exponent {n s S j q b a : ℝ} (hn : n ≠ 0) (hs : s ≠ 0)
    (hS : S ≠ 0) (hSq : S=s+j*q) :
    -(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
      (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2 =
      n*j*(a-s*b)^2/(2*s*S) := by
  subst S
  field_simp
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

theorem rankOneDensity_cancellation {n s S j q b a : ℝ} (hn : n ≠ 0)
    (hs : 0 < s) (hS : S ≠ 0) (hSq : S=s+j*q)
    (x m : ι → ℝ) (hm : m⬝ᵥm=n*q) (hx : x⬝ᵥm=n*a) :
    rankOneDensity s (j/n) m (x+(j*b) • m)*exp (n*j*b^2/2) =
    sqrt (s/S)*radialDensity (sqrt s) x*exp (n*j*(a-s*b)^2/(2*s*S)) := by
  have he : s+(j/n)*(m⬝ᵥm)=S := by rw [hm,hSq]; field_simp
  rw [rankOneDensity,he,radialDensity_translate,sq_sqrt hs.le,hm,hx]
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x,hm,hx]
  have hE := scalar_gaussian_exponent hn hs.ne' hS hSq (j := j) (q := q) (b := b) (a := a)
  calc
    _ = sqrt (s/S)*radialDensity (sqrt s) x*
        exp (-(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
          (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2) := by rw [exp_add,exp_add]; ring
    _ = _ := by rw [hE]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma pi_gaussian_convolution (m₁ m₂ : ι → ℝ) (v₁ v₂ : ι → ℝ≥0) :
    ((Measure.pi (fun i=>gaussianReal (m₁ i) (v₁ i))).prod
      (Measure.pi (fun i=>gaussianReal (m₂ i) (v₂ i)))).map (fun p=>p.1+p.2)=
    Measure.pi (fun i=>gaussianReal (m₁ i+m₂ i) (v₁ i+v₂ i)) := by
  have h := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i=>gaussianReal (m₁ i) (v₁ i)) (fun i=>gaussianReal (m₂ i) (v₂ i))).map_eq
  rw [← h,Measure.map_map (by fun_prop) (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).measurable]
  change (Measure.pi (fun i=>(gaussianReal (m₁ i) (v₁ i)).prod (gaussianReal (m₂ i) (v₂ i)))).map
    (fun x i=> (x i).1+(x i).2)=_
  have (i : ι) : IsProbabilityMeasure (((gaussianReal (m₁ i) (v₁ i)).prod
      (gaussianReal (m₂ i) (v₂ i))).map (fun p : ℝ×ℝ=>p.1+p.2)) :=
    inferInstance
  rw [Measure.pi_map_pi (f := fun (_ : ι) (p : ℝ×ℝ)=>p.1+p.2) (fun _=>by fun_prop)]
  congr 1
  funext i
  exact gaussianReal_conv_gaussianReal

theorem continuous_convolution_density (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {φ p : (ι → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ x,0 ≤ φ x)
    {C : ℝ} (hφC : ∀ x,φ x ≤ C)
    (hconv : (μ.prod ((volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (φ x)))).map
      (fun q=>q.1+q.2)=(volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (p x)))
    (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (φ (z-x)) ∂μ)=ENNReal.ofReal (p z) := by
  let K : (ι → ℝ) → ℝ≥0∞ := fun y=>∫⁻ x,ENNReal.ofReal (φ (y-x)) ∂μ
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hae : K=ᵐ[volume] (fun y=>ENNReal.ofReal (p y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hK.aemeasurable hp.measurable.ennreal_ofReal.aemeasurable).mp
    ext s hs
    rw [withDensity_apply _ hs,withDensity_apply _ hs]
    let F : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ := fun q=>s.indicator (fun _=>1) q.2
    have hF : Measurable F := measurable_const.indicator (hs.preimage measurable_snd)
    have hh := additive_noise_lintegral μ (fun x=>ENNReal.ofReal (φ x))
      hφ.measurable.ennreal_ofReal id measurable_id F hF
    have hm : Measurable (s.indicator (fun _=> (1 : ℝ≥0∞))) := measurable_const.indicator hs
    have he := congrArg (fun ν=>∫⁻ y,s.indicator (fun _=> (1 : ℝ≥0∞)) y ∂ν) hconv
    rw [lintegral_map hm (by fun_prop),lintegral_withDensity_eq_lintegral_mul _
      hp.measurable.ennreal_ofReal hm] at he
    change (∫⁻ q,F (q.1,id q.1+q.2) ∂μ.prod (volume.withDensity (fun x=>ENNReal.ofReal (φ x))))=_ at he
    rw [hh] at he
    have hleft (y : ι → ℝ) : (∫⁻ x, ENNReal.ofReal (φ (y-id x))*F (x,y) ∂μ)=s.indicator K y := by
      by_cases hy : y∈s <;> simp [F,K,hy]
    have hright (y : ι → ℝ) : ENNReal.ofReal (p y)*s.indicator (fun _=>(1 : ℝ≥0∞)) y=
        s.indicator (fun y=>ENNReal.ofReal (p y)) y := by by_cases hy : y∈s <;> simp [hy]
    simp only [Pi.mul_apply,hleft,hright,lintegral_indicator hs] at he
    exact he
  have hi (y : ι → ℝ) : Integrable (fun x=>φ (y-x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have hc : Continuous (fun y : ι → ℝ=>∫ x,φ (y-x) ∂μ) := by
    apply continuous_of_dominated (bound := fun _=>C)
    · intro y; exact (hi y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
    · exact integrable_const C
    · exact Filter.Eventually.of_forall (fun x=>by fun_prop)
  have he (y : ι → ℝ) : K y=ENNReal.ofReal (∫ x,φ (y-x) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi y) (Filter.Eventually.of_forall (fun x=>hφpos _))).symm
  have hcont : Continuous K := by rw [show K=(fun y=>ENNReal.ofReal (∫ x,φ (y-x) ∂μ)) from funext he]; exact ENNReal.continuous_ofReal.comp hc
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (ι → ℝ)) hcont
    (ENNReal.continuous_ofReal.comp hp)).mp hae) z

theorem gaussian_radial_convolution {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ) (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (radialDensity σ (z-x))
      ∂Measure.pi (fun _ : ι=>gaussianReal 0 t.toNNReal))=
    ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) z) := by
  classical
  have hv : 0 < t+σ^2 := add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)
  have hnoise : Measure.pi (fun _ : ι=>gaussianReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity σ x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by intro hh; have hh' := congrArg (fun r : ℝ≥0=>(r:ℝ)) hh; exact (sq_pos_of_pos hσ).ne' hh')]
    congr 1; funext x; rw [product_gaussianPDF_radial hσ.le]
  have hout : Measure.pi (fun _ : ι=>gaussianReal 0 (t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by
      have he : (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)=t+σ^2 := by simp [Real.coe_toNNReal _ ht]
      exact_mod_cast (show (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)≠0 by rw [he]; exact hv.ne'))]
    congr 1; funext x
    have he : t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)=NNReal.mk ((sqrt (t+σ^2))^2) (sq_nonneg _) := by
      ext; simp [Real.coe_toNNReal _ ht,sq_sqrt hv.le]
    rw [he,product_gaussianPDF_radial (sqrt_nonneg _)]
  apply continuous_convolution_density _ (continuous_radialDensity σ)
    (continuous_radialDensity _) (fun x=>(radialDensity_pos hσ x).le)
    (radialDensity_le hσ)
  rw [← hnoise,pi_gaussian_convolution]
  simpa only [zero_add] using hout
end SKGap.GaussianDensity
end
end

end OAI
