import Mathlib
import OAI.Probability.LogConcave.Analysis.GrowthInnerGradient
import OAI.Probability.LogConcave.Sampling.Directional

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

structure PolyC1 {d : ℕ} (f : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ 1 f
  growth : HasPolynomialGrowth f
  derivative_growth : ∀ v : Point d, HasPolynomialGrowth (directional v f)

lemma integrable_polynomial_gibbs {d : ℕ} {H f : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : Continuous f)
    (hg : HasPolynomialGrowth f) : Integrable f (gibbs H) := by
  apply integrable_gibbs_of_weighted hH (ht.integrable_exp hH)
  simpa using integrable_tilted H hH hf ht hg 0

namespace PolyC1
variable {d : ℕ} {f g : Point d → ℝ}
lemma continuous (hf : PolyC1 f) : Continuous f := hf.smooth.continuous
lemma differentiable (hf : PolyC1 f) : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
lemma directional_continuous (hf : PolyC1 f) (v : Point d) : Continuous (directional v f) :=
  (hf.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
lemma add (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,Appell.HasGrowth.add hf.growth hg.growth,fun v => ?_⟩
  rw [directional_add hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (hf.derivative_growth v) (hg.derivative_growth v)
lemma neg (hf : PolyC1 f) : PolyC1 (fun x => -f x) := by
  refine ⟨hf.smooth.neg,?_,fun v => ?_⟩
  · simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) hf.growth
  · rw [directional_neg hf.differentiable]
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v)
lemma mul (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,Appell.HasGrowth.mul hf.growth hg.growth,fun v => ?_⟩
  rw [directional_mul hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ} (hf : ∀i∈s,PolyC1 (f i)) :
    PolyC1 (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),
    Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth),fun v => ?_⟩
  rw [directional_sum s (fun i hi => (hf i hi).differentiable)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).derivative_growth v)
end PolyC1

def adjointCoordinate {d : ℕ} (H : Point d → ℝ) (v : Point d) (f : Point d → ℝ) : Point d → ℝ :=
  fun x => -directional v f x+directional v H x*f x

lemma adjointCoordinate_pairing {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    (∫x,adjointCoordinate H v f x*g x ∂gibbs H)=∫x,f x*directional v g x ∂gibbs H := by
  have hs : Continuous (directional v H) := (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsg : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  have hi₁ : Integrable (fun z => directional v f z*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hf.directional_continuous v).mul hg.continuous)
    (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
  have hi₂ : Integrable (fun z => f z*directional v g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    (hf.continuous.mul (hg.directional_continuous v))
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
  have hi₃ : Integrable (fun z => (directional v H z*f z)*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hs.mul hf.continuous).mul hg.continuous)
    (Appell.HasGrowth.mul (Appell.HasGrowth.mul hsg hf.growth) hg.growth)
  have hh := polynomial_gibbs_ibp hH ht hL (hf.mul hg).smooth (hf.mul hg).growth v
    ((hf.mul hg).derivative_growth v)
  change (∫x,directional v (fun x => f x*g x) x ∂gibbs H)=_ at hh
  rw [directional_mul hf.differentiable hg.differentiable,integral_add hi₁ hi₂] at hh
  simp only [←directional_gradient,mul_assoc] at hi₃ ⊢ hh
  change (∫x,(-directional v f x+directional v H x*f x)*g x ∂gibbs H)=_
  simp_rw [add_mul,neg_mul,mul_assoc]
  rw [integral_add (f:=fun z => -(directional v f z*g z)) hi₁.neg hi₃,integral_neg]
  linarith

def tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι] (H : Point d → ℝ)
    (b : ι → Point d) (V : ι → Point d → ℝ) : Point d → ℝ :=
  fun x => ∑i,adjointCoordinate H (b i) (V i) x

lemma tensorAdjoint_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    {H g : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hV : ∀i,PolyC1 (V i)) (hg : PolyC1 g)
    (b : ι → Point d) :
    (∫x,tensorAdjoint H b V x*g x ∂gibbs H)=
      ∑i,∫x,V i x*directional (b i) g x ∂gibbs H := by
  have hi (i : ι) : Integrable (fun x => adjointCoordinate H (b i) (V i) x*g x) (gibbs H) := by
    apply integrable_polynomial_gibbs hH.continuous ht
    · exact (((hV i).directional_continuous _).neg.add
        (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)).mul hg.continuous
    · have hs : HasPolynomialGrowth (directional (b i) H) := by
        simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL (b i)
      exact Appell.HasGrowth.mul
        (Appell.HasGrowth.add (by
          simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) ((hV i).derivative_growth (b i)))
          (Appell.HasGrowth.mul hs (hV i).growth)) hg.growth
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_pairing hH ht hL (hV i) hg (b i))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
