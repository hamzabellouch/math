import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GammaNatMulLeft
import OAI.Geometry.WeakHessian.Sobolev.MulBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_add_const_left (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (a : ℝ) :
    gamma m (fun x => f x+a) g =ᵐ[m] gamma m f g := by
  have ep : (fun x => f x+a+g x) = (fun x => (f x+g x)+a) := by funext x; ring
  have em : (fun x => f x+a-g x) = (fun x => (f x-g x)+a) := by funext x; ring
  filter_upwards [weakGradient_add_const_of_exists (hf.add hfinite hg).2 a,
    weakGradient_add_const_of_exists (hf.sub hfinite hg).2 a] with x hp hm
  simp only [gamma,ep,em,hp,hm]

lemma weakGradient_mul_le_local (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (fun y => f y*η y) x ≤
      |η x| *weakGradient m f x + |f x| *weakGradient m η x :=
  (weakGradient_isMinimal (hf.mul_bounded hfinite hη hA hB).2).2 _
    ((weakGradient_isMinimal hf.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.1 hη.1.aemeasurable hA hB)

lemma gamma_product_residual (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f η g : X → ℝ} (hf : LocalSobolev m f) (hη : LocalSobolev m η) (hg : LocalSobolev m g)
    {A B : ℝ} (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (a b : ℝ) :
    ∀ᵐ x ∂m, |gamma m (fun y => f y*η y) g x - b*gamma m f g x - a*gamma m η g x| ≤
      (|η x-b| *weakGradient m f x + |f x-a| *weakGradient m η x)*weakGradient m g x := by
  let u : X → ℝ := fun x => f x-a
  let v : X → ℝ := fun x => η x-b
  have hu : LocalSobolev m u := hf.add_const hfinite (-a)
  have hv : LocalSobolev m v := hη.add_const hfinite (-b)
  have hvA : ∀ᵐ x ∂m, |v x| ≤ A+|b| := by
    filter_upwards [hA] with x hx
    exact (abs_sub (η x) b).trans (add_le_add hx le_rfl)
  have hDf : weakGradient m u =ᵐ[m] weakGradient m f := weakGradient_add_const_of_exists hf.2 (-a)
  have hDη : weakGradient m v =ᵐ[m] weakGradient m η := weakGradient_add_const_of_exists hη.2 (-b)
  have hvB : ∀ᵐ x ∂m, |weakGradient m v x| ≤ B := by
    filter_upwards [hB,hDη] with x hx he; simpa only [he] using hx
  have hp := hf.mul_bounded hfinite hη hA hB
  have hres := hu.mul_bounded hfinite hv hvA hvB
  have hs₁ := hp.sub hfinite (hf.const_mul b)
  have hs₂ := hs₁.sub hfinite (hη.const_mul a)
  have e : (fun x => u x*v x) = (fun x => (f x*η x-b*f x-a*η x)+a*b) := by
    funext x; dsimp only [u,v]; ring
  filter_upwards [abs_gamma_le hfinite hpar hres hg,
    weakGradient_mul_le_local hfinite hu hv hvA hvB,hDf,hDη,
    gamma_add_const_left hfinite hs₂ hg (a*b),
    gamma_sub_left hfinite hpar hs₁ (hη.const_mul a) hg,
    gamma_sub_left hfinite hpar hp (hf.const_mul b) hg,
    gamma_const_mul_left hfinite hpar hf hg b,
    gamma_const_mul_left hfinite hpar hη hg a,
    weakGradient_nonneg (m := m) g] with x hab hd hdf hdη he hs2 hs1 hb ha hng
  rw [e,he,hs2,hs1,hb,ha] at hab
  rw [hdf,hdη,e] at hd
  exact hab.trans (mul_le_mul_of_nonneg_right hd hng)

lemma gamma_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f η g : X → ℝ} (hf : LocalSobolev m f) (hη : LocalSobolev m η) (hg : LocalSobolev m g)
    {A B : ℝ} (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    gamma m (fun y => f y*η y) g =ᵐ[m]
      (fun x => f x*gamma m η g x + η x*gamma m f g x) := by
  filter_upwards [ae_all_iff.mpr (fun a : ℚ => ae_all_iff.mpr
    (fun b : ℚ => gamma_product_residual hfinite hpar hf hη hg hA hB (a:ℝ) (b:ℝ)))] with x hx
  obtain ⟨qa,_,_,has⟩ := Real.exists_seq_rat_strictMono_tendsto (f x)
  obtain ⟨qb,_,_,hbs⟩ := Real.exists_seq_rat_strictMono_tendsto (η x)
  have H : |gamma m (fun y => f y*η y) g x - η x*gamma m f g x - f x*gamma m η g x| ≤ (0:ℝ) := by
    have hl := (((tendsto_const_nhds (x := gamma m (fun y => f y*η y) g x)).sub (hbs.mul_const (gamma m f g x))).sub
      (has.mul_const (gamma m η g x))).abs
    have hr := ((((tendsto_const_nhds (x := η x)).sub hbs).abs.mul_const (weakGradient m f x)).add
      (((tendsto_const_nhds (x := f x)).sub has).abs.mul_const (weakGradient m η x))).mul_const (weakGradient m g x)
    have hr0 : Tendsto (fun n => (|η x-(qb n:ℝ)| *weakGradient m f x +
        |f x-(qa n:ℝ)| *weakGradient m η x)*weakGradient m g x) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self,abs_zero,zero_mul,zero_add] using hr
    exact le_of_tendsto_of_tendsto hl hr0 (Eventually.of_forall fun n => hx (qa n) (qb n))
  have he : gamma m (fun y => f y*η y) g x - η x*gamma m f g x - f x*gamma m η g x = 0 :=
    abs_nonpos_iff.mp H
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
