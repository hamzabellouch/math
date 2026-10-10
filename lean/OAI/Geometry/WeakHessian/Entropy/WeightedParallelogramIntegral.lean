import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Sobolev.GradientPairSum
import OAI.Geometry.WeakHessian.Calculus.TriangularFoldNorm

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weighted_parallelogram_of_integral (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {η ξ : X → ℝ}
    (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hei : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D) :
    (∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m) =
    2*(∫ x, (weakGradient m f x*η x)^2 ∂m) + 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) := by
  let fs (n : ℕ) := triangularFold (1/((n:ℝ)+1)) ∘ f
  let gs (n : ℕ) := triangularFold (1/((n:ℝ)+1)) ∘ g
  have hfs (n : ℕ) : Sobolev m (fs n) :=
    hf.normalContraction hfinite (triangularFold_lipschitz _) (triangularFold_zero _)
  have hgs (n : ℕ) : Sobolev m (gs n) :=
    hg.normalContraction hfinite (triangularFold_lipschitz _) (triangularFold_zero _)
  have hef (n : ℕ) : weakGradient m (fs n) =ᵐ[m] weakGradient m f :=
    weakGradient_triangularFold hfinite hf (by positivity)
  have heg (n : ℕ) : weakGradient m (gs n) =ᵐ[m] weakGradient m g :=
    weakGradient_triangularFold hfinite hg (by positivity)
  have hft : Tendsto (fun n => (hfs n).1.toLp (fs n)) atTop (𝓝 0) := triangularFold_tendsto_toLp hf.1
  have hgt : Tendsto (fun n => (hgs n).1.toLp (gs n)) atTop (𝓝 0) := triangularFold_tendsto_toLp hg.1
  have hplus (n : ℕ) := (hfs n).add hfinite (hgs n)
  have hminus (n : ℕ) := (hfs n).sub hfinite (hgs n)
  have hpt : Tendsto (fun n => (hplus n).1.toLp (fun x => fs n x+gs n x)) atTop (𝓝 0) := by
    have he (n : ℕ) : (hplus n).1.toLp (fun x => fs n x+gs n x) =
        (hfs n).1.toLp (fs n) + (hgs n).1.toLp (gs n) := MemLp.toLp_add (hfs n).1 (hgs n).1
    simpa only [he,zero_add] using hft.add hgt
  have hmt : Tendsto (fun n => (hminus n).1.toLp (fun x => fs n x-gs n x)) atTop (𝓝 0) := by
    have he (n : ℕ) : (hminus n).1.toLp (fun x => fs n x-gs n x) =
        (hfs n).1.toLp (fs n) - (hgs n).1.toLp (gs n) := MemLp.toLp_sub (hfs n).1 (hgs n).1
    simpa only [he,sub_zero] using hft.sub hgt
  have hrf (n : ℕ) : ‖(hfs n).2.2.toLp (weakGradient m (fs n))‖ ≤
      ‖hf.2.2.toLp (weakGradient m f)‖ := by
    have H : (hfs n).2.2.toLp (weakGradient m (fs n)) = hf.2.2.toLp (weakGradient m f) :=
      Lp.ext ((hfs n).2.2.coeFn_toLp.trans ((hef n).trans hf.2.2.coeFn_toLp.symm))
    rw [H]
  have hrg (n : ℕ) : ‖(hgs n).2.2.toLp (weakGradient m (gs n))‖ ≤
      ‖hg.2.2.toLp (weakGradient m g)‖ := by
    have H : (hgs n).2.2.toLp (weakGradient m (gs n)) = hg.2.2.toLp (weakGradient m g) :=
      Lp.ext ((hgs n).2.2.coeFn_toLp.trans ((heg n).trans hg.2.2.coeFn_toLp.symm))
    rw [H]
  let R := ‖(hf.2.2.add hg.2.2).toLp (fun x => weakGradient m f x+weakGradient m g x)‖
  have hbound {u : X → ℝ} (hu : Sobolev m u)
      (he : ∀ᵐ x ∂m, weakGradient m u x ≤ weakGradient m f x+weakGradient m g x) :
      ‖hu.2.2.toLp (weakGradient m u)‖ ≤ R := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu.2.2.coeFn_toLp,(hf.2.2.add hg.2.2).coeFn_toLp,
      (weakGradient_isMinimal hu.2.1.2).1.2.1, he] with x h1 h2 h0 hx
    change ‖(hu.2.2.toLp (weakGradient m u)) x‖ ≤
      ‖((hf.2.2.add hg.2.2).toLp (weakGradient m f + weakGradient m g)) x‖
    simpa only [h1,h2,Real.norm_eq_abs,abs_of_nonneg h0,Pi.add_apply] using hx.trans (le_abs_self _)
  have hrp (n : ℕ) : ‖(hplus n).2.2.toLp (weakGradient m (fun x => fs n x+gs n x))‖ ≤ R := by
    apply hbound (hplus n)
    filter_upwards [weakGradient_add_le hfinite (hfs n).2.1 (hgs n).2.1,hef n,heg n] with x hx hf' hg'
    simpa only [hf',hg'] using hx
  have hrm (n : ℕ) : ‖(hminus n).2.2.toLp (weakGradient m (fun x => fs n x-gs n x))‖ ≤ R := by
    apply hbound (hminus n)
    filter_upwards [weakGradient_add_le hfinite (hfs n).2.1 ((hgs n).neg).2.1,hef n,heg n,
      weakGradient_const_mul (m := m) (-1) (gs n)] with x hx hf' hg' hn
    simp only [neg_one_mul,abs_neg,abs_one,one_mul] at hn
    simpa only [← sub_eq_add_neg,hn,hf',hg'] using hx
  let e (u : X → ℝ) := (∫ x, (weakGradient m (fun y => u y*η y) x)^2 ∂m) -
    ∫ x, (weakGradient m u x*η x)^2 ∂m
  have ht (us : ℕ → X → ℝ) (hs : ∀ n, Sobolev m (us n)) {R : ℝ}
      (hR : ∀ n, ‖(hs n).2.2.toLp (weakGradient m (us n))‖ ≤ R)
      (hT : Tendsto (fun n => (hs n).1.toLp (us n)) atTop (𝓝 0)) :
      Tendsto (fun n => e (us n)) atTop (𝓝 0) :=
    tendsto_gradient_mul_error hfinite hs hη hξ hei hη0 hξ0 hA hB hD hηA hDη hξC hDξ hR hT
  have hT := ((ht _ hplus hrp hpt).add (ht _ hminus hrm hmt)).sub
    (((ht _ hfs hrf hft).const_mul 2).add ((ht _ hgs hrg hgt).const_mul 2))
  have hpair (n : ℕ) :
      (∫ x, (weakGradient m (fun y => fs n y+gs n y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => fs n y-gs n y) x*η x)^2 ∂m) =
      (∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m) := by
    rw [← integral_add (memLp_mul_bounded (hplus n).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq
        (memLp_mul_bounded (hminus n).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq,
      ← integral_add (memLp_mul_bounded (hf.add hfinite hg).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq
        (memLp_mul_bounded (hf.sub hfinite hg).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq]
    apply integral_congr_ae
    filter_upwards [gradientPairSum_fold (m := m) hfinite hf hg (δ := 1/((n:ℝ)+1)) (by positivity)] with x hx
    change weakGradient m (fun y => fs n y+gs n y) x^2 +
      weakGradient m (fun y => fs n y-gs n y) x^2 =
      weakGradient m (fun y => f y+g y) x^2 + weakGradient m (fun y => f y-g y) x^2 at hx
    calc
      _ = (weakGradient m (fun y => fs n y+gs n y) x^2 +
        weakGradient m (fun y => fs n y-gs n y) x^2)*(η x)^2 := by ring
      _ = _ := congrArg (fun a : ℝ => a*(η x)^2) hx
      _ = _ := by ring
  have hefs (n : ℕ) : (∫ x, (weakGradient m (fs n) x*η x)^2 ∂m) =
      ∫ x, (weakGradient m f x*η x)^2 ∂m :=
    integral_congr_ae ((hef n).mono fun x hx => congrArg (fun a : ℝ => (a*η x)^2) hx)
  have hegs (n : ℕ) : (∫ x, (weakGradient m (gs n) x*η x)^2 ∂m) =
      ∫ x, (weakGradient m g x*η x)^2 ∂m :=
    integral_congr_ae ((heg n).mono fun x hx => congrArg (fun a : ℝ => (a*η x)^2) hx)
  let v := 2*(∫ x, (weakGradient m f x*η x)^2 ∂m) + 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) -
      ((∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m))
  have heq (n : ℕ) : e (fun x => fs n x+gs n x) + e (fun x => fs n x-gs n x) -
      (2*e (fs n)+2*e (gs n)) = v := by
    have H := hpar (fun x => fs n x*η x) (fun x => gs n x*η x)
      ((hfs n).mul_bounded hfinite hη hηA hDη) ((hgs n).mul_bounded hfinite hη hηA hDη)
    have hp : (fun y => (fs n y+gs n y)*η y) = (fun y => fs n y*η y+gs n y*η y) := by funext y; ring
    have hm : (fun y => (fs n y-gs n y)*η y) = (fun y => fs n y*η y-gs n y*η y) := by funext y; ring
    dsimp only [e,v]
    rw [hp,hm,hefs,hegs]
    linarith [hpair n]
  simp only [zero_add,mul_zero,sub_zero,heq] at hT
  have hv : v = 0 := tendsto_nhds_unique tendsto_const_nhds hT
  dsimp only [v] at hv
  linarith
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
