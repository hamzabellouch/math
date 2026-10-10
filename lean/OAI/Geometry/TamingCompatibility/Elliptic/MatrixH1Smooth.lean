import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.PrincipalDerivativeError
import OAI.Geometry.TamingCompatibility.DifferentialForms.NegativeWeightMoment

namespace OAI

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem matrix_H1_smooth {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u)
    (hf : ∀ n : ℕ, MemSobolev n 2
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u)) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧ u = EuclideanSobolev.boundedDistribution g := by
  apply EuclideanSobolev.exists_smooth_representative
  intro s
  obtain ⟨n,hn⟩ := exists_nat_gt s
  exact (matrix_H1_bootstrap n a hweak hstrong b L v c K hu (hf n)).mono (by linarith)

end TamingCompatibility.HilbertSobolev

end

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology
section Locality
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma cutoff_product_eq (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) : (g : E → ℂ) * h = g := by
  funext x
  by_cases hx : x ∈ tsupport g
  · simp [hh x hx |>.eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_derivative_product_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v : E) :
    (g : E → ℂ) * (∂_{v} h : 𝓢(E,ℂ)) = 0 := by
  funext x
  by_cases hx : x ∈ tsupport g
  · have hd := (hh x hx).lineDeriv_eq (𝕜 := ℝ) (v := v)
    simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const, Pi.mul_apply,
      Pi.zero_apply, mul_zero] using congrArg (g x * ·) hd
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_second_product_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) :
    (g : E → ℂ) * (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)) = 0 := by
  funext x
  by_cases hx : x ∈ tsupport g
  · have hdh : (fun y => (∂_{w} h : 𝓢(E,ℂ)) y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(hh x hx).eventuallyEq_nhds] with y hy
      simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const] using hy.lineDeriv_eq (𝕜 := ℝ) (v := w)
    have hd := hdh.lineDeriv_eq (𝕜 := ℝ) (v := v)
    simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const, Pi.mul_apply,
      Pi.zero_apply, mul_zero] using congrArg (g x * ·) hd
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_mul_cutoff (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F h u) = smulLeftCLM F g u := by
  rw [smulLeftCLM_smulLeftCLM_apply h.hasTemperateGrowth g.hasTemperateGrowth,
    mul_comm (h : E → ℂ), cutoff_product_eq g h hh]

lemma cutoff_mul_derivative (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F (∂_{v} h : 𝓢(E,ℂ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (∂_{v} h : 𝓢(E,ℂ)).hasTemperateGrowth
    g.hasTemperateGrowth, mul_comm,
    cutoff_derivative_product_zero g h hh v]
  change smulLeftCLM F (fun _ => 0) u = 0
  simp

lemma cutoff_mul_second (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)).hasTemperateGrowth
    g.hasTemperateGrowth, mul_comm,
    cutoff_second_product_zero g h hh v w]
  change smulLeftCLM F (fun _ => 0) u = 0
  simp

lemma cutoff_secondCommutator_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (secondCommutator h v w u) = 0 := by
  simp only [secondCommutator, map_add, cutoff_mul_second g h hh,
    cutoff_mul_derivative g h hh, add_zero]

end Locality
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma localizationError_cutoff_zero
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (localizationError a h u) = 0 := by
  simp only [localizationError, map_add, ContinuousLinearMap.map_smul_of_tower,
    map_sum, coefficient_products_commute g, cutoff_secondCommutator_zero g h hh,
    map_zero, Finset.sum_const_zero, smul_zero, add_zero]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma perturbedHelmholtz_locality
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (perturbedHelmholtz a (smulLeftCLM F h u)) =
      smulLeftCLM F g (perturbedHelmholtz a u) := by
  rw [perturbedHelmholtz_cutoff, map_add, cutoff_mul_cutoff g h hh,
    localizationError_cutoff_zero a g h hh, add_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_locality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
      smulLeftCLM F g (matrixLowerOrder b L v c K u) := by
  simp only [matrixLowerOrder, map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [coefficient_products_commute g (b i), distribution_derivative_product,
      map_add, fiberMap_product, fiberMap_product, map_add,
      cutoff_mul_derivative g h hh, cutoff_mul_cutoff g h hh, zero_add]
    exact coefficient_products_commute (b i) g _
  · apply Finset.sum_congr rfl
    intro i _
    rw [coefficient_products_commute g (c i), fiberMap_product,
      cutoff_mul_cutoff g h hh]
    exact coefficient_products_commute (c i) g _

theorem matrix_cutoff_succ_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g : 𝓢(E,ℂ))
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u)
    (hf : MemSobolev n 2 (smulLeftCLM F g
      (perturbedHelmholtz a u + matrixLowerOrder b L v c K u))) :
    MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g u) := by
  apply principal_H1_bootstrap n a hweak hstrong
  · have h1 : MemSobolev (1:ℕ) 2 u := hu.mono (by have := Nat.cast_nonneg (α := ℝ) n; simpa only [Nat.cast_one] using le_add_of_nonneg_left this)
    simpa only [Nat.cast_one] using memSobolev_nat_product 1 g h1
  · rw [perturbedHelmholtz_cutoff]
    have hl := memSobolev_nat_product n g (matrixLowerOrder_memSobolev n b L v c K hu)
    rw [map_add] at hf
    have hp := hf.sub hl
    rw [add_sub_cancel_right] at hp
    exact hp.add (localizationError_memSobolev n a g hu)

end TamingCompatibility.HilbertSobolev

end

end OAI
