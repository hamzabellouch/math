import OAI.Analysis.Mahler.Positivity

namespace OAI
open Complex Matrix
open scoped BigOperators ComplexOrder
local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

lemma pairing_sum_right (a : ι → ℂ) (B : κ → ι → ℂ) :
    pairing a (fun j => ∑ k, B k j) = ∑ k, pairing a (B k) := by
  simp only [pairing, Finset.mul_sum]
  rw [Finset.sum_comm]
lemma pairing_sum_left (a : ι → ℂ) (B : κ → ι → ℂ) :
    pairing (fun j => ∑ k, B k j) a = ∑ k, pairing (B k) a := by
  simp only [pairing, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma pairing_mul_right (a b : ι → ℂ) (r : ℂ) :
    pairing a (fun j => r * b j) = r * pairing a b := by
  simp [pairing, Finset.mul_sum, mul_left_comm]
lemma pairing_mul_left (a b : ι → ℂ) (r : ℂ) :
    pairing (fun j => r * b j) a = conj r * pairing b a := by
  simp [pairing, map_mul, Finset.mul_sum, mul_assoc]

lemma logKernel_sum_right (a b : ι → ℂ) (B : κ → ι → ℂ) :
    logKernel a b (fun j => ∑ k, B k j) = ∑ k, logKernel a b (B k) := by
  simp only [logKernel, pairing_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
lemma logKernel_sum_left (a b : ι → ℂ) (B : κ → ι → ℂ) :
    logKernel a (fun j => ∑ k, B k j) b = ∑ k, logKernel a (B k) b := by
  simp only [logKernel, pairing_sum_left, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
lemma logKernel_mul_right (a b c : ι → ℂ) (r : ℂ) :
    logKernel a b (fun j => r * c j) = r * logKernel a b c := by
  simp only [logKernel, pairing_mul_right]
  ring
lemma logKernel_mul_left (a b c : ι → ℂ) (r : ℂ) :
    logKernel a (fun j => r * b j) c = conj r * logKernel a b c := by
  simp only [logKernel, pairing_mul_left]
  ring

noncomputable def kernelMatrix (a : ι → ℂ) (B : κ → ι → ℂ) : Matrix κ κ ℂ :=
  fun i j => logKernel a (B i) (B j)

omit fintypeKappa in
lemma kernelMatrix_hermitian [Fintype κ] (a : ι → ℂ) (B : κ → ι → ℂ) :
    (kernelMatrix a B).IsHermitian := by
  ext i j
  exact logKernel_conj a (B j) (B i)

lemma kernelMatrix_quadratic (a : ι → ℂ) (B : κ → ι → ℂ) (c : κ → ℂ) :
    star c ⬝ᵥ (kernelMatrix a B *ᵥ c) =
      logKernel a (fun k => ∑ i, c i * B i k) (fun k => ∑ i, c i * B i k) := by
  rw [logKernel_sum_left]
  simp_rw [logKernel_mul_left, logKernel_sum_right, logKernel_mul_right]
  simp [dotProduct, mulVec, kernelMatrix, mul_comm]

lemma kernelMatrix_posSemidef (a : ι → ℂ) (B : κ → ι → ℂ) :
    (kernelMatrix a B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (kernelMatrix_hermitian a B)
  intro c
  rw [kernelMatrix_quadratic]
  exact logKernel_nonneg _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
/-- Mixed Hessian in a finite family of directions; the row is the conjugate index. -/
noncomputable def complexHessian (u : E → ℂ) (x : E) (e : κ → E) : Matrix κ κ ℂ :=
  fun i j => dbar (fun y => dz u y (e j)) x (e i)

omit fintypeKappa in
lemma complexHessian_logTau_eq [Fintype κ] {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    complexHessian (logTau f) x e =
      kernelMatrix (fun j => f j x) (fun i j => fderiv ℂ (f j) x (e i)) := by
  ext i j
  exact mixed_logTau_kernel hf ht

/-- PSD of the actual complex Hessian, with no assumed Hessian formula. -/
theorem complexHessian_logTau_posSemidef {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    (complexHessian (logTau f) x e).PosSemidef := by
  rw [complexHessian_logTau_eq e hf ht]
  exact kernelMatrix_posSemidef _ _

/-- The determinant is real and nonnegative, in the complex real-axis order. -/
theorem complexHessian_logTau_det_nonneg [DecidableEq κ]
    {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    0 ≤ (complexHessian (logTau f) x e).det :=
  (complexHessian_logTau_posSemidef e hf ht).det_nonneg

noncomputable def jacobian (f : ι → E → ℂ) (x : E) (e : κ → E) : Matrix ι κ ℂ :=
  fun j i => fderiv ℂ (f j) x (e i)

omit fintypeKappa in
lemma complexHessian_energy_eq_gram [Fintype κ] {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    complexHessian (energy f) x e =
      (jacobian f x e)ᴴ * jacobian f x e := by
  ext i j
  exact mixed_energy hf

theorem complexHessian_energy_posSemidef {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    (complexHessian (energy f) x e).PosSemidef := by
  rw [complexHessian_energy_eq_gram e hf]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem complexHessian_energy_det_nonneg [DecidableEq κ]
    {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    0 ≤ (complexHessian (energy f) x e).det :=
  (complexHessian_energy_posSemidef e hf).det_nonneg

/-- Complex Hessian indexing: row k is z_k, column l is bar z_l. -/
noncomputable def sourceHessian (u : E → ℂ) (x : E) (e : κ → E) : Matrix κ κ ℂ :=
  (complexHessian u x e).transpose

/-- The complex Hessian in this indexing has real nonnegative determinant. -/
theorem sourceHessian_logTau_det_nonneg [DecidableEq κ]
    {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    0 ≤ (sourceHessian (logTau f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact complexHessian_logTau_det_nonneg e hf ht

theorem sourceHessian_energy_det_nonneg [DecidableEq κ]
    {f : ι → E → ℂ} {x : E} (e : κ → E)
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    0 ≤ (sourceHessian (energy f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact complexHessian_energy_det_nonneg e hf

end Mahler

end OAI
