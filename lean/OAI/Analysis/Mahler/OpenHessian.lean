import OAI.Analysis.Mahler.HolomorphicRegularity
import OAI.Analysis.Mahler.MassTarget

namespace OAI
open Complex Matrix
open scoped BigOperators Topology ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

lemma diff_numerator_of_open {f : ι → E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) : DifferentiableAt ℝ (numerator f v) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ)).mul
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ))

lemma dbar_numerator_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (numerator f v) x w = ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  change dbar (fun y => ∑ j, conj (f j y) * fderiv ℂ (f j) y v) x w = _
  rw [dbar_sum (f := fun j y => conj (f j y) * fderiv ℂ (f j) y v) (fun j => (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ)).mul
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ))
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ),
    dbar_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ),
    dz_holomorphic ((hf j x hx).differentiableAt (hU.mem_nhds hx)), dbar_holomorphic (differentiableAt_fderiv_apply_of_open hU hx (hf j))]
  simp

/-- Actual mixed Wirtinger derivative of the squared norm. -/
theorem mixed_energy_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (fun y => dz (energy f) y v) x w =
      ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℂ (f j) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)
  have he : (fun y => dz (energy f) y v) =ᶠ[𝓝 x] numerator f v := by
    filter_upwards [hh] with y hy
    exact dz_energy (fun j => hy j)
  rw [dbar_congr_nhds he, dbar_numerator_of_open hU hx hf]

/-- Actual mixed derivative of the real logarithm, on the positive tau domain. -/
theorem mixed_logTau_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    dbar (fun y => dz (logTau f) y v) x w =
      ((tau f x : ℂ) * (∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v)
        - (∑ j, conj (f j x) * fderiv ℂ (f j) x v) *
          (∑ j, conj (fderiv ℂ (f j) x w) * f j x)) / (tau f x : ℂ)^2 := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℂ (f j) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)
  have hc : ContinuousAt (tau f) x := by
    have h := Complex.continuous_re.continuousAt.comp
      (differentiable_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx)))).continuousAt
    simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h
  have hp : ∀ᶠ y in 𝓝 x, 0 < tau f y := hc.eventually (lt_mem_nhds ht)
  have he : (fun y => dz (logTau f) y v) =ᶠ[𝓝 x]
      (fun y => numerator f v y / energy f y) := by
    filter_upwards [hh, hp] with y hy hty
    simpa only [numerator, energy_eq_tau] using dz_logTau
      (v := v) (fun j => hy j) hty
  rw [dbar_congr_nhds he, dbar_div (diff_numerator_of_open hU hx hf)
    (differentiable_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx)))) (by
      rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht),
    dbar_numerator_of_open hU hx hf, dbar_energy (fun j => ((hf j x hx).differentiableAt (hU.mem_nhds hx))), energy_eq_tau]
  simp only [numerator]
  ring

omit fintypeKappa in
lemma complexHessian_logTau_eq_of_open [Fintype κ] {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    complexHessian (logTau f) x e =
      kernelMatrix (fun j => f j x) (fun i j => fderiv ℂ (f j) x (e i)) := by
  ext i j
  exact mixed_logTau_of_open hU hx hf ht

theorem complexHessian_logTau_posSemidef_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    (complexHessian (logTau f) x e).PosSemidef := by
  rw [complexHessian_logTau_eq_of_open e hU hx hf ht]
  exact kernelMatrix_posSemidef _ _

omit fintypeKappa in
lemma complexHessian_energy_eq_gram_of_open [Fintype κ] {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    complexHessian (energy f) x e = (jacobian f x e)ᴴ * jacobian f x e := by
  ext i j
  exact mixed_energy_of_open hU hx hf

theorem complexHessian_energy_posSemidef_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    (complexHessian (energy f) x e).PosSemidef := by
  rw [complexHessian_energy_eq_gram_of_open e hU hx hf]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sourceHessian_logTau_det_nonneg_of_open [DecidableEq κ]
    {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    0 ≤ (sourceHessian (logTau f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact (complexHessian_logTau_posSemidef_of_open e hU hx hf ht).det_nonneg

theorem sourceHessian_energy_det_nonneg_of_open [DecidableEq κ]
    {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    0 ≤ (sourceHessian (energy f) x e).det := by
  rw [sourceHessian, Matrix.det_transpose]
  exact (complexHessian_energy_posSemidef_of_open e hU hx hf).det_nonneg

/-- The mass density is nonnegative under the mass hypotheses. -/
theorem MassHypotheses.massDensity_nonneg {n N m : ℕ} {U : Set (ComplexEuclidean n)}
    {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : MassHypotheses n N m U f G) {z : ComplexEuclidean n} (hz : z ∈ U) :
    0 ≤ massDensity f z := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact (Complex.nonneg_iff.mp (sourceHessian_energy_det_nonneg_of_open _
    h.open_domain hz h.holomorphic)).1

end Mahler

end OAI
