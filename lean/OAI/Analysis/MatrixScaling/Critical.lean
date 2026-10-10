import OAI.Analysis.MatrixScaling.Minimizer
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Log-determinant derivatives, critical points, and normalized tuple relations. -/

noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {d : ℕ}

theorem posDef_iff_decreasing_pos {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    P.PosDef ↔ ∀ i, 0 < decreasingEigenvalues hP i := by
  constructor
  · intro h i; exact decreasingEigenvalues_pos h i
  · intro h
    apply hP.posDef_iff_eigenvalues_pos.mpr
    intro i
    have hi := h ((spectralIndex d).symm i)
    rw [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at hi
    exact hi

theorem isOpen_posDef_hermitian : IsOpen {P : HermitianMatrices d | P.val.PosDef} := by
  have he : {P : HermitianMatrices d | P.val.PosDef} =
      ⋂ i : Fin d, {P : HermitianMatrices d | 0 < decreasingEigenvalues P.property i} := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, posDef_iff_decreasing_pos P.property]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (continuous_decreasingEigenvalues i)

/-- A Hermitian direction remains in the positive cone near a positive
point, providing the open domain needed for the critical-point argument. -/
theorem eventually_posDef_add_smul {P K : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (hK : K.IsHermitian) :
    ∀ᶠ u : ℝ in 𝓝 0, (P+(u : ℂ) • K).PosDef := by
  have hline (u : ℝ) : (P+(u : ℂ) • K).IsHermitian := by
    change (P+(u : ℂ) • K).conjTranspose = P+(u : ℂ) • K
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hP.1.eq, hK.eq]
    congr 1
    simp
  let f : ℝ → HermitianMatrices d := fun u => ⟨P+(u : ℂ) • K, hline u⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hm : f 0 ∈ {P : HermitianMatrices d | P.val.PosDef} := by simpa [f] using hP
  exact hf.continuousAt (isOpen_posDef_hermitian.mem_nhds hm)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Polynomial
namespace Kaplansky
variable {d : ℕ}

/-- Jacobi's directional formula, derived from the polynomial determinant
expansion at the identity and an actual inverse factorization. -/
theorem hasDerivAt_det_add_smul (P K : Matrix (Fin d) (Fin d) ℂ) (hP : IsUnit P) :
    HasDerivAt (fun z : ℂ => (P+z • K).det) (P.det * (P⁻¹*K).trace) 0 := by
  let M := P⁻¹*K
  let p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det
  have hd := p.hasDerivAt (0 : ℂ)
  have hp : p.derivative.eval 0 = M.trace := Matrix.derivative_det_one_add_X_smul M
  rw [hp] at hd
  have hev (z : ℂ) : p.eval z = (1+z • M).det := by
    simp only [p, eval_det]
    congr 1
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm]
  have hi : P*P⁻¹=1 := Matrix.mul_nonsing_inv P (P.isUnit_iff_isUnit_det.mp hP)
  have hf : (fun z : ℂ => (P+z • K).det) = fun z => P.det * p.eval z := by
    funext z
    rw [hev, ← Matrix.det_mul]
    congr 1
    dsimp [M]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hi, Matrix.one_mul]
  rw [hf]
  exact hd.const_mul P.det

theorem hasDerivAt_log_det_add_smul {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (K : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun u : ℝ => Real.log (P+(u : ℂ) • K).det.re)
      (P⁻¹*K).trace.re 0 := by
  have hd := (hasDerivAt_det_add_smul P K hP.isUnit).real_of_complex
  have hn : (P+(↑(0 : ℝ) : ℂ) • K).det.re ≠ 0 := by
    simpa using ne_of_gt (posDef_det_re_pos hP)
  have hlog := hd.log hn
  have him : P.det.im = 0 := hP.posSemidef.det_nonneg.2.symm
  have hv : (P.det * (P⁻¹*K).trace).re / (P+(↑(0 : ℝ) : ℂ) • K).det.re =
      (P⁻¹*K).trace.re := by
    simp only [Complex.ofReal_zero, zero_smul, add_zero, Complex.mul_re, him, zero_mul, sub_zero]
    exact mul_div_cancel_left₀ _ (ne_of_gt (posDef_det_re_pos hP))
  rw [hv] at hlog
  exact hlog

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

def scalingAdjoint (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, (T i).conjTranspose * Q * T i

theorem scalingAdjoint_trace (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin d) (Fin d) ℂ) :
    (scalingAdjoint T Q * K).trace = (Q * scalingMap T K).trace := by
  simp only [scalingAdjoint, scalingMap, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem scalingAdjoint_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {Q : Matrix (Fin r) (Fin r) ℂ} (hQ : Q.PosSemidef) :
    (scalingAdjoint T Q).PosSemidef :=
  Matrix.posSemidef_sum _ (fun i _ => hQ.conjTranspose_mul_mul_same (T i))

theorem hasDerivAt_scalingPotential {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (K : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K))
      (((1+scalingMap T P)⁻¹ * scalingMap T K).trace.re - (3/2)*(P⁻¹*K).trace.re) 0 := by
  have hQ : (1+scalingMap T P).PosDef :=
    Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hP.posSemidef)
  have hd := (hasDerivAt_log_det_add_smul hQ (scalingMap T K)).sub
    ((hasDerivAt_log_det_add_smul hP K).const_mul (3/2))
  have he : (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K)) =
      (fun u : ℝ => Real.log (1+scalingMap T P+(u : ℂ) • scalingMap T K).det.re) -
      (fun u : ℝ => (3/2)*Real.log (P+(u : ℂ) • K).det.re) := by
    funext u
    simp only [scalingPotential, Pi.sub_apply]
    congr 3
    simp [scalingMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib,
      Finset.smul_sum, add_assoc]
  rw [he]
  exact hd

theorem scaling_minimizer_critical (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (hmin : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R) :
    scalingAdjoint T (1+scalingMap T P)⁻¹ = (3/2 : ℂ) • P⁻¹ := by
  let Q := 1+scalingMap T P
  let C := scalingAdjoint T Q⁻¹ - (3/2 : ℂ) • P⁻¹
  have hQ : Q.PosDef := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hP.posSemidef)
  have hC : C.IsHermitian := by
    change (scalingAdjoint T Q⁻¹ - (3/2 : ℂ) • P⁻¹).conjTranspose = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      (scalingAdjoint_positive T hQ.inv.posSemidef).1.eq, hP.inv.1.eq]
    norm_num
    rfl
  have hdirection (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian) :
      ((C*K).trace).re = 0 := by
    have hlocal : IsLocalMin (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K)) 0 := by
      filter_upwards [eventually_posDef_add_smul hP hK] with u hu
      simpa only [Complex.ofReal_zero, zero_smul, add_zero] using hmin _ hu
    have hd := hlocal.hasDerivAt_eq_zero (hasDerivAt_scalingPotential hP T K)
    have he : (C*K).trace = (Q⁻¹*scalingMap T K).trace - (3/2 : ℂ)*(P⁻¹*K).trace := by
      simp only [C, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
        scalingAdjoint_trace, smul_eq_mul]
    rw [he]
    norm_num [Complex.sub_re, Complex.mul_re]
    exact hd
  have hr := hdirection C hC
  have hpos : (C.conjTranspose*C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have him : (C*C).trace.im = 0 := by
    have ht := hpos.trace_nonneg
    rw [hC.eq] at ht
    exact ht.2.symm
  have hz : (C.conjTranspose*C).trace = 0 := by
    rw [hC.eq]
    apply Complex.ext
    · exact hr
    · exact him
  have hzero : C = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  exact sub_eq_zero.mp hzero

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def normalizedTuple (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    Fin n → Matrix (Fin r) (Fin d) ℂ :=
  fun i => (Real.sqrt (2/3 : ℝ) : ℂ) • (J*T i*A)

theorem normalizedTuple_column (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    (∑ i, (normalizedTuple T A J i).conjTranspose * normalizedTuple T A J i) =
      (2/3 : ℂ) • (A.conjTranspose * scalingAdjoint T (J.conjTranspose*J) * A) := by
  have hs : (Real.sqrt (2/3 : ℝ) : ℂ) * star (Real.sqrt (2/3 : ℝ) : ℂ) = (2/3 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [normalizedTuple, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, scalingAdjoint, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem normalizedTuple_row (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    (∑ i, normalizedTuple T A J i * (normalizedTuple T A J i).conjTranspose) =
      (2/3 : ℂ) • (J * scalingMap T (A*A.conjTranspose) * J.conjTranspose) := by
  have hs : star (Real.sqrt (2/3 : ℝ) : ℂ) * (Real.sqrt (2/3 : ℝ) : ℂ) = (2/3 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [normalizedTuple, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, scalingMap, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Kaplansky

end

end OAI
