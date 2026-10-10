import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Entire spectral exponentials and finite matrix functional calculus. -/

noncomputable section
open scoped BigOperators ComplexOrder
open PolynomialPEPS.PinnedEntropy

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
namespace PolynomialPEPS.Subvolume.SpectralCurve

variable {n : Type*} [Fintype n] [DecidableEq n]

def spectralHom (U : unitary (Matrix n n ℂ)) :
    (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toAlgHom := (Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toAlgHom.comp (Matrix.diagonalAlgHom ℂ)
  map_star' v := by
    change Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (star v)) =
      star (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal v))
    rw [← map_star]
    congr 1
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

@[simp] theorem spectralHom_apply (U : unitary (Matrix n n ℂ)) (v : n → ℂ) :
    spectralHom U v = (U : Matrix n n ℂ) * Matrix.diagonal v * star (U : Matrix n n ℂ) := rfl

def curve (U : unitary (Matrix n n ℂ)) (r : n → ℝ) (z : ℂ) : Matrix n n ℂ :=
  spectralHom U (fun i => Complex.exp (z * (r i : ℂ)))

@[simp] theorem curve_zero (U : unitary (Matrix n n ℂ)) (r : n → ℝ) :
    curve U r 0 = 1 := by
  change spectralHom U _ = 1
  simp only [zero_mul, Complex.exp_zero]
  exact (spectralHom U).map_one

theorem curve_add (U : unitary (Matrix n n ℂ)) (r : n → ℝ) (z w : ℂ) :
    curve U r (z+w) = curve U r z * curve U r w := by
  simp only [curve, add_mul, Complex.exp_add]
  exact (spectralHom U).map_mul _ _

theorem curve_star (U : unitary (Matrix n n ℂ)) (r : n → ℝ) (z : ℂ) :
    star (curve U r z) = curve U r (star z) := by
  rw [curve, ← map_star]
  congr 1
  ext i
  simp only [Pi.star_apply, RCLike.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem curve_mem_unitary (U : unitary (Matrix n n ℂ)) (r : n → ℝ)
    (z : ℂ) (hz : z.re = 0) : curve U r z ∈ unitary (Matrix n n ℂ) := by
  have hstar : star z = -z := by
    apply Complex.ext <;> simp [hz]
  constructor <;> rw [curve_star, hstar, ← curve_add] <;> simp

theorem norm_curve_le (U : unitary (Matrix n n ℂ)) (r : n → ℝ)
    (z : ℂ) (b : ℝ) (hb : ∀ i, z.re * r i ≤ b) :
    ‖curve U r z‖ ≤ Real.exp b := by
  apply (NonUnitalStarAlgHom.norm_apply_le (spectralHom U) _).trans
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos b).le).mpr
  intro i
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (hb i)

theorem curve_posSemidef (U : unitary (Matrix n n ℂ)) (r : n → ℝ) (x : ℝ) :
    (curve U r (x : ℂ)).PosSemidef := by
  have hdiag : (Matrix.diagonal (fun i => Complex.exp ((x : ℂ) * (r i : ℂ)))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ Complex.exp ((x : ℂ) * (r i : ℂ))
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    exact Complex.nonneg_iff.mpr ⟨(Real.exp_pos _).le, rfl⟩
  exact hdiag.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

theorem hasDerivAt_curve (U : unitary (Matrix n n ℂ)) (r : n → ℝ) (z : ℂ) :
    HasDerivAt (curve U r)
      (spectralHom U (fun i => (r i : ℂ) * Complex.exp (z * (r i : ℂ)))) z := by
  let S : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
    (spectralHom U).toAlgHom.toLinearMap.toContinuousLinearMap
  have h : HasDerivAt (fun w : ℂ => fun i => Complex.exp (w * (r i : ℂ)))
      (fun i => (r i : ℂ) * Complex.exp (z * (r i : ℂ))) z := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa [mul_comm] using ((hasDerivAt_id z).mul_const (r i : ℂ)).cexp
  exact S.hasFDerivAt.comp_hasDerivAt z h

@[simp] theorem hasDerivAt_curve_zero (U : unitary (Matrix n n ℂ)) (r : n → ℝ) :
    HasDerivAt (curve U r) (spectralHom U (fun i => (r i : ℂ))) 0 := by
  simpa using hasDerivAt_curve U r 0

@[simp] theorem trace_spectralHom (U : unitary (Matrix n n ℂ)) (v : n → ℂ) :
    Matrix.trace (spectralHom U v) = ∑ i, v i := by
  rw [spectralHom_apply, Matrix.trace_mul_comm, ← mul_assoc]
  simp only [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]

theorem sum_eigenvalues_spectralHom (U : unitary (Matrix n n ℂ)) (d : n → ℝ)
    (hM : (spectralHom U (fun i => (d i : ℂ))).IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (hM.eigenvalues i)) = ∑ i, f (d i) := by
  let M := spectralHom U (fun i => (d i : ℂ))
  have hchar : M.charpoly = (Matrix.diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [show M = (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
        star (U : Matrix n n ℂ) from rfl, Matrix.charpoly_mul_comm, ← mul_assoc]
    simp only [Unitary.coe_star_mul_self, one_mul]
  have hroots : M.charpoly.roots =
      Multiset.map (fun i => (d i : ℂ)) Finset.univ.val := by
    rw [hchar, Matrix.charpoly_diagonal]
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using
      Polynomial.roots_multiset_prod_X_sub_C
        (Finset.univ.val.map (fun i => (d i : ℂ)))
  have heigen := hM.roots_charpoly_eq_eigenvalues
  change M.charpoly.roots =
    Multiset.map (fun i => (hM.eigenvalues i : ℂ)) Finset.univ.val at heigen
  have hh := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum)
    (heigen.symm.trans hroots)
  simpa only [Multiset.map_map, Function.comp_def, Complex.ofReal_re,
    Finset.sum_map_val] using hh

theorem tracePower_curve_one (U : unitary (Matrix n n ℂ))
    (p : n → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (a : ℝ) (ha : 0 < a) :
    ∑ i, Real.rpow ((curve_posSemidef U
      (fun i => a / 2 * Real.log (p i)) 1).isHermitian.eigenvalues i) (2/a) = 1 := by
  let r := fun i => a / 2 * Real.log (p i)
  have hc : curve U r 1 = spectralHom U (fun i => (Real.exp (r i) : ℂ)) := by
    unfold curve
    congr 1
    ext i
    simp
  have hm : (spectralHom U (fun i => (Real.exp (r i) : ℂ))).IsHermitian :=
    hc ▸ (curve_posSemidef U r 1).isHermitian
  have heig := (curve_posSemidef U r 1).isHermitian.eigenvalues_eq_eigenvalues_iff hm
  have heq := heig.mpr (congrArg Matrix.charpoly hc)
  change ∑ i, Real.rpow ((curve_posSemidef U r 1).isHermitian.eigenvalues i) (2/a) = 1
  have hv := sum_eigenvalues_spectralHom U (fun i => Real.exp (r i)) hm
    (fun t => Real.rpow t (2/a))
  rw [heq, hv]
  suffices ∀ i, Real.rpow (Real.exp (r i)) (2/a) = p i by
    simpa only [this] using hsum
  intro i
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hmul : r i * (2/a) = Real.log (p i) := by
    dsimp [r]
    field_simp [ne_of_gt ha]
  rw [hmul, Real.exp_log (hp i)]

end PolynomialPEPS.Subvolume.SpectralCurve

end

end OAI
