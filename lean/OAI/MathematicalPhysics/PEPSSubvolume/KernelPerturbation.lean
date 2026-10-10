import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.SpectralPowers

namespace OAI

/-! Zero-eigenspace perturbations and superquadratic normalization. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.KernelPerturbation
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def kernel (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) : Matrix ι ι ℂ :=
  spectralHom U (fun i => if e i = 0 then 1 else 0)

def magnitude (e : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  if e i = 0 then |t| else e i

def phaseValue (e : ι → ℝ) (ζ : unitary ℂ) (t : ℝ) (i : ι) : ℂ :=
  if e i = 0 then (if t < 0 then -(ζ : ℂ) else (ζ : ℂ)) else 1

omit [Fintype ι] [DecidableEq ι] in
theorem phaseValue_unitary (e : ι → ℝ) (ζ : unitary ℂ) (t : ℝ) :
    (fun i => phaseValue e ζ t i) ∈ unitary (ι → ℂ) := by
  constructor
  · ext i
    change star (phaseValue e ζ t i) * phaseValue e ζ t i = 1
    by_cases hi : e i = 0
    · by_cases ht : t < 0
      · simp only [phaseValue, ite_eq_left hi, ite_eq_left ht, star_neg, neg_mul_neg]
        exact ζ.property.1
      · simp only [phaseValue, ite_eq_left hi, ite_eq_right ht]
        exact ζ.property.1
    · simp [phaseValue,hi]
  · ext i
    change phaseValue e ζ t i * star (phaseValue e ζ t i) = 1
    by_cases hi : e i = 0
    · by_cases ht : t < 0
      · simp only [phaseValue, ite_eq_left hi, ite_eq_left ht, star_neg, neg_mul_neg]
        exact ζ.property.2
      · simp only [phaseValue, ite_eq_left hi, ite_eq_right ht]
        exact ζ.property.2
    · simp [phaseValue,hi]

def perturbUnitary (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ)
    (ζ : unitary ℂ) (t : ℝ) : unitary (Matrix ι ι ℂ) :=
  ⟨spectralHom U (phaseValue e ζ t),
    Unitary.map_mem (spectralHom U) (phaseValue_unitary e ζ t)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem magnitude_nonneg (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (t : ℝ) (i : ι) :
    0 ≤ magnitude e t i := by
  unfold magnitude
  split
  · exact abs_nonneg t
  · exact he i

theorem magnitude_posSemidef (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (t : ℝ) :
    (spectralHom U (fun i => (magnitude e t i : ℂ))).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨magnitude_nonneg e he t i,rfl⟩

theorem perturb_factorization (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ)
    (ζ : unitary ℂ) (t : ℝ) :
    (perturbUnitary U e ζ t : Matrix ι ι ℂ) *
      spectralHom U (fun i => (magnitude e t i : ℂ)) =
    spectralHom U (fun i => (e i : ℂ)) + ((t : ℂ)*(ζ : ℂ)) • kernel U e := by
  change spectralHom U _ * spectralHom U _ = _
  unfold kernel
  rw [← map_mul, ← map_smul, ← map_add]
  congr 1
  ext i
  simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    phaseValue, magnitude]
  by_cases hi : e i = 0
  · simp only [hi, ite_eq_left, Complex.ofReal_zero, zero_add, mul_one]
    by_cases ht : t < 0
    · rw [ite_eq_left ht, abs_of_neg ht, Complex.ofReal_neg]
      ring
    · rw [ite_eq_right ht, abs_of_nonneg (le_of_not_gt ht)]
      ring
  · simp [hi]

omit [DecidableEq ι] in
theorem magnitude_power_sum (e : ι → ℝ) (p : ℝ) (hp : 0 < p)
    (hs : ∑ i, (e i)^p = 1) (t : ℝ) :
    ∑ i, (magnitude e t i)^p = 1 +
      (∑ i : ι, if e i = 0 then (1:ℝ) else 0) * |t|^p := by
  have heach (i : ι) : (magnitude e t i)^p =
      (e i)^p + (if e i = 0 then (1:ℝ) else 0)*|t|^p := by
    unfold magnitude
    by_cases hi : e i = 0
    · simp [hi, Real.zero_rpow (ne_of_gt hp)]
    · simp [hi]
  simp_rw [heach]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs]

end PolynomialPEPS.Subvolume.KernelPerturbation

open scoped BigOperators
namespace PolynomialPEPS.Subvolume.KernelNormalization

variable {ι : Type*} [Fintype ι]

def scale (S p : ℝ) : ℝ := S^(-(1/p))

theorem scale_pos (S p : ℝ) (hS : 0 < S) : 0 < scale S p :=
  Real.rpow_pos_of_pos hS _

theorem scale_power (S p : ℝ) (hS : 0 < S) (hp : p ≠ 0) :
    (scale S p)^p * S = 1 := by
  rw [scale, ← Real.rpow_mul hS.le]
  have he : -(1/p)*p = -1 := by field_simp
  rw [he, Real.rpow_neg_one, inv_mul_cancel₀ (ne_of_gt hS)]

theorem power_sum (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (S p : ℝ) (hS : 0 < S) (hp : p ≠ 0) (hs : ∑ i, (d i)^p = S) :
    ∑ i, (scale S p*d i)^p = 1 := by
  simp_rw [Real.mul_rpow (scale_pos S p hS).le (hd _)]
  rw [← Finset.mul_sum, hs, scale_power S p hS hp]

theorem scale_inv_sq_le (S p : ℝ) (hS : 1 ≤ S) (hp : 2 < p) :
    (scale S p)⁻¹^2 ≤ S := by
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  rw [scale, ← Real.rpow_neg hSp.le]
  simp only [neg_neg]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hSp.le]
  conv_rhs => rw [← Real.rpow_one S]
  apply Real.rpow_le_rpow_of_exponent_le hS
  have hp' : 0 < p := by linarith
  have he : (1/p)*2 = 2/p := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact (div_le_one hp').mpr (le_of_lt hp)

theorem norm_sq_bound (N M S p : ℝ) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hS : 1 ≤ S) (hp : 2 < p) (hb : scale S p * M ≤ N) :
    M^2 ≤ N^2*S := by
  have hspos := scale_pos S p (lt_of_lt_of_le zero_lt_one hS)
  have hm : M ≤ N*(scale S p)⁻¹ := by
    apply (le_div_iff₀ hspos).mpr
    simpa [mul_comm, div_eq_mul_inv] using hb
  have hm' : M^2 ≤ (N*(scale S p)⁻¹)^2 := by
    exact (sq_le_sq₀ hM (mul_nonneg hN (inv_nonneg.mpr hspos.le))).mpr hm
  rw [mul_pow] at hm'
  exact hm'.trans (mul_le_mul_of_nonneg_left (scale_inv_sq_le S p hS hp) (sq_nonneg N))

end PolynomialPEPS.Subvolume.KernelNormalization

namespace PolynomialPEPS.Subvolume.KernelPerturbation
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve
open PolynomialPEPS.Subvolume.KernelNormalization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cost (e : ι → ℝ) (p t : ℝ) : ℝ :=
  1 + (∑ i : ι, if e i = 0 then (1:ℝ) else 0) * |t|^p

omit [DecidableEq ι] in
theorem one_le_cost (e : ι → ℝ) (p t : ℝ) : 1 ≤ cost e p t := by
  unfold cost
  have hk : 0 ≤ ∑ i : ι, if e i = 0 then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun i _ => by split <;> norm_num)
  exact le_add_of_nonneg_right (mul_nonneg hk (Real.rpow_nonneg (abs_nonneg _) _))

def normalized (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) (p t : ℝ) : Matrix ι ι ℂ :=
  spectralHom U (fun i => ((scale (cost e p t) p * magnitude e t i : ℝ) : ℂ))

theorem normalized_posSemidef (U : unitary (Matrix ι ι ℂ))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (p t : ℝ) :
    (normalized U e p t).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  refine Complex.nonneg_iff.mpr ⟨?_,rfl⟩
  exact mul_nonneg (scale_pos _ _ (lt_of_lt_of_le zero_lt_one (one_le_cost e p t))).le
    (magnitude_nonneg e he t i)

theorem normalized_capacity (U : unitary (Matrix ι ι ℂ))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (p : ℝ) (hp : 0 < p)
    (hs : ∑ i, (e i)^p = 1) (t : ℝ) :
    ∑ i, ((normalized_posSemidef U e he p t).isHermitian.eigenvalues i)^p = 1 := by
  have hsum := sum_eigenvalues_spectralHom U
    (fun i => scale (cost e p t) p * magnitude e t i)
    (normalized_posSemidef U e he p t).isHermitian (fun x => x^p)
  apply hsum.trans
  exact power_sum (magnitude e t) (magnitude_nonneg e he t) (cost e p t) p
    (lt_of_lt_of_le zero_lt_one (one_le_cost e p t)) (ne_of_gt hp)
    (magnitude_power_sum e p hp hs t)

theorem normalized_eq_smul (U : unitary (Matrix ι ι ℂ))
    (e : ι → ℝ) (p t : ℝ) :
    normalized U e p t = (scale (cost e p t) p : ℂ) •
      spectralHom U (fun i => (magnitude e t i : ℂ)) := by
  unfold normalized
  rw [← map_smul]
  apply congrArg (spectralHom U)
  funext i
  exact Complex.ofReal_mul _ _

theorem normalized_factorization (U : unitary (Matrix ι ι ℂ))
    (e : ι → ℝ) (ζ : unitary ℂ) (p t : ℝ) :
    (perturbUnitary U e ζ t : Matrix ι ι ℂ) * normalized U e p t =
      (scale (cost e p t) p : ℂ) •
        (spectralHom U (fun i => (e i : ℂ)) + ((t : ℂ)*(ζ : ℂ)) • kernel U e) := by
  rw [normalized_eq_smul, mul_smul_comm, perturb_factorization]

end PolynomialPEPS.Subvolume.KernelPerturbation

end

end OAI
