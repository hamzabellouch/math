import OAI.Analysis.Cuntz.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section

/-! Square approximation, square swap, and orthogonal additivity. -/

section
open scoped CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The scalar error estimate underlying approximate comparison of xx* and x*x. -/
theorem squareSwap_scalar_error {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    |t - (Real.sqrt (t+δ))⁻¹ * t * t * (Real.sqrt (t+δ))⁻¹| ≤ δ := by
  have hd : 0 < t+δ := add_pos_of_nonneg_of_pos ht hδ
  have hs : Real.sqrt (t+δ) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : t - (Real.sqrt (t+δ))⁻¹ * t * t * (Real.sqrt (t+δ))⁻¹ = t*δ/(t+δ) := by
    field_simp
    rw [Real.sq_sqrt hd.le]
    ring
  rw [he, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- A concrete functional-calculus approximation. No polar decomposition
or square-swap property of dimension functions is assumed. -/
theorem exists_squareSwap_approx (x : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖x * star x - v * (star x * x) * star v‖ < ε := by
  let b := x * star x
  have hb : 0 ≤ b := mul_star_self_nonneg x
  have hbsa : IsSelfAdjoint b := hb.isSelfAdjoint
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let f : ℝ → ℝ := fun t => (Real.sqrt (t+δ))⁻¹
  have hf : ContinuousOn f (spectrum ℝ b) := by
    apply ContinuousOn.inv₀ ((continuousOn_id.add continuousOn_const).sqrt)
    intro t ht
    exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hb ht) hδ)).ne'
  let L := cfc f b
  have hL : star L = L := (cfc_predicate f b : IsSelfAdjoint L).star_eq
  have he : cfc (fun t => t - f t * t * t * f t) b = b - L * b * b * L := by
    rw [cfc_sub (fun t : ℝ => t) (fun t => f t * t * t * f t) b continuousOn_id (((hf.mul continuousOn_id).mul continuousOn_id).mul hf)]
    rw [cfc_mul (fun t => f t * t * t) f b ((hf.mul continuousOn_id).mul continuousOn_id) hf]
    rw [cfc_mul (fun t => f t * t) (fun t : ℝ => t) b (hf.mul continuousOn_id) continuousOn_id]
    rw [cfc_mul f (fun t : ℝ => t) b hf continuousOn_id, cfc_id' ℝ b]
  refine ⟨L*x, ?_⟩
  have hn : ‖cfc (fun t => t - f t * t * t * f t) b‖ ≤ δ := by
    apply norm_cfc_le hδ.le
    intro t ht
    exact squareSwap_scalar_error (spectrum_nonneg_of_nonneg hb ht) hδ
  have he' : x * star x - (L*x) * (star x*x) * star (L*x) = b - L*b*b*L := by
    simp only [star_mul, hL, b, mul_assoc]
  rw [he', ← he]
  exact hn.trans_lt (half_lt_self hε)

end Kaplansky

end

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Cuntz square swapping is proved by norm approximants. -/
theorem cuntzLE_mul_star_self [DecidableEq ι] (x : CStarMatrix ι ι A) :
    CuntzLE (CStarMatrix.ofMatrix.symm (x * star x))
      (CStarMatrix.ofMatrix.symm (star x * x)) := by
  apply (CuntzLE.iff_approx _ _).mpr
  intro ε hε
  obtain ⟨v, hv⟩ := exists_squareSwap_approx x ε hε
  exact ⟨CStarMatrix.ofMatrix.symm v, hv⟩

theorem cuntzEquivalent_square_swap [DecidableEq ι] (x : CStarMatrix ι ι A) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (x * star x))
      (CStarMatrix.ofMatrix.symm (star x * x)) := by
  refine ⟨cuntzLE_mul_star_self x, ?_⟩
  simpa only [star_star] using cuntzLE_mul_star_self (star x)

/-- Rectangular Gram matrices of different sizes have the same Cuntz class. -/
theorem cuntzEquivalent_rectangular_gram (v : Matrix ι κ A) :
    CuntzEquivalent (v * v.conjTranspose) (v.conjTranspose * v) := by
  classical
  let X : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (Matrix.fromBlocks 0 v 0 0)
  have hleft : CStarMatrix.ofMatrix.symm (X * star X) =
      cuntzBlock (v * v.conjTranspose) (0 : Matrix κ κ A) := by
    change Matrix.fromBlocks 0 v 0 0 * (Matrix.fromBlocks 0 v 0 0).conjTranspose = _
    simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have hright : CStarMatrix.ofMatrix.symm (star X * X) =
      cuntzBlock (0 : Matrix ι ι A) (v.conjTranspose * v) := by
    change (Matrix.fromBlocks 0 v 0 0).conjTranspose * Matrix.fromBlocks 0 v 0 0 = _
    simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have h := cuntzEquivalent_square_swap X
  rw [hleft, hright] at h
  exact (cuntzEquivalent_block_zero _).symm.trans
    (h.trans ((cuntzEquivalent_block_comm _ _).trans (cuntzEquivalent_block_zero _)))

/-- Positives formed as either square have equal values under every
constructed dimension state; this is not an assumed quasitrace axiom. -/
theorem CuntzDimensionState.value_square_swap (d : CuntzDimensionState A) (n : ℕ)
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm (x * star x), mul_star_self_nonneg x⟩ =
      d.value ⟨n, CStarMatrix.ofMatrix.symm (star x * x), star_mul_self_nonneg x⟩ :=
  d.value_eq (cuntzEquivalent_square_swap x)

end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Orthogonality passes to actual positive square roots. -/
theorem sqrt_mul_sqrt_eq_zero_of_mul_eq_zero {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a*b = 0) : CFC.sqrt a * CFC.sqrt b = 0 := by
  have hsa : star a = a := ha.isSelfAdjoint.star_eq
  have hsb : star (CFC.sqrt b) = CFC.sqrt b := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have h1 : a * CFC.sqrt b = 0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    calc
      (a * CFC.sqrt b) * star (a * CFC.sqrt b) = a * b * a := by
        simp only [star_mul, hsa, hsb, mul_assoc]
        rw [← mul_assoc (CFC.sqrt b), CFC.sqrt_mul_sqrt_self b hb]
      _ = 0 := by rw [hab, zero_mul]
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hsa' : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  calc
    star (CFC.sqrt a * CFC.sqrt b) * (CFC.sqrt a * CFC.sqrt b) = CFC.sqrt b * (a * CFC.sqrt b) := by
      simp only [star_mul, hsa', hsb, mul_assoc]
      rw [← mul_assoc (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a ha]
    _ = 0 := by rw [h1, mul_zero]

/-- Orthogonal positive addition agrees with block addition in the Cuntz monoid. -/
theorem cuntzEquivalent_orthogonal_add {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (a+b))
      (cuntzBlock (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  let S := CFC.sqrt a
  let T := CFC.sqrt b
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hT : star T = T := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hST : S*T = 0 := sqrt_mul_sqrt_eq_zero_of_mul_eq_zero ha hb hab
  have hTS : T*S = 0 := by simpa only [star_mul, hS, hT, star_zero] using congrArg star hST
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  have hl : v * v.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    change S*star S + T*star T = a+b
    rw [hS, hT, CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
  have hr : v.conjTranspose * v =
      cuntzBlock (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (star S * S))
      (CStarMatrix.ofMatrix.symm (star S * T)) (CStarMatrix.ofMatrix.symm (star T * S))
      (CStarMatrix.ofMatrix.symm (star T * T)) = _
    rw [hS, hT, hST, hTS, CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
    rfl
  simpa only [hl, hr] using cuntzEquivalent_rectangular_gram v

theorem CuntzDimensionState.value_orthogonal_add (d : CuntzDimensionState A) (n : ℕ)
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ =
      d.value ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.value ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  rw [← d.value_add pa pb]
  exact d.value_eq ((cuntzEquivalent_orthogonal_add a b ha hb hab).trans
    (CuntzPositiveMatrix.add_equiv pa pb).symm)

end Kaplansky

end

end OAI
