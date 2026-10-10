import Mathlib
import OAI.Geometry.PrescribedPotential.DeterminantOrder

namespace OAI

/-! Matrix Cofactor Order. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ComplexOrder Matrix.Norms.Elementwise Classical
namespace MongeAmpere
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

def cofactorQuadratic (H : Mat) (v : Fin d → ℂ) : ℝ :=
  (H.det * (star v ⬝ᵥ (H⁻¹ *ᵥ v))).re

lemma det_add_rankOne (H : Mat) (hH : IsUnit H.det) (v : Fin d → ℂ) (t : ℂ) :
    (H + t • Matrix.vecMulVec v (star v)).det = H.det + t * (H.det * (star v ⬝ᵥ (H⁻¹ *ᵥ v))) := by
  have hu : t • Matrix.vecMulVec v (star v) =
      Matrix.replicateCol Unit (t • v) * Matrix.replicateRow Unit (star v) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec, mul_assoc]
  rw [hu, Matrix.det_add_replicateCol_mul_replicateRow hH]
  rw [Matrix.det_unique (A := (1 + Matrix.replicateRow Unit (star v) * H⁻¹ *
    Matrix.replicateCol Unit (t • v)))]
  have hv : (Matrix.replicateRow Unit (star v) * H⁻¹ * Matrix.replicateCol Unit (t • v)) () () =
      t * (star v ⬝ᵥ (H⁻¹ *ᵥ v)) := by
    simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change H.det * (1 + (Matrix.replicateRow Unit (star v) * H⁻¹ * Matrix.replicateCol Unit (t • v)) () ()) = _
  rw [hv]
  ring

lemma det_re_add_rankOne (H : Mat) (hH : H.PosDef) (v : Fin d → ℂ) (t : ℝ) :
    (H + (t : ℂ) • Matrix.vecMulVec v (star v)).det.re = H.det.re + t * cofactorQuadratic H v := by
  rw [det_add_rankOne H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, cofactorQuadratic]

 

lemma cofactorQuadratic_mono {H K : Mat} (hH : H.PosDef) (hK : K.PosDef)
    (hKH : (K - H).PosSemidef) (v : Fin d → ℂ) :
    cofactorQuadratic H v ≤ cofactorQuadratic K v := by
  have hb (t : ℝ) (ht : 0 ≤ t) : H.det.re + t * cofactorQuadratic H v ≤
      K.det.re + t * cofactorQuadratic K v := by
    have ht' := (Matrix.posSemidef_vecMulVec_self_star v).smul
      (show (0 : ℂ) ≤ (t : ℂ) from Complex.nonneg_iff.mpr ⟨ht, rfl⟩)
    have hh : ((K + (t : ℂ) • Matrix.vecMulVec v (star v)) -
        (H + (t : ℂ) • Matrix.vecMulVec v (star v))).PosSemidef := by
      convert hKH using 1
      abel
    have hm := det_re_mono (hH.add_posSemidef ht') hh
    simpa only [det_re_add_rankOne H hH, det_re_add_rankOne K hK] using hm
  by_contra hn
  have hp : 0 < cofactorQuadratic H v - cofactorQuadratic K v := sub_pos.mpr (lt_of_not_ge hn)
  let t := (|K.det.re - H.det.re| + 1) / (cofactorQuadratic H v - cofactorQuadratic K v)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : t * (cofactorQuadratic H v - cofactorQuadratic K v) = |K.det.re - H.det.re| + 1 :=
    div_mul_cancel₀ _ hp.ne'
  have hh := hb t ht
  nlinarith [le_abs_self (K.det.re - H.det.re)]

lemma cofactorQuadratic_nonneg (H : Mat) (hH : H.PosDef) (v : Fin d → ℂ) :
    0 ≤ cofactorQuadratic H v := by
  exact (Complex.nonneg_iff.mp (mul_nonneg hH.det_pos.le
    (hH.inv.posSemidef.dotProduct_mulVec_nonneg v))).1

lemma cofactorQuadratic_smul (H : Mat) (hH : H.PosDef) (v : Fin d → ℂ)
    (hd : 0 < d) (c : ℝ) (hc : 0 < c) :
    cofactorQuadratic ((c : ℂ) • H) v = c ^ (d - 1) * cofactorQuadratic H v := by
  have hn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let : Invertible (c : ℂ) := invertibleOfNonzero hn
  have hi := Matrix.inv_smul H (c : ℂ) (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  have hp : (c : ℂ) ^ d * (c : ℂ)⁻¹ = (c : ℂ) ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
    rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
  simp only [cofactorQuadratic, Matrix.det_smul, Fintype.card_fin, hi, invOf_eq_inv,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [show (c : ℂ) ^ d * H.det * ((c : ℂ)⁻¹ * (star v ⬝ᵥ (H⁻¹ *ᵥ v))) =
    ((c : ℂ) ^ d * (c : ℂ)⁻¹) * (H.det * (star v ⬝ᵥ (H⁻¹ *ᵥ v))) by ring, hp,
    ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma cofactorQuadratic_segment {H K : Mat} (hH : H.PosDef) (hK : K.PosDef)
    (v : Fin d → ℂ) (hd : 0 < d) {s : ℝ} (hs : s ∈ Set.Ico 0 1) :
    (1 - s) ^ (d - 1) * cofactorQuadratic H v ≤
      cofactorQuadratic (((1 - s : ℝ) : ℂ) • H + (s : ℂ) • K) v := by
  have hc : (0 : ℂ) < ((1 - s : ℝ) : ℂ) := Complex.pos_iff.mpr ⟨sub_pos.mpr hs.2, rfl⟩
  have hp := hH.smul hc
  have hq := hK.posSemidef.smul
    (show (0 : ℂ) ≤ (s : ℂ) from Complex.nonneg_iff.mpr ⟨hs.1, rfl⟩)
  have hm := cofactorQuadratic_mono hp (hp.add_posSemidef hq)
    (show ((((1 - s : ℝ) : ℂ) • H + (s : ℂ) • K) - ((1 - s : ℝ) : ℂ) • H).PosSemidef by
      simpa only [add_sub_cancel_left] using hq) v
  rwa [cofactorQuadratic_smul H hH v hd (1 - s) (sub_pos.mpr hs.2)] at hm

end MongeAmpere

end
end

end OAI
