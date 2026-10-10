import OAI.Analysis.Cotype.FiniteL2DualNorm

namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem probabilityL2Dual_norm {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    ‖probabilityL2Dual g‖ = cubeL2 (X →L[ℝ] ℝ) g := by
  rw [probabilityL2Dual, norm_smul, finiteL2Dual_norm, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), cubeL2_eq_piLp]

theorem cubeL2_dual_le_of_pairing {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ f : Cube n → X, |dualPairing f g| ≤ C*cubeL2 X f) :
    cubeL2 (X →L[ℝ] ℝ) g ≤ C := by
  rw [← probabilityL2Dual_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  let q := Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹)
  have hc : (0 : ℝ) < Fintype.card (Cube n) := by exact_mod_cast Fintype.card_pos
  have hq : q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (inv_pos.mpr hc))
  let f : Cube n → X := fun u => q⁻¹ • z u
  have he : probabilityL2Vector f = z := by
    ext u
    change q • (q⁻¹ • z u) = z u
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
  have hv : probabilityL2Dual g (probabilityL2Vector f) = dualPairing f g := by
    have he' := probabilityL2Dual_amplification (ContinuousLinearMap.id ℝ X) f g
    have hid : l2Amplification (ContinuousLinearMap.id ℝ X) (probabilityL2Vector f) = probabilityL2Vector f := by
      ext u; rfl
    rw [hid] at he'
    exact he'
  rw [← he, hv, probabilityL2Vector_norm]
  exact h f

theorem dualPairing_radProjection {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    dualPairing f (radProjection (X →L[ℝ] ℝ) g) = dualPairing (radProjection X f) g := by
  calc
    _ = ∑ i, average (fun ε => sign (ε i) * (moment (X →L[ℝ] ℝ) g i) (f ε)) := by
      simp [dualPairing, radProjection, rademacherSum, average_sum]
    _ = ∑ i, (moment (X →L[ℝ] ℝ) g i) (moment X f i) := by
      apply Finset.sum_congr rfl; intro i hi
      generalize moment (X →L[ℝ] ℝ) g i = φ
      simp [moment, average]
    _ = ∑ i, average (fun η => sign (η i) * g η (moment X f i)) := by
      apply Finset.sum_congr rfl; intro i hi
      generalize moment X f i = x
      simp [moment, average]
    _ = _ := by simp [dualPairing, radProjection, rademacherSum, average_sum]

theorem radProjection_dual_bound {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f) :
    ∀ (n : ℕ) (g : Cube n → (X →L[ℝ] ℝ)),
      cubeL2 (X →L[ℝ] ℝ) (radProjection (X →L[ℝ] ℝ) g) ≤ K*cubeL2 (X →L[ℝ] ℝ) g := by
  intro n g
  apply cubeL2_dual_le_of_pairing _ (mul_nonneg hK (cubeL2_nonneg g))
  intro f
  rw [dualPairing_radProjection]
  exact (dualPairing_bound _ _).trans (by
    have hh := mul_le_mul_of_nonneg_right (h n f) (cubeL2_nonneg g)
    simpa [mul_assoc, mul_right_comm K] using hh)

theorem radProjection_bound_of_dual {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (n : ℕ) (g : Cube n → (X →L[ℝ] ℝ)),
      cubeL2 (X →L[ℝ] ℝ) (radProjection (X →L[ℝ] ℝ) g) ≤ K*cubeL2 (X →L[ℝ] ℝ) g) :
    ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f := by
  intro n f
  obtain ⟨g,hg,he⟩ := exists_dualPairing_norming (radProjection X f)
  have hb := dualPairing_bound f (radProjection (X →L[ℝ] ℝ) g)
  rw [dualPairing_radProjection, he, abs_of_nonneg (cubeL2_nonneg _)] at hb
  have hd := (h n g).trans (mul_le_of_le_one_right hK hg)
  exact hb.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hd (cubeL2_nonneg f))

theorem kConvex_dual_iff : KConvex (X →L[ℝ] ℝ) ↔ KConvex X := by
  constructor
  · rintro ⟨K,hK,h⟩; exact ⟨K,hK,radProjection_bound_of_dual hK h⟩
  · rintro ⟨K,hK,h⟩; exact ⟨K,hK,radProjection_dual_bound hK h⟩

end Cotype

end

end OAI
