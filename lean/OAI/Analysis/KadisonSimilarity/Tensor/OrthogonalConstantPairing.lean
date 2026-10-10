import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

namespace OAI

/-! A bounded vector has zero constant pairing with an infinite orthogonal
family of fixed norm. This is the Hilbert-space step of the free-factor
center argument. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem orthonormal_constant_pairing_eq_zero (v : ℕ → H) (hv : Orthonormal ℂ v)
    (x : H) (z : ℂ) (hz : ∀ n, inner ℂ (v n) x = z) : z = 0 := by
  have hb (N : ℕ) : (N : ℝ) * ‖z‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [hz, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      hv.sum_inner_products_le (s := Finset.range N) x
  by_contra hne
  have hp : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ ^ 2 / ‖z‖ ^ 2)
  have hlt : ‖x‖ ^ 2 < (N : ℝ) * ‖z‖ ^ 2 := (div_lt_iff₀ hp).mp hN
  exact (not_lt_of_ge (hb N)) hlt

/-- The family need not be normalized before applying the argument. -/
theorem orthogonal_constant_pairing_eq_zero (v : ℕ → H) (κ : ℝ)
    (hv : ∀ i j, inner ℂ (v i) (v j) = if i = j then (κ : ℂ) ^ 2 else 0)
    (x : H) (z : ℂ) (hz : ∀ n, inner ℂ (v n) x = z) : z = 0 := by
  classical
  by_cases hk : κ = 0
  · have h0 : v 0 = 0 := by simpa [hk] using hv 0 0
    simpa only [h0, inner_zero_left] using (hz 0).symm
  have hkC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hs : starRingEnd ℂ ((κ : ℂ)⁻¹) = (κ : ℂ)⁻¹ := by
    change star ((κ : ℂ)⁻¹) = (κ : ℂ)⁻¹
    simp
  let w : ℕ → H := fun n => (κ : ℂ)⁻¹ • v n
  have hw : Orthonormal ℂ w := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [w, inner_smul_left, inner_smul_right, hs, hv]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      field_simp
    · simp [hij]
  have he : (κ : ℂ)⁻¹ * z = 0 := orthonormal_constant_pairing_eq_zero w hw x _ (fun n => by
    simp only [w, inner_smul_left, hs, hz])
  exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hkC)

end KadisonSimilarity

end

end OAI
