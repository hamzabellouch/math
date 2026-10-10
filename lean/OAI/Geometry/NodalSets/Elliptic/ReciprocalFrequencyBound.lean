import OAI.Geometry.NodalSets.Elliptic.ReciprocalDerivativeBound

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reciprocal_frequency_bound (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (f : E → ℝ), ContDiff ℝ ∞ f → ∀ (x : E) (N H : ℝ),
      1 ≤ N → 0 < H →
      (1/2:ℝ)*(N^128)⁻¹*H^2 ≤ f x →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+8)*H^2) →
      ‖iteratedFDeriv ℝ r (fun y ↦ (f y)⁻¹) x‖ ≤ C*N^(137*r+128)*(H^2)⁻¹ := by
  obtain ⟨C,hC,hb⟩ := reciprocal_derivative_bound (E := E) r
  let B : ℝ := max 1 (2*A)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBA : 2*A ≤ B := le_max_right _ _
  refine ⟨2*C*B^r,by positivity,?_⟩
  intro f hf x N H hN hH hl hu
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hf0 : 0 < f x := lt_of_lt_of_le (by positivity) hl
  have hratio (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ |f x| * (B*N^137)^i := by
    rw [abs_of_pos hf0]
    have hpow : N^(i+136) ≤ N^(137*i) := by gcongr; omega
    have hBi : 2*A ≤ B^i := hBA.trans (le_self_pow₀ hB1 (by omega))
    calc
      _ ≤ A*N^(i+8)*H^2 := hu i hi hir
      _ = ((1/2:ℝ)*(N^128)⁻¹*H^2)*(2*A*N^(i+136)) := by
        rw [show i+136 = (i+8)+128 by omega,pow_add]
        field_simp
        ring
      _ ≤ f x * (2*A*N^(i+136)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _ ≤ f x * (B^i*N^(137*i)) := by gcongr
      _ = f x * (B*N^137)^i := by rw [mul_pow,← pow_mul]
  have hinv : |f x|⁻¹ ≤ 2*N^128*(H^2)⁻¹ := by
    rw [abs_of_pos hf0]
    calc
      (f x)⁻¹ ≤ ((1/2:ℝ)*(N^128)⁻¹*H^2)⁻¹ := (inv_le_inv₀ hf0 (by positivity)).mpr hl
      _ = _ := by field_simp
  have h := hb f hf x hf0.ne' (B*N^137) (by positivity) hratio
  refine h.trans ?_
  calc
    C*|f x|⁻¹*(B*N^137)^r ≤ C*(2*N^128*(H^2)⁻¹)*(B*N^137)^r := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul,pow_add]; ring

end
end Yau.Geometry

end OAI
