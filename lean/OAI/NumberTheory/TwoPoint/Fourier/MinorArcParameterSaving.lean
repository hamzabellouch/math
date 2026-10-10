import OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicSieve
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicWindows

namespace OAI

/-! The minor-arc fourth-root estimate retains the freely chosen
Diophantine parameter. This permits a common parameter in both arcs. -/
namespace TwoPointCorrelations

open Finset Filter

lemma minor_arc_parameter_fourth_root (D S X H R W : ℝ)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hH : 0 < H)
    (hlogH : 1 ≤ Real.log H) (hlogR : 0 < Real.log R) (hW : 0 < W)
    (hbound : S^4 ≤ D*X^4*H^4*(1+Real.log (2*H))/(W*Real.log R^4)) :
    S ≤ (3*D+1)*X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R := by
  have hlog : 1+Real.log (2*H) ≤ 3*Real.log H := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hK : 1 ≤ 3*D+1 := by linarith
  have hKpow : 3*D ≤ (3*D+1)^4 := by
    have hh := pow_le_pow_right₀ hK (by omega : 1 ≤ 4)
    simp only [pow_one] at hh
    linarith
  have hroot : ((Real.log H/W)^(1/4:ℝ))^4=Real.log H/W := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ Real.log H/W)]
    norm_num
  have hs : S^4 ≤ 3*D*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 := by
    calc
      _ ≤ D*X^4*H^4*(1+Real.log (2*H))/(W*Real.log R^4) := hbound
      _ ≤ D*X^4*H^4*(3*Real.log H)/(W*Real.log R^4) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = _ := by
        rw [div_pow,mul_pow,mul_pow,hroot]
        field_simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ 3*D*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 := hs
    _ ≤ (3*D+1)^4*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 :=
      mul_le_mul_of_nonneg_right hKpow (by positivity)
    _ = _ := by ring

theorem minor_arc_dyadic_parameter_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ (P : Finset ℕ) (X H : ℕ), 1 ≤ H → H ≤ X → R ≤ X →
      1 ≤ Real.log (H:ℝ) →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ p ∧ p ≤ 2*R) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ (R:ℝ) → (R:ℝ) ≤ (H:ℝ)/W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q:ℝ) → (q:ℝ) ≤ (H:ℝ)/W →
      ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P ((X+H)/R+1) H 1 a c α k‖) ≤
        C*(X:ℝ)*H*(Real.log (H:ℝ)/W)^(1/4:ℝ)/Real.log (R:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := minor_arc_dyadic_bilinear_sieve
  refine ⟨3*D+1,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with R hbound hR
  intro P X H hH hHX hRX hlogH hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hH0 : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlogR : 0 < Real.log (R:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  exact minor_arc_parameter_fourth_root D _ X H R W hD.le (Nat.cast_nonneg X)
    hH0 hlogH hlogR (by linarith)
    (hbound P X H hH hHX hRX hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ)

end TwoPointCorrelations

end OAI
