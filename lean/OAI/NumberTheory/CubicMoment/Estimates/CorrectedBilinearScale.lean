import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearMass

namespace OAI

/-! The logarithmic saving furnished by corrected Cauchy--Schwarz. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def correctedBilinearSum (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
    (cStar:ℂ)*dispersionModel B β u*
      (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
        ((norm a^(-1/6:ℝ):ℝ):ℂ))

lemma bilinear_error_log_saving {x : ℂ} {M K A L z E V : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (_hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : ‖x‖^2 ≤ E*V) (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖x‖ ≤ Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hsqA : (A^(5/6:ℝ))^2 = A^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (A^(5/6:ℝ)) 2,←Real.rpow_mul hA.le]
    norm_num
  have hsqL : (L^(5/6:ℝ))^2 = L^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (L^(5/6:ℝ)) 2,←Real.rpow_mul hL.le]
    norm_num
  have hAadd : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hid : (Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      (M*A*z^d)*(K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hM hK),hsqA,hsqL,
      pow_add,pow_mul]
    field_simp
    simp only [←pow_mul]
    rw [Nat.mul_comm 2 k,←hAadd]
    ring
  have hb := herror.trans (mul_le_mul henergy hmass hV (by positivity))
  rw [←hid] at hb
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp hb

theorem corrected_bilinear_log_saving (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R L z M K : ℝ} (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hcut : ∀ x, R < x → V x = 0)
    (hPV : ∀ a ∈ P, 1 ≤ V (norm a/A)) (k d : ℕ)
    (henergy : (∑ a ∈ P, ‖α a‖^2) ≤ M*A*z^d)
    (hmass : correctedSquareMass B β u V A ≤
      K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖correctedBilinearSum P B α β u‖ ≤
      Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  exact bilinear_error_log_saving hM hK hA hL hz k d
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (correctedSquareMass_nonneg B β u V hV A)
    (corrected_bilinear_mass_bound_sq P B α β u hP hB V hV hA hcut hPV)
    henergy hmass

end CubicFirstMoment

end

end OAI
