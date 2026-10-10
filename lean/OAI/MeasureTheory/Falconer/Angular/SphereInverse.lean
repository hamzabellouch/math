import OAI.MeasureTheory.Falconer.Angular.SphereStationary
import OAI.MeasureTheory.Falconer.Measures.InverseSupport
import OAI.MeasureTheory.Falconer.Estimates.InverseBudget

namespace OAI

/-! # The actual outgoing inverse expansion on the prepared patch

The finite inverse amplitudes remove the outgoing coefficient series.
Their fixed patch support removes every incoming coefficient. All errors
have the same total frequency order and the same derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem stationary_weight_eq (Λ : ℝ) (j : ℕ) :
    ((Λ^(-(j : ℝ)) : ℝ) : ℂ) = ((Λ : ℂ)⁻¹)^j := by
  simp only [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,Complex.ofReal_inv,
    Complex.ofReal_pow,inv_pow]

theorem stationary_weight_mul {Λ : ℝ} (hΛ : 0 < Λ) {J j : ℕ} (hj : j ≤ J) :
    Λ^(-(j : ℝ))*Λ^(-((J-j : ℕ) : ℝ)) = Λ^(-(J : ℝ)) := by
  rw [← Real.rpow_add hΛ,← neg_add,← Nat.cast_add,Nat.add_sub_of_le hj]

noncomputable def inverseSphereSum (m J : ℕ) (Λ : ℝ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) : ℂ :=
  ∑ j ∈ Finset.range (J+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
    sphereOscillation Λ e (fun w => localInverseAmplitude m B j w)

theorem inverse_direct_sum (m J : ℕ) (Λ : ℝ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3))
    (he : ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) :
    (∑ j ∈ Finset.range (J+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
      directStationarySum m (J+1-j) Λ (localInverseAmplitude m B j) e) = B e := by
  simpa only [directStationarySum,stationary_weight_eq] using
    localInverseAmplitude_triangle m J B e (stationaryPatchMask_one m e he) ((Λ : ℂ)⁻¹)

theorem sphere_inverse_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)),
      ‖(e : Space (m+3))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseSphereSum m J Λ B e -
        Complex.exp (Complex.I*(Λ : ℂ))*B e‖ ≤
        A*Λ^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
  choose F hF hFb using fun k => sphere_stationary_expansion hgnomonic hquadratic m (k+1) (by omega)
  choose U hU hUb using fun j => localInverseAmplitude_scaled_budget m j
    (2*(J-j+1)+(m+2)+1)
  let A := ∑ j ∈ Finset.range (J+1), F (J-j)*U j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => mul_nonneg (hF (J-j)) (hU j))
  refine ⟨A,hA,?_⟩
  intro e he B hB C D hC hD hb Λ hΛ
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  let E : ℕ → ℂ := fun j => ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
    (p*sphereOscillation Λ e (fun w => localInverseAmplitude m B j w)-
      z*directStationarySum m (J+1-j) Λ (localInverseAmplitude m B j) e)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (J+1)) :
      ‖E j‖ ≤ F (J-j)*U j*Λ^(-((J+1 : ℕ) : ℝ))*C*D^(2*(J+1)+(m+2)+1) := by
    have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hN : J-j+1 = J+1-j := by omega
    have hder := hUb j B hB C D hC hD (fun l hl w => hb l (by omega) w)
    have hCj : 0 ≤ U j*C*D^(2*j) :=
      mul_nonneg (mul_nonneg (hU j) hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hinput : ∀ l ≤ 2*(J-j+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ l (localInverseAmplitude m B j) w‖ ≤ (U j*C*D^(2*j))*D^l := by
      intro l hl w
      apply (hder l hl w).trans_eq
      rw [pow_add]
      ring
    have hf := hFb (J-j) e (localInverseAmplitude m B j)
      (localInverseAmplitude_contDiff m hB j) (U j*C*D^(2*j)) D hCj hD hinput Λ hΛ
    have hz : directStationarySum m (J-j+1) Λ
        (antipodalConjugate (localInverseAmplitude m B j)) e = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [localInverseAmplitude_antipodal_coefficient_zero m j k B e he,mul_zero]
    rw [hz,mul_zero,star_zero,add_zero,hN] at hf
    have hw : ‖((Λ^(-(j : ℝ)) : ℝ) : ℂ)‖ = Λ^(-(j : ℝ)) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛp _)]
    dsimp only [E]
    rw [norm_mul,hw]
    apply (mul_le_mul_of_nonneg_left hf (Real.rpow_pos_of_pos hΛp _).le).trans_eq
    calc
      _ = F (J-j)*U j*C*(Λ^(-(j : ℝ))*Λ^(-((J+1-j : ℕ) : ℝ)))*
          D^(2*j+(2*(J+1-j)+(m+2)+1)) := by rw [pow_add]; ring
      _ = _ := by
        rw [stationary_weight_mul hΛp (by omega : j ≤ J+1),
          show 2*j+(2*(J+1-j)+(m+2)+1) = 2*(J+1)+(m+2)+1 by omega]
        ring
  have hsum : p*inverseSphereSum m J Λ B e-z*B e = ∑ j ∈ Finset.range (J+1), E j := by
    rw [← inverse_direct_sum m J Λ B e he]
    simp only [inverseSphereSum,Finset.mul_sum,← Finset.sum_sub_distrib,E]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change ‖p*inverseSphereSum m J Λ B e-z*B e‖ ≤ _
  rw [hsum]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hterm).trans_eq
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]

end Falconer

end OAI
