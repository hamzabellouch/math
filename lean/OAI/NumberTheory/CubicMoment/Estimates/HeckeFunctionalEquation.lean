import OAI.NumberTheory.CubicMoment.Estimates.HeckeSymmetry

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

def heckeCompleted (A k : ℝ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^s * Complex.Gamma (s+(k:ℂ)) * L s

/-- The precisely normalized functional-equation input, supplied for an
actual primitive character and its contragredient, away from the gamma
poles. The regular-point restriction is necessary because mathlib
totalizes Gamma at its poles; the analytic completion has removable
singularities there, whereas the pointwise product need not agree. -/
def HeckeFunctionalEquation (A k : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 →
    Complex.Gamma (1-s+(k:ℂ)) ≠ 0 →
    heckeCompleted A k L s = ε*heckeCompleted A k Ldual (1-s)

theorem hecke_uncompleted {A k : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A k ε L Ldual) (s : ℂ)
    (hG : Complex.Gamma (s+(k:ℂ)) ≠ 0)
    (hGdual : Complex.Gamma (1-s+(k:ℂ)) ≠ 0) :
    L s = ε*(A:ℂ)^(1-2*s) *
      (Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))) * Ldual (1-s) := by
  have ha : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hap : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ha)
  have hp : (A:ℂ)^s*(A:ℂ)^(1-2*s) = (A:ℂ)^(1-s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero hap hG)
  calc
    _ = ε*((A:ℂ)^(1-s)*Complex.Gamma (1-s+(k:ℂ))*Ldual (1-s)) := hFE s hG hGdual
    _ = _ := by
      field_simp [hG]
      rw [← hp]
      rw [show (1-s*2:ℂ) = 1-2*s by ring]
      ring

lemma hecke_conductor_phase {A : ℝ} (hA : 0 < A) (t τ : ℝ) :
    (A:ℂ)^(1-2*((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) =
      mellinPhase (t-τ) (A^2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne'),
    ← Complex.ofReal_log hA.le]
  unfold mellinPhase
  rw [Real.log_pow]
  congr 1
  push_cast
  ring

theorem hecke_symmetry_line {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ} (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (t τ : ℝ) :
    L ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
      ε*mellinPhase (t-τ) (A^2)*heckeGammaRatio k (τ-t)*
        Ldual ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I) := by
  have hg : Complex.Gamma (((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero]
    norm_num
    linarith
  have hgd : Complex.Gamma (1-((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,sub_zero,add_zero]
    norm_num
    linarith
  have h := hecke_uncompleted hA hFE ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) hg hgd
  rw [hecke_conductor_phase hA] at h
  have hs : 1-((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
      (1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by ring
  have htop : 1-((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)+(k:ℂ) =
      ((k+1/2:ℝ):ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  have hbot : ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)+(k:ℂ) =
      ((k+1/2:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [htop,hbot,hs] at h
  simpa only [heckeGammaRatio] using h

lemma hecke_scale_phase {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I) =
      (Real.sqrt Z:ℂ)*mellinPhase τ Z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne'),
    ← Complex.ofReal_log hZ.le,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hZ,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exact symmetry-line amplitude and scalar phase. This identity
keeps all conductor dependence outside the dual polynomial. -/
theorem hecke_symmetry_integrand {A Z k : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A k ε L Ldual) (W : ℂ → ℂ) (t τ : ℝ) :
    W ((1/2:ℂ)+(τ:ℂ)*Complex.I) * (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I) *
      L ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
    (Real.sqrt Z:ℂ) * W ((1/2:ℂ)+(τ:ℂ)*Complex.I) *
      heckeSymmetryFactor ε (A^2) Z k t τ *
        Ldual ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I) := by
  rw [hecke_scale_phase hZ,hecke_symmetry_line hA hk hFE]
  unfold heckeSymmetryFactor
  ring

lemma norm_hecke_symmetry_line {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} (hε : ‖ε‖ = 1) {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A k ε L Ldual) (t τ : ℝ) :
    ‖L ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)‖ =
      ‖Ldual ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I)‖ := by
  rw [hecke_symmetry_line hA hk hFE]
  simp only [norm_mul,hε,mellinPhase_norm,norm_heckeGammaRatio hk,one_mul]

end CubicFirstMoment

end

end OAI
