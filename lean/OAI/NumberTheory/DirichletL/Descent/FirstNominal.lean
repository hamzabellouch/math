import OAI.NumberTheory.DirichletL.Descent.FirstProfileIdentity

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
noncomputable section

def firstRootScale (s : Fin 9 → ℝ) : ℝ :=
  s 3 * Real.sqrt (s 4) * s 5 * Real.sqrt (s 7) * Real.sqrt (s 8)

theorem firstRootScale_pos (s : Fin 9 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < firstRootScale s := by
  unfold firstRootScale
  exact mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (Real.sqrt_pos.2 (hs 4)))
    (hs 5)) (Real.sqrt_pos.2 (hs 7))) (Real.sqrt_pos.2 (hs 8))

theorem firstNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (s q : Fin 9 → ℝ)
    (hs : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ) :
    firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ
      (fun i y => V i (y-Real.log (s i))) K q =
    ((firstRootScale s : ℝ):ℂ)⁻¹ *
      firstNormProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
        (fun i => q i/s i) := by
  have hl : (q 0/s 0)*(q 2/s 2)*(q 5/s 5)*(q 7/s 7) =
      q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7) := by ring
  have hr : (q 1/s 1)*(q 2/s 2)*(q 5/s 5)*(q 8/s 8) =
      q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8) := by ring
  have hk : (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))*(q 6/s 6)/
      ((q 3/s 3)*(q 4/s 4)*(q 5/s 5)^2*(q 7/s 7)*(q 8/s 8)) =
      K*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) := by
    field_simp [(hs 3).ne', (hs 4).ne', (hs 5).ne', (hs 6).ne', (hs 7).ne', (hs 8).ne']
  have hd : (q 3/s 3)*Real.sqrt (q 4/s 4)*(q 5/s 5)*
      Real.sqrt (q 7/s 7)*Real.sqrt (q 8/s 8) =
      (q 3*Real.sqrt (q 4)*q 5*Real.sqrt (q 7)*Real.sqrt (q 8))/firstRootScale s := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 7).le,Real.sqrt_div (hq 8).le]
    unfold firstRootScale
    ring
  unfold firstNormProfile
  simp only [Real.log_div (hq _).ne' (hs _).ne']
  rw [hl,hr,hk]
  have hdC : (↑(q 3/s 3):ℂ)*↑(Real.sqrt (q 4/s 4))*↑(q 5/s 5)*
      ↑(Real.sqrt (q 7/s 7))*↑(Real.sqrt (q 8/s 8)) =
      ((q 3:ℂ)*↑(Real.sqrt (q 4))*(q 5:ℂ)*↑(Real.sqrt (q 7))*↑(Real.sqrt (q 8)))/
        (firstRootScale s:ℂ) := by exact_mod_cast hd
  rw [hdC]
  have hDc : (firstRootScale s:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (firstRootScale_pos s hs).ne'
  field_simp [hDc]

end
end SevenEighths.InverseMoment

end OAI
