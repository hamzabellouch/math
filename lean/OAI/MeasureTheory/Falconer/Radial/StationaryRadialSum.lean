import OAI.MeasureTheory.Falconer.Radial.SignedRadialKernel

namespace OAI

/-! # Exact finite radial expansion of the two full-sphere approximants -/

namespace Falconer
open Set MeasureTheory

noncomputable def stationaryPoleTerm (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (ε : Bool) : ℂ :=
  ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*stationaryPhase (stationarySign ε*Λ)*
    signedStationaryCoefficient m j Λ B e ε

theorem stationarySphereApprox_pole_sum (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    stationarySphereApprox m J Λ B e =
      ∑ ε : Bool, ∑ j ∈ Finset.range J, stationaryPoleTerm m j Λ B e ε := by
  rw [stationarySphereApprox_signed m J hΛ]
  simp only [Fintype.sum_bool,stationaryPoleTerm,stationarySign,Bool.false_eq_true,
    ite_true,ite_false,neg_one_mul,one_mul,Finset.mul_sum,mul_add]
  ring_nf

theorem stationaryPoleTerm_radial_product (m j k : ℕ) (Ψ : ℝ → ℝ)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ s : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hs : 0 < s)
    (ε η : Bool) :
    (Ψ s:ℂ)*stationaryPoleTerm m j (R*s*d₁) B e ε*
      stationaryPoleTerm m k (R*s*d₂) G f η =
    stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s := by
  let p : ℝ := ((m+2:ℕ):ℝ)/2
  have hpow (d : ℝ) (hd : 0 < d) : (R*s*d)^(-p) = (R*d)^(-p)*s^(-p) := by
    rw [show R*s*d = (R*d)*s by ring,Real.mul_rpow (mul_pos hR hd).le hs.le]
  have hpowers : s^(-p)*(s^j)⁻¹*s^(-p)*(s^k)⁻¹ =
      s^(-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) := by
    rw [← Real.rpow_natCast s j,← Real.rpow_neg hs.le,
      ← Real.rpow_natCast s k,← Real.rpow_neg hs.le,
      ← Real.rpow_add hs,← Real.rpow_add hs,← Real.rpow_add hs]
    congr 1
    dsimp [p]
    ring
  have hphase : stationaryPhase (stationarySign ε*(R*s*d₁))*
      stationaryPhase (stationarySign η*(R*s*d₂)) =
      stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s) := by
    rw [stationaryPhase_mul]
    congr 1
    ring
  simp only [stationaryPoleTerm,neg_div]
  change (Ψ s:ℂ)*
    ((((R*s*d₁)^(-p):ℝ):ℂ)*stationaryPhase (stationarySign ε*(R*s*d₁))*
      signedStationaryCoefficient m j (R*s*d₁) B e ε)*
    ((((R*s*d₂)^(-p):ℝ):ℂ)*stationaryPhase (stationarySign η*(R*s*d₂))*
      signedStationaryCoefficient m k (R*s*d₂) G f η) = _
  rw [hpow d₁ hd₁,hpow d₂ hd₂,
    signedStationaryCoefficient_scale,signedStationaryCoefficient_scale]
  have halgebra : (Ψ s:ℂ)*
      ((((R*d₁)^(-p)*s^(-p):ℝ):ℂ)*stationaryPhase (stationarySign ε*(R*s*d₁))*
        (((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d₁) B e ε))*
      ((((R*d₂)^(-p)*s^(-p):ℝ):ℂ)*stationaryPhase (stationarySign η*(R*s*d₂))*
        (((s^k)⁻¹:ℝ)*signedStationaryCoefficient m k (R*d₂) G f η)) =
      (stationaryPhase (stationarySign ε*(R*s*d₁))*
        stationaryPhase (stationarySign η*(R*s*d₂)))*
      (((R*d₁)^(-p)*(R*d₂)^(-p):ℝ):ℂ)*
      (signedStationaryCoefficient m j (R*d₁) B e ε*
        signedStationaryCoefficient m k (R*d₂) G f η)*
      ((Ψ s*(s^(-p)*(s^j)⁻¹*s^(-p)*(s^k)⁻¹):ℝ):ℂ) := by
    push_cast
    ring
  rw [halgebra,hphase,hpowers]
  dsimp only [signedRadialCoefficient,PlanarFalconer.radialStationaryProfile,p]
  push_cast
  ring_nf

theorem stationarySphereApprox_radial_sum (m J : ℕ) (Ψ : ℝ → ℝ)
    (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (s : ℝ) :
    (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d₁) B e*
      stationarySphereApprox m J (R*s*d₂) G f =
    ∑ ε : Bool, ∑ j ∈ Finset.range J, ∑ η : Bool, ∑ k ∈ Finset.range J,
      stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
        signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s := by
  by_cases hs : 0 < s
  · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd₁),
      stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd₂)]
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ε _
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro k _
    exact stationaryPoleTerm_radial_product m j k Ψ B G e f hR hd₁ hd₂ hs ε η
  · have hz : Ψ s = 0 := by
      by_contra hn
      have hp := (hsupp s hn).1
      linarith
    simp only [hz,Complex.ofReal_zero,zero_mul,signedRadialCoefficient,
      PlanarFalconer.radialStationaryProfile,mul_zero,Complex.ofReal_zero,
      Finset.sum_const_zero]

end Falconer

end OAI
