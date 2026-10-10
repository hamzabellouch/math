import OAI.MeasureTheory.Falconer.Angular.SignedStationaryRadial
import OAI.MeasureTheory.Falconer.Angular.StationaryRadialScaling
import OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryExpansion

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

noncomputable def stationarySign (plus : Bool) : ℝ := if plus then 1 else -1
noncomputable def signedStationaryTerm (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (Λ : ℝ) : ℂ :=
  Complex.exp (Complex.I*((stationarySign plus*Λ:ℝ):ℂ)) *
    ((Λ^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f 0 Λ

 theorem fullCircleStationaryExpansion_signed {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm true j f Λ) +
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm false j f Λ) := by
  rw [fullCircleStationaryExpansion_operators hΛ hf]
  simp only [signedStationaryTerm,stationarySign,signedStationaryJet,normalizedStationaryJet,
    ↓reduceIte,Bool.false_eq_true,one_mul,neg_one_mul,
    map_mul,map_sum,map_pow,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_neg,Finset.mul_sum,mul_assoc]
  simp [neg_mul,mul_neg]

 theorem signedStationaryJet_scale (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ A s : ℝ) :
    signedStationaryJet plus j f θ (A*s) = ((s⁻¹:ℝ):ℂ)^j * signedStationaryJet plus j f θ A := by
  cases plus <;> simp only [signedStationaryJet,normalizedStationaryJet,↓reduceIte,
    Bool.false_eq_true,mul_inv_rev,Complex.ofReal_mul,mul_pow,map_mul,map_pow,Complex.conj_ofReal]
  all_goals ring

 theorem signedStationaryRadialCoefficient_eq (Ψ : ℝ → ℝ) (plus₁ plus₂ : Bool)
    (j k : ℕ) (f g : ℝ → ℂ) (θ φ : ℝ) {A B s : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) :
    signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B s =
      (Ψ s : ℂ) * (((A*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus₁ j f θ (A*s) *
        (((B*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus₂ k g φ (B*s) := by
  have hp := congrArg (fun t : ℝ => (t:ℂ)) (stationary_radial_power j k hs)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv] at hp
  simp only [signedStationaryRadialCoefficient,radialStationaryProfile,
    signedStationaryJet_scale,Real.mul_rpow hA.le hs.le,Real.mul_rpow hB.le hs.le,
    Complex.ofReal_mul,Complex.ofReal_inv]
  rw [← hp]
  ring

 theorem signedStationaryTerm_product (Ψ : ℝ → ℝ) (plus₁ plus₂ : Bool)
    (j k : ℕ) (f g : ℝ → ℂ) {R d₁ d₂ s : ℝ}
    (hR : 0 < R) (h1 : 0 < d₁) (h2 : 0 < d₂) (hs : 0 < s) :
    (Ψ s : ℂ) * signedStationaryTerm plus₁ j f (R*d₁*s) *
      signedStationaryTerm plus₂ k g (R*d₂*s) =
      Complex.exp (Complex.I*((R*(stationarySign plus₁*d₁+stationarySign plus₂*d₂):ℝ):ℂ)*(s:ℂ)) *
        signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g 0 0 (R*d₁) (R*d₂) s := by
  rw [signedStationaryRadialCoefficient_eq Ψ plus₁ plus₂ j k f g 0 0
    (mul_pos hR h1) (mul_pos hR h2) hs]
  have he : Complex.exp (Complex.I*((stationarySign plus₁*(R*d₁*s):ℝ):ℂ)) *
      Complex.exp (Complex.I*((stationarySign plus₂*(R*d₂*s):ℝ):ℂ)) =
      Complex.exp (Complex.I*((R*(stationarySign plus₁*d₁+stationarySign plus₂*d₂):ℝ):ℂ)*(s:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold signedStationaryTerm
  rw [← he]
  ring

end PlanarFalconer

end OAI
