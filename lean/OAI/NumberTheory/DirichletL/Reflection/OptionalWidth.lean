import OAI.NumberTheory.DirichletL.Reflection.CanonicalWidth
import OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem original_optional_terminal_saving
    (J I F B R Q₀ : Ideal O) (hJ : J≠0) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R))
    (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
    (e : A→Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    InverseTerminalWidths.reflectedExponent 0 H
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 0))
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 2))
      za v ell el (terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e) + O₀/2 + π ≤
        F₀ - cstar / 4 := by
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun a : A => completedLocalExponent J F a.val.val
  have hQ : B*F*R≠0 := mul_ne_zero (mul_ne_zero hB hF) hR
  have hj : (fun i => completedLocalExponent I F (G.ideal i))=j := by
    funext i
    exact poolPrimeFamily_fiber_exponent J I F (B*F*R) Q₀ hJ hI hQ hpower hmask i.val
  have hret' : v+3*ell+el≤terminalDualWidth Z H za Nstar G.ideal
      (fun i => completedLocalExponent I F (G.ideal i)) e+τ := by
    rw [hj]
    exact hret
  have hh := actual_terminal_saving I F B R hI hF hB hR G.ideal
    ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    (fun a => poolPrimeFamily_fiber_divides J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)
    (fun a => FreeReflection.pool_nonresidual I (B*F*R) Q₀
      (CanonicalRowCompletion.nonresidualPoolEquiv J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)) e
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    hM hO hz hzcap hv hl he hret' hc hmargin hd hη hτ hπ
  rw [hj,← frozenExtracted_eq_ideal G j e 0,← frozenExtracted_eq_ideal G j e 2] at hh
  convert hh using 1
  unfold InverseTerminalWidths.reflectedExponent
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
