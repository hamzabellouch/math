import OAI.NumberTheory.CubicMoment.Angular.AngularTailHighOrdinaryNegligible
import OAI.NumberTheory.CubicMoment.Angular.AngularTailHighUpperNegligible
import OAI.NumberTheory.CubicMoment.Angular.AngularUpperLowTailUniform
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularFull

namespace OAI

/-! The literal fixed-angular Gauss height tail is negligible. One stopping
exponent and one height cap serve all four branches and the semiprime term. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem primeProductGaussTail_angular_isLittleO
    (hℓ : ℓ ≠ 0)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ}
    (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ m : ℕ,
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) :
    ∃ (η : ℝ) (Ct : ℕ), 0 < η ∧ η < 5/6 ∧ 8 ≤ Ct ∧
      (fun X => primeProductGaussTail ℓ (X^(1/6+η:ℝ)) ((1+Real.log X)^Ct) X)
        =o[atTop] firstMomentScale := by
  obtain ⟨κ₁,hκ₁,hκ₁small,hlow⟩ := angular_upperLowTail_isLittleO_uniform ℓ hℓ
    hpnt hMV hC hHuxley hVor hGamma
  obtain ⟨κ₂,hκ₂,_hκ₂small,hhigh⟩ := angular_tailHighUpperArity_isLittleO_uniform ℓ
    hpub hHuxley hperiod hMV hC hGI hGQ
  let κ := min κ₁ κ₂/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκone : κ ≤ κ₁ := by dsimp [κ]; linarith [min_le_left κ₁ κ₂]
  have hκtwo : κ ≤ κ₂ := by dsimp [κ]; linarith [min_le_right κ₁ κ₂]
  let ξ := κ/4
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξκ : ξ < κ/2 := by dsimp [ξ]; linarith
  have hξsmall : ξ < 1/100 := by dsimp [ξ]; linarith
  have hξz : ξ ≤ 2/5 := by linarith
  obtain ⟨m,hdecomp⟩ := angular_primeProductGaussTail_scale_decomposition ℓ hξ hξz
  obtain ⟨η₀,hη₀,_hη₀κ,hupperlow⟩ := hlow κ hκ hκone ξ hξ hξκ m
  obtain ⟨Ct₁,hordinarylow⟩ := angular_scaleFirstOrdinaryLowTail_isLittleO ℓ hℓ m hpnt hMV hC hHuxley
    hVor hGamma hξ hξsmall
  have hdata (i : Fin m) := angular_tailHighOrdinaryArity_isLittleO ℓ i hpnt hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ
  choose ct hordinaryhigh using hdata
  obtain ⟨Ct₂,hsemi⟩ := semiprimeGaussTailAngular_isLittleO ℓ hpub hHuxley hperiod hMV hC hGI hGQ
  let Ct := max 8 (max Ct₁ (max Ct₂ (Finset.univ.sup ct)))
  let η := min (1/6000) (η₀/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηsmall : η ≤ 1/6000 := min_le_left _ _
  have hηlow : η ≤ η₀/2 := (min_le_right _ _).trans (by linarith)
  have hCt : 8 ≤ Ct := le_max_left _ _
  let H := fun X : ℝ => X^(1/6+η:ℝ)
  let T := fun X : ℝ => (1+Real.log X)^Ct
  have hH : ∀ᶠ X : ℝ in atTop, 1 ≤ H X := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact Real.one_le_rpow hX (by linarith)
  have hHcap : ∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hHlow : ∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+η₀/2) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hHX : ∀ᶠ X : ℝ in atTop, H X ≤ X := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show (1/6+η:ℝ) ≤ 1 by linarith)
  have hTlog : ∀ᶠ X : ℝ in atTop, Real.log X ≤ T X := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
    exact (by linarith : Real.log X ≤ 1+Real.log X).trans
      (le_self_pow₀ hL (by omega : Ct ≠ 0))
  have hTpow (n : ℕ) (hn : n ≤ Ct) : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^n ≤ T X := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hn
  have h₁ := hordinarylow H T (hTpow Ct₁ ((le_max_left _ _).trans (le_max_right _ _))) hH hHX
  have h₂ : (fun X => ∑ i ∈ Finset.range m, angular_tailHighOrdinaryArity ℓ i ξ (H X) (T X) X)
      =o[atTop] firstMomentScale := by
    have hh := Asymptotics.IsLittleO.fun_sum (s := Finset.univ) (fun i _ =>
      hordinaryhigh i H T (hTpow (ct i)
        ((Finset.le_sup (f := ct) (Finset.mem_univ i)).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))) hH hHcap)
    apply hh.congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X =>
      Fin.sum_univ_eq_sum_range (fun i => angular_tailHighOrdinaryArity ℓ i ξ (H X) (T X) X) m)
  have h₃ := hupperlow H T hTlog hH hHlow
  have h₄ := Asymptotics.IsLittleO.fun_sum (s := Finset.range m) (fun i _ =>
    hhigh κ hκ hκtwo ξ hξ hξz i H T hTlog hH hHcap)
  have h₅ := hsemi Ct ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) H
    (hH.and hHcap)
  refine ⟨η,Ct,hη,by linarith,hCt,?_⟩
  apply ((((h₁.add h₂).add h₃).add h₄).sub h₅).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hdecomp] with X hx
  exact (hx κ (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
