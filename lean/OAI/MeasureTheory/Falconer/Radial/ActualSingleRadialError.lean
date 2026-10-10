import OAI.MeasureTheory.Falconer.Angular.AngularStationaryRadialError
import OAI.MeasureTheory.Falconer.Angular.ActualFarCircleExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem uniform_actual_single_radial_error {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → ∀ x y : Fin 2 → Plane,
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    (4*(2:ℝ)^(-h) ≤ ‖x 0-y 0‖) → ∀ θ : Fin 2 → ℝ,
    (∀ l, x l-y l = ‖x l-y l‖ • sourceDirection (θ l)) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    let E := fun l r => fullCircleStationaryExpansion (r*‖x l-y l‖)
      (fun t => β l (x l) (sourceUnitDirection (t+θ l))*
        conj (β l (y l) (sourceUnitDirection (t+θ l)))) n
    ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral (β 0) (x 0) (y 0) r *
         angularPairCircleIntegral (β 1) (x 1) (y 1) r)) -
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (E 0 r*angularPairCircleIntegral (β 1) (x 1) (y 1) r))‖ ≤
      ((2:ℝ)^N)^(-T) := by
  let C := sourceArcLength.real univ*(symbolDerivativeConstant K^K)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨n,N₁,h₁⟩ := uniform_actual_far_circle_expansion (T := max T 0+1) hsig K
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (4*W*(2*C+1))
  refine ⟨n,max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm x y hx hy
    v h L₀ hv hLL hL₀ hd θ hθ
  dsimp only
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let E := fun l r => fullCircleStationaryExpansion (r*‖x l-y l‖)
    (fun t => β l (x l) (sourceUnitDirection (t+θ l))*conj (β l (y l) (sourceUnitDirection (t+θ l)))) n
  let ε := ((2:ℝ)^N)^(-(max T 0+1))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have heone : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith [le_max_right T 0])
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hb (l : Fin 2) (r : ℝ) : ‖angularPairCircleIntegral (β l) (x l) (y l) r‖ ≤ C :=
    angularPairCircleIntegral_norm_le (β l) (x l) (y l)
      (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
      (inheritedCircleSymbol_norm_le _ _ _ _ (hQ l) _ _ _ _ _ _ _ _ K (hK l) _ (hx l))
      (inheritedCircleSymbol_norm_le _ _ _ _ (hQ l) _ _ _ _ _ _ _ _ K (hK l) _ (hy l)) r
  have he (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :
      ‖angularPairCircleIntegral (β 0) (x 0) (y 0) r-E 0 r‖ ≤ ε := by
    have hrid : (2:ℝ)^v*(r/(2:ℝ)^v) = r := by field_simp
    have hexp := h₁ N ((le_max_left _ _).trans hN) (S 0) (b 0) (k 0) (hcard 0) (hK 0)
      L hLN (hL 0) (Q 0) (hQ 0) (ρ 0) (m 0) (lam 0) (J 0) (i 0) (hsp 0) (x 0) (y 0)
      (hx 0) (hy 0) v h L₀ (r/(2:ℝ)^v) (θ 0) hv hLL hL₀ hd (hs _ hr).1.le (hθ 0)
    dsimp only at hexp
    rw [hrid] at hexp
    have hf := far_bump_frequency hv hd (hs _ hr).1.le
    rw [hrid] at hf
    have hΛ : 1 ≤ r*‖x 0-y 0‖ :=
      (Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
        (by linarith [mul_nonneg hsig.le (Nat.cast_nonneg N)] : 0 ≤ 2*L₀)).trans hf
    exact hexp.trans ((mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hΛ (by norm_num : (-1/2:ℝ) ≤ 0)) hε).trans_eq (one_mul ε))
  have herr := angular_radial_product_replacement v hΨ hpos hs hW hw
    (angularPairCircleIntegral (β 0) (x 0) (y 0)) (angularPairCircleIntegral (β 1) (x 1) (y 1))
    (E 0) (angularPairCircleIntegral (β 1) (x 1) (y 1))
    (angularPairCircleIntegral_measurable _ (hβ 0) _ _)
    (angularPairCircleIntegral_measurable _ (hβ 1) _ _)
    ((fullCircleStationaryExpansion_measurable _ n).comp (by fun_prop))
    (angularPairCircleIntegral_measurable _ (hβ 1) _ _)
    hC hε (hb 0) (hb 1) he (fun r _ => by simpa using hε)
  apply herr.trans
  have hc : 4*W*(2*C+1) ≤ (2:ℝ)^N := by
    simpa using h₂ N ((le_max_right _ _).trans hN)
  calc
    _ ≤ (4*W*(2*C+1))*ε := by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hW) hε]
    _ ≤ (2:ℝ)^N*ε := mul_le_mul_of_nonneg_right hc hε
    _ = ((2:ℝ)^N)^(-max T 0) := by
      dsimp [ε]
      nth_rw 1 [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (le_max_left T 0))

end PlanarFalconer

end OAI
