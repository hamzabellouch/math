import OAI.NumberTheory.CubicMoment.Decomposition.StoppedFullModel
import OAI.NumberTheory.CubicMoment.Estimates.SieveTruncationScale

namespace OAI

/-! The literal stopped variance model summed over the actual finite
square-divisor sieve, with its cardinality loss absorbed logarithmically. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_sieved_model_log_saving
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ) (k H q : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*(k+2*q)) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      let T := squarefreeDivisorTruncation ((Real.log X)^q)
      ‖sievedDispersionVariance T S β u Φ A-
        (finiteSieveDensity T:ℂ)*cubeModelTerm S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K,G,hK,hfull⟩ := stopped_divisor_full_model_log_saving (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' (k+2*q) H (2*q)
  refine ⟨324*K,G,by positivity,?_⟩
  filter_upwards [hfull,eventually_ge_atTop (Real.exp 1)] with X hfull hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let L := Real.log X
  let D := L^q
  let T := squarefreeDivisorTruncation D
  have hL1 : 1 ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hDp : 0 < D := pow_pos hLp _
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < b) _).trans_le hAlo
  have herror (c : Eisenstein) (hc : c ∈ T) (d : Eisenstein) (hd : d ∈ T) :
      ‖divisorDispersionVariance (primarySquarefreeJoin c d) S β u Φ A-
        ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*cubeModelTerm S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/L^(k+2*q) := by
    have hc' := squarefreeTruncation_spec D c hc
    have hd' := squarefreeTruncation_spec D d hd
    have hjn : norm (primarySquarefreeJoin c d) ≤ L^(2*q) := by
      have hh := squarefreeTruncation_join_norm hDp.le hc hd
      simpa only [D,←pow_mul,Nat.mul_comm] using hh
    exact hfull δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
      hAlo hAhi (primarySquarefreeJoin c d) (primarySquarefreeJoin_primary hc'.1 hd'.1)
      (primarySquarefreeJoin_squarefree hc'.1 hd'.1) hjn e he hNe j₀ k₀ h Z Q early hj hR
  have hh := sieved_model_error_bound T (squarefreeTruncation_spec D) S
    (fun a ha => (stoppedIntervalSupport_spec X (b/2) b e ha).1)
    β u Φ hΦ hΦ' hAp (cubeModelTerm S β u Φ A) herror
  have hcard : (T.card:ℝ)^2 ≤ (18*D)^2 :=
    pow_le_pow_left₀ (by positivity) (squarefreeDivisorTruncation_card_le hDp.le) 2
  apply hh.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_)
  change (18*L^q)^2*(K*A^(2/3:ℝ)*b^(5/3:ℝ)/L^(k+2*q)) =
    (324*K)*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k
  rw [mul_pow,←pow_mul,show q*2 = 2*q by omega,pow_add]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
