import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorTotal
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorCube
import OAI.NumberTheory.CubicMoment.Estimates.DivisorPoissonSplit
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeModel

namespace OAI

/-! The actual small square-divisor coprime Gram has its full squared model
with exact inverse-square divisor density. Common-factor restoration is separate. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_coprime_model_log_saving
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*k) →
      ∀ (d : Eisenstein), primary d → Squarefree d → norm d ≤ b^(1/1000:ℝ) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      norm d < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖divisorCoprimeDispersionGram d S β u Φ A-
        (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kn,hKn,hnoncube⟩ := stopped_divisor_noncube_total (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H
  obtain ⟨Kc,hKc,hcube⟩ := stopped_cube_model_log_saving (ι := ι) hξ hξz Φ hΦ hΦ' k
  refine ⟨Kc+Kn,by positivity,?_⟩
  filter_upwards [hnoncube,hcube,eventually_ge_atTop (Real.exp 1)] with X hnoncube hcube hX
  intro δ b u V A hδ hδone hwidth hb hbXlow hbX hV hu hVF W hW hWi hWd hAlo hAhi
    d hd hds hdhi e he hNe j₀ k₀ h Z Q early hj hR hdR hRlog
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  have hbp : 0 < b := by linarith
  have hA : 0 < A := (Real.rpow_pos_of_pos hbp _).trans_le hAlo
  have hz : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hcR : (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) := by
    have hp : (Real.log X)^(k+1) ≤ (Real.log X)^(2*(4*(k+2)+k)) :=
      pow_le_pow_right₀ hz (by omega)
    exact (hp.trans (by nlinarith [pow_nonneg (zero_le_one.trans hz) (2*(4*(k+2)+k))])).trans hRlog
  have hs (a : Eisenstein) (ha : a ∈ S) : primary a ∧ Squarefree a ∧ a ≠ 1 := by
    have hp := stoppedIntervalSupport_spec X (b/2) b e ha
    refine ⟨hp.1,hp.2.1,?_⟩
    intro ha1
    have hn := (Finset.mem_filter.mp ha).2.2.2.1
    rw [ha1,norm_one_eq] at hn
    linarith
  have hn := hnoncube δ b u V A hδ hδone hwidth hb hbXlow hbX hV hu hVF
    W hW hWi hWd hAlo d (primary_ne_zero hd) hdhi e he hNe j₀ k₀ h Z Q early hj hR hRlog
  have hc := hcube δ b A u hδ hδone hb hbX hA hAhi W hW e j₀ k₀ h Z Q early hj hcR
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hcube' : ‖divisorCubePoissonContribution d S β u Φ A-
      (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A‖ ≤
      Kc*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
    rw [stopped_divisor_cube_eq hX1 hξz hδ hδone W j₀ k₀ h Z Q early hj
      e d hd hds hdR u Φ hA.le,←mul_sub,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity)]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) _).trans hc
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (one_le_norm (primary_ne_zero hd)) : 1 ≤ (norm d)^2)
  change ‖divisorCoprimeDispersionGram d S β u Φ A-
    (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A‖ ≤
    (Kc+Kn)*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k
  rw [divisorCoprimeDispersionGram_split (primary_ne_zero hd) S hs β u Φ hΦ hΦ' hA]
  calc
    _ = ‖(divisorCubePoissonContribution d S β u Φ A-
        (1/(norm d)^2:ℝ)*cubeModelTerm S β u Φ A)+
        divisorNoncubePoissonContribution d (primary_ne_zero hd) S β u Φ A‖ := by
      congr 1
      ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hcube' hn).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
