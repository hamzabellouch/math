import OAI.NumberTheory.CubicMoment.Estimates.LogCoefficientEnergy
import OAI.NumberTheory.CubicMoment.Estimates.DilatedNoncubeSieve
import OAI.NumberTheory.CubicMoment.Estimates.StructuredFrequencyPolynomial

namespace OAI

/-! The ordinary sieve on the actual full convolution, retaining precise
logarithmic weight costs. It applies also below every fixed conductor power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_ordinary_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε)
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (C : ℝ) (a : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (U V : ℝ)
      (v e : Eisenstein) (u : ℝ) (Ram S T J H : Finset Eisenstein),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → 1 ≤ U → 1 ≤ V →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(U*V)^ε*((U*V)^2+L r)*L r*(1+Real.log (L r))^a := by
  obtain ⟨C₀,a,hC₀,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  obtain ⟨C₁,C₂,_,hC₂,hsieve⟩ := dilated_noncube_three_sieve_bounds hHuxley
    (one_le_pow₀ hR : 1 ≤ R^(Fintype.card ι)) hε
  refine ⟨C₂*(C₀+1),a,mul_pos hC₂ (by linarith),?_⟩
  intro r X U V v e u Ram S T J H hL hX hprod hU hV hS hT hH
  let Z := R/2*L r
  let B := structuredFrequencySupport (W r) X Z
  let β := structuredFrequencyCoefficient v e u (W r) X Z
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hB : ∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ R^(Fintype.card ι)*L r := by
    intro b hb
    simpa only [hprod] using structuredFrequencySupport_bounds (W r) X hXp
      (zero_le_one.trans hR) (hlo r) (hhi r) Z b hb
  have heq : fullPrimeSupport R (W r) X = coordinatePrimeSupport (W r) X Z := by
    simpa only [Z,hprod] using fullPrimeSupport_eq_product_cutoff (zero_le_one.trans hR)
      (W r) X hX (hhi r)
  have hE : (∑ b ∈ B, ‖β b‖^2) ≤ (C₀+1)*L r*(1+Real.log (L r))^a := by
    apply (structuredFrequencyCoefficient_energy_le v e u (W r) X Z).trans
    have hb := henergy r X hL hX hprod
    change (∑ b ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
      ‖primeMomentCoefficient (W r) X Z b‖^2) ≤ _
    have hb' : (∑ b ∈ orderedConvolutionSupport (coordinatePrimeSupport (W r) X Z),
        ‖primeMomentCoefficient (W r) X Z b‖^2) ≤ C₀*L r*(1+Real.log (L r))^a := by
      simpa only [fullPrimeCoefficient,primeMomentCoefficient,heq] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀+1) hLp.le) (pow_nonneg hz _))
  have hm := hsieve B Ram S T J H (L r) U V hL hU hV hB hS hT hH β
  have hbound := hm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hfull (h : Eisenstein) : fullStructuredPrimeSum R h 1 v e u (W r) X =
      structuredPrimeSum h 1 v e u (W r) X Z := by
    apply fullStructuredPrimeSum_eq h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (zero_le_one.trans hR)]
  have hsum : (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [hfull,structuredPrimeSum_eq_frequency]
  rw [hsum]
  apply hbound.trans
  calc
    _ ≤ ((Ram.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+L r))*
        ((C₀+1)*L r*(1+Real.log (L r))^a) :=
      mul_le_mul_of_nonneg_left hE
        (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC₂.le)
          (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hV)) _))
          (add_nonneg (sq_nonneg _) hLp.le))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
