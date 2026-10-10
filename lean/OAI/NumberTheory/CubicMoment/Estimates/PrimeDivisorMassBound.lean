import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoprimeMass
import OAI.NumberTheory.CubicMoment.Estimates.GramSliceRows
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSliceSieve

namespace OAI

/-! Actual common-divisor terms of the Poisson mass are controlled by
the three sieve bounds for their shortened coefficient rows. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeDivisorMellinMass_le {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N₀ : ℝ} (hN₀ : 0 < N₀) :
    fullPrimeDivisorMellinMass R W X e H u N₀ f t ≤
      ((∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 0 (u+2*Real.pi*t)‖^2)+
       (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 0 (u-2*Real.pi*t)‖^2))/2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  apply add_le_add
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (fullPrimeSliceRow_norm_le W X hX hlo hhi hf e h u t hN₀) 2)
  · exact Finset.sum_le_sum (fun h _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
      (fullPrimeSliceRow_reverse_norm_le W X hX hlo hhi hf e h u t hN₀) 2)

theorem fullPrime_divisor_mass_three_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (f e : Eisenstein)
      (u t : ℝ) (Ram S T J H : Finset Eisenstein) (N N₀ U V : ℝ),
      (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → primary f → 0 < N₀ →
      (∏ i, X i)/norm f = N → 1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      fullPrimeDivisorMellinMass R W X e H u N₀ f t ≤
        min ((Ram.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((Ram.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hbound⟩ := fullPrime_slice_three_sieve (ι := ι) hHuxley hR hε
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro W X f e u t Ram S T J H N N₀ U V hX hlo hhi hf hN₀ hN hN1 hU hV hS hT hH
  have hp := hbound W X f e 1 0 (u+2*Real.pi*t) Ram S T J H N U V hN hN1 hU hV hS hT hH
  have hn := hbound W X f e 1 0 (u-2*Real.pi*t) Ram S T J H N U V hN hN1 hU hV hS hT hH
  apply (fullPrimeDivisorMellinMass_le W X hX hlo hhi hf e H u t hN₀).trans
  linarith

end CubicFirstMoment

end

end OAI
