import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBilinearMellin
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeckeContour
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! The cubic-sieve bound for the actual varying-weight bilinear Gauss
sum. The common Mellin majorant is derived from the given weight family. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma UniformLogWeights.zeroLine_majorant
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : γ) (V : ℝ), 0 < V → ∀ t : ℝ,
      ‖zeroLineMellinWeight (W r) V t‖ ≤
        (1/(2*Real.pi))*mellinEdgeMajorant D t := by
  obtain ⟨D,hD,hdecay⟩ := hW.mellin_decay 0 2
  refine ⟨D,hD,?_⟩
  intro r V hV t
  rw [zeroLineMellinWeight_norm (W r) hV]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^2)).mpr
  exact (mul_comm _ _).trans_le (by simpa using hdecay r 0 (by norm_num) t)

theorem UniformLogWeights.metaplectic_weighted_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A B : Finset Eisenstein) (N Z V : ℝ),
      1 ≤ N → 1 ≤ Z → 0 < V →
      (∀ r ∈ A, primary r ∧ Squarefree r ∧ norm r ≤ N) →
      (∀ u ∈ B, primary u ∧ Squarefree u ∧ norm u ≤ Z) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W (w r) (norm u/V)‖^2 ≤
        K*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨C,hC,hbilinear⟩ := metaplectic_bilinear_sieve hε
  obtain ⟨D,hD,hmajorant⟩ := hW.zeroLine_majorant
  let m : ℝ → ℝ := fun t => (1/(2*Real.pi))*mellinEdgeMajorant D t
  have hm : Integrable m := (mellinEdgeMajorant_integrable D).const_mul _
  have hm0 (t : ℝ) : 0 ≤ m t := by dsimp [m,mellinEdgeMajorant]; positivity
  let H : ℝ := ∫ t : ℝ, m t
  have hH : 0 ≤ H := integral_nonneg hm0
  refine ⟨(1+H)^2*C,by positivity,?_⟩
  intro w A B N Z V hN hZ hV hA hB α β
  let Q : ℝ := C*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
    (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let F : ℝ → ℂ := fun t => ∑ r ∈ A, ∑ u ∈ B,
    (α r*zeroLineMellinWeight (W (w r)) V t)*
      (β u*mellinPhase (-t) (norm u))*gauss (r*u)
  have hb (t : ℝ) : ‖F t‖^2 ≤ (m t)^2*Q := by
    have hα : (∑ r ∈ A, ‖α r*zeroLineMellinWeight (W (w r)) V t‖^2) ≤
        (m t)^2*(∑ r ∈ A, ‖α r‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (hmajorant (w r) V hV t) 2)
        (sq_nonneg _)).trans_eq (mul_comm _ _)
    have hβ : (∑ u ∈ B, ‖β u*mellinPhase (-t) (norm u)‖^2) =
        ∑ u ∈ B, ‖β u‖^2 := by
      apply Finset.sum_congr rfl
      intro u _
      simp [mellinPhase,Complex.norm_exp]
    have h := hbilinear A B N Z hN hZ hA hB
      (fun r => α r*zeroLineMellinWeight (W (w r)) V t)
      (fun u => β u*mellinPhase (-t) (norm u))
    rw [hβ] at h
    apply h.trans
    calc
      _ ≤ C*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          ((m t)^2*(∑ r ∈ A, ‖α r‖^2))*(∑ u ∈ B, ‖β u‖^2) := by gcongr
      _ = _ := by dsimp [Q]; ring
  have hn (t : ℝ) : ‖F t‖ ≤ m t*Real.sqrt Q := by
    have h := Real.le_sqrt_of_sq_le (hb t)
    rwa [Real.sqrt_mul (sq_nonneg (m t)),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hm0 t)] at h
  have hnorm : ‖∫ t : ℝ, F t‖ ≤ H*Real.sqrt Q := by
    have hi := norm_integral_le_of_norm_le (hm.mul_const (Real.sqrt Q))
      (Filter.Eventually.of_forall hn)
    simpa only [integral_mul_const] using hi
  rw [metaplectic_bilinear_mellin A B α β (fun r => W (w r))
    (fun r _ => hW.compact (w r)) (fun r _ => hW.positive (w r))
    (fun r _ => hW.smooth (w r)) (fun u hu => (hB u hu).1) hV]
  change ‖∫ t : ℝ, F t‖^2 ≤ _
  calc
    _ ≤ (H*Real.sqrt Q)^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) hnorm 2
    _ = H^2*Q := by rw [mul_pow,Real.sq_sqrt hQ]
    _ ≤ (1+H)^2*Q := mul_le_mul_of_nonneg_right (by nlinarith) hQ
    _ = _ := by dsimp [Q]; ring

end CubicFirstMoment

end

end OAI
