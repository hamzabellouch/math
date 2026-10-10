import OAI.NumberTheory.CubicMoment.Estimates.SparseGeometricStop
import OAI.NumberTheory.CubicMoment.Estimates.SparseBilinearPowers
import OAI.NumberTheory.CubicMoment.Estimates.SmallBStoppedAlphaEnergy
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticWeightedBilinear

namespace OAI

/-! Actual sparse late-stop Gauss sums have a power saving. The two
coefficient energies come from their literal stopping constructions;
the smooth factor is handled by the proved weighted cubic sieve. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma energy_bounded_twist (S : Finset Eisenstein)
    (α v : Eisenstein → ℂ) (hv : ∀ a ∈ S, ‖v a‖ ≤ 1) :
    (∑ a ∈ S, ‖α a*v a‖^2) ≤ ∑ a ∈ S, ‖α a‖^2 := by
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (hv a ha)) 2

/-- Fixed support dilations and arbitrary bounded independent twists are
allowed. The small-prime boundary and the stopping thresholds are the
actual geometric ones, not assumed sparsity of an abstract coefficient. -/
theorem ordinary_late_stopped_bilinear
    {ι γ : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M)
    {G : γ → ℝ → ℂ} (hG : UniformLogWeights G) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ V : ℝ), Real.exp 1 ≤ A → 1 ≤ B → A ≤ X → B ≤ X →
      A ≤ M*X^(2/3:ℝ) → B ≤ M*X^(2/3:ℝ) → A*B ≤ M*X →
      1 < ρ → ρ ≤ 2 → 0 < V →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ) (w : Eisenstein → γ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R D
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        gauss (a*b)*G (w a) (norm b/V)‖ ≤ K*X^(5/6-τ) := by
  obtain ⟨δ,Kβ,hδ,hKβ,hβ⟩ := ordinary_late_stopped_energy (ι := ι) hpnt hC hξ hξz
  obtain ⟨Kα,d,hKα,hα⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨Ks,hKs,hsieve⟩ := hG.metaplectic_weighted_bilinear
    (show 0 < δ/4 by positivity)
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound d (show 0 < δ/4 by positivity)
  let K₀ := Ks*(3*Kα*Kβ*(H+1)*M^(2+δ/4))
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨δ/4,Real.sqrt K₀,by positivity,Real.sqrt_pos.mpr hK₀,?_⟩
  filter_upwards [hβ,eventually_ge_atTop (1:ℝ)] with X hβ hX
  intro A B ρ V hA hB hAX hBX hAs hBs hAB hρ hρ₂ hV j k h hboundary
    S W R D E U P Q remaining vα vβ w hS hW hR hD hE hP hQ hvα hvβ
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hA1 : 1 ≤ A := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hA
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  have hea : (∑ a ∈ P, ‖α a*vα a‖^2) ≤ Kα*A*(1+Real.log X)^d := by
    apply (energy_bounded_twist P α vα hvα).trans
    apply (hα E U P primeDetectorCutoff (X^ξ) A remaining hE
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hA hP).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKα.le (by linarith))
    have hl : 1+Real.log A ≤ 1+Real.log X := by
      linarith [Real.log_le_log (show 0 < A from zero_lt_one.trans_le hA1) hAX]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hA1]) hl d
  have heb : (∑ b ∈ Q, ‖β b*vβ b‖^2) ≤ Kβ*B*X^(-δ) :=
    (energy_bounded_twist Q β vβ hvβ).trans
      (hβ B ρ (by linarith) hBX hρ hρ₂ j k h hboundary S W R D Q hS hW hR hD hQ)
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hsq : ‖∑ a ∈ P, ∑ b ∈ Q,
      (α a*vα a)*(β b*vβ b)*gauss (a*b)*G (w a) (norm b/V)‖^2 ≤
      K₀*X^(5/3-δ/2) := by
    apply (hsieve w P Q A B V hA1 hB hV hP hQ
      (fun a => α a*vα a) (fun b => β b*vβ b)).trans
    calc
      _ ≤ Ks*(A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) := by gcongr
      _ = Ks*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ))) := by ring
      _ ≤ Ks*((3*Kα*Kβ*(H+1)*M^(2+δ/4))*X^(5/3-δ/2)) :=
        mul_le_mul_of_nonneg_left (sparse_bilinear_power_bound hX (by linarith)
          (by linarith) hM hδ (by positivity) hKα.le hKβ.le d hAs hBs hAB
          ((hlog X hX).trans (by linarith))) hKs.le
      _ = _ := by dsimp [K₀]; ring
  have he : (Real.sqrt K₀*X^(5/6-δ/4))^2 = K₀*X^(5/3-δ/2) := by
    rw [mul_pow,Real.sq_sqrt hK₀.le,←Real.rpow_mul_natCast hXp.le]
    congr 2
    ring
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp (hsq.trans_eq he.symm)

end CubicFirstMoment

end

end OAI
