import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppedBilinear
import OAI.NumberTheory.CubicMoment.Estimates.SparseModelCounting

namespace OAI

/-! The actual late-stop squarefree model is power-saving by direct
counting and the two proved coefficient energies. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_late_stopped_model
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M H : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M) (hH : 0 ≤ H) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), Real.exp 1 ≤ A → 1 ≤ B → A ≤ X → B ≤ X →
      A ≤ M*X^(2/3:ℝ) → B ≤ M*X^(2/3:ℝ) → A*B ≤ M*X →
      1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (V : Eisenstein → Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A/2 ≤ norm a ∧ norm a ≤ A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      (∀ a ∈ P, ∀ b ∈ Q, ‖V a b‖ ≤ H) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*
        stoppedBeta R D
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*
        (idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖ ≤
        K*X^(5/6-τ) := by
  obtain ⟨δ,Kβ,hδ,hKβ,hβ⟩ := ordinary_late_stopped_energy (ι := ι) hpnt hC hξ hξz
  obtain ⟨Kα,d,hKα,hα⟩ := smallB_stopped_alpha_energy hpnt
  obtain ⟨J,hJ,hlog⟩ := log_power_normalization_bound d (show 0 < δ/4 by positivity)
  let Ks : ℝ := 1+324*H^2*(2:ℝ)^(2/3:ℝ)
  have hKs : 0 < Ks := by dsimp [Ks]; positivity
  let K₀ := Ks*(3*Kα*Kβ*(J+1)*M^(2+δ/4))
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨δ/4,Real.sqrt K₀,by positivity,Real.sqrt_pos.mpr hK₀,?_⟩
  filter_upwards [hβ,eventually_ge_atTop (1:ℝ)] with X hβ hX
  intro A B ρ hA hB hAX hBX hAs hBs hAB hρ hρ₂ j k h hboundary
    S W R D E U P Q remaining V hS hW hR hD hE hP hQ hV
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hA1 : 1 ≤ A := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hA
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R D
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  have hea : (∑ a ∈ P, ‖α a‖^2) ≤ Kα*A*(1+Real.log X)^d := by
    apply (hα E U P primeDetectorCutoff (X^ξ) A remaining hE
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) hA
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKα.le (by linarith))
    have hl : 1+Real.log A ≤ 1+Real.log X := by
      linarith [Real.log_le_log (show 0 < A from zero_lt_one.trans_le hA1) hAX]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hA1]) hl d
  have heb : (∑ b ∈ Q, ‖β b‖^2) ≤ Kβ*B*X^(-δ) :=
    hβ B ρ (by linarith) hBX hρ hρ₂ j k h hboundary S W R D Q hS hW hR hD
      (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.1,(hQ b hb).2.2.2⟩)
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hsieve := squarefree_model_bilinear_operator P Q α β V hA1 hB
    (by norm_num : (0:ℝ) < 2) hH (show 0 ≤ δ/4 by positivity)
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩)
    (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.2⟩) hV
  have hsq : ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
      ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*V a b‖^2 ≤ K₀*X^(5/3-δ/2) := by
    apply hsieve.trans
    calc
      _ ≤ Ks*(A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) := by
        dsimp only [Ks]
        gcongr
        linarith
      _ = Ks*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
          (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ))) := by ring
      _ ≤ Ks*((3*Kα*Kβ*(J+1)*M^(2+δ/4))*X^(5/3-δ/2)) :=
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
