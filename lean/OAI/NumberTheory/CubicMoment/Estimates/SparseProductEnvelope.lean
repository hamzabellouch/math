import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppedBilinear
import OAI.NumberTheory.CubicMoment.Estimates.SparseEnvelopeWeights

namespace OAI

/-! The sparse Gauss contribution with the manuscript's literal smooth
product envelope. The envelope is not replaced by independent factors. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_late_stopped_product_envelope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ M D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hM : 1 ≤ M) (hD : 1 ≤ D)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), 0 < A → Real.exp 1 ≤ M*A → 1 ≤ B →
      M*A ≤ X → B ≤ X → M*A ≤ D*X^(2/3:ℝ) → B ≤ D*X^(2/3:ℝ) →
      (M*A)*B ≤ D*X → 1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ M*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R F
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        gauss (a*b)*V (norm (a*b)/X)‖ ≤ K*X^(5/6-τ) := by
  let hW := uniformLogWeights_constant (ι := Unit) V hV hpos hsm
  let hG := hW.logDilate (Real.log M) (Real.log_nonneg hM)
  obtain ⟨τ,K,hτ,hK,hbound⟩ := ordinary_late_stopped_bilinear (ι := ι)
    hpnt hC hξ hξz hD hG
  refine ⟨τ,K,hτ,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro A B ρ hA hMA hB hAX hBX hAs hBs hAB hρ hρ₂ j k h hboundary
    S W R F E U P Q remaining vα vβ hS hWeights hR hF hE hP hQ hvα hvβ
  let w : Eisenstein → Unit × {s : ℝ // 0 < s ∧ |Real.log s| ≤ Real.log M} := fun a =>
    ((),if ha : a ∈ P then
      ⟨norm a/A,log_dyad_ratio hA hM (hP a ha).2.2.1 (hP a ha).2.2.2⟩
      else ⟨1,by simp [Real.log_nonneg hM]⟩)
  have he (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) :
      V ((w a).2*(norm b/(X/A))) = V (norm (a*b)/X) := by
    dsimp only [w]
    simp only [ha,dite_eq_left,Subtype.coe_mk]
    congr 1
    rw [norm_mul_eq]
    field_simp
  have hb := hbound (M*A) B ρ (X/A) hMA hB hAX hBX hAs hBs hAB hρ hρ₂
    (div_pos hX hA) j k h hboundary S W R F E U P Q remaining vα vβ w
    hS hWeights hR hF hE
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.2⟩) hQ hvα hvβ
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [he a ha b]

end CubicFirstMoment

end

end OAI
