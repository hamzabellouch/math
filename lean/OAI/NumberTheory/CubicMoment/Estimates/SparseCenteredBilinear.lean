import OAI.NumberTheory.CubicMoment.Estimates.SparseProductEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppedModel
import OAI.NumberTheory.CubicMoment.Estimates.SparseLateGeometry
import OAI.NumberTheory.CubicMoment.Estimates.BilinearKernelIdentity

namespace OAI

/-! The centered sparse late-stop contribution.
Both its Gauss part and its squarefree model are proved small; the
norm range supplies the cubic-sieve geometry. -/
noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_sparse_centered_bilinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hD : 1 ≤ D)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ : ℝ), 0 < A → Real.exp 1 ≤ 2*A →
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → 2*A ≤ D*X/B →
      1 < ρ → ρ ≤ 2 →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop)
        (vα vβ : Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      (∀ a ∈ P, ‖vα a‖ ≤ 1) → (∀ b ∈ Q, ‖vβ b‖ ≤ 1) →
      ‖∑ a ∈ P, ∑ b ∈ Q,
        (stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining a*vα a)*
        (stoppedBeta R F
          (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
          primeDetectorCutoff (X^ξ)
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false) b*vβ b)*
        centeredGauss (a*b)*V (norm (a*b)/X)‖ ≤ K*X^(5/6-τ) := by
  obtain ⟨τg,Kg,hτg,hKg,hGauss⟩ := ordinary_late_stopped_product_envelope (ι := ι)
    hpnt hC hξ hξz (by norm_num : (1:ℝ) ≤ 2) hD V hV hpos hsm
  obtain ⟨H,hH,hVbound⟩ := (uniformLogWeights_constant (ι := Unit) V hV hpos hsm).norm_bound
  obtain ⟨τm,Km,hτm,hKm,hModel⟩ := ordinary_late_stopped_model (ι := ι)
    hpnt hC hξ hξz hD hH
  have hcs := cStar_pos
  refine ⟨min τg τm,Kg+cStar*Km,lt_min hτg hτm,by positivity,?_⟩
  filter_upwards [hGauss,hModel,eventually_late_stop_rectangle_bounds hD,
    eventually_ge_atTop (1:ℝ)] with X hGauss hModel hrect hX
  intro A B ρ hA h2A hBlo hBhi hAB hρ hρ₂ j k h hboundary
    S W R F E U P Q remaining vα vβ hS hW hR hF hE hP hQ hvα hvβ
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 35/100)).trans hBlo
  obtain ⟨hAX,hBX,hAs,hBs,hABs⟩ := hrect (2*A) B hBlo hBhi hAB
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R F
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  let Gs := ∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*gauss (a*b)*V (norm (a*b)/X)
  let Ws := fun a b => vα a*vβ b*V (norm (a*b)/X)
  let Ms := ∑ a ∈ P, ∑ b ∈ Q, α a*β b*(idealMoebius (a*b):ℂ)^2*
    ((norm (a*b)^(-1/6:ℝ):ℝ):ℂ)*Ws a b
  have hg : ‖Gs‖ ≤ Kg*X^(5/6-τg) := hGauss A B ρ hA h2A hB1 hAX hBX
    hAs hBs hABs hρ hρ₂ j k h hboundary S W R F E U P Q remaining vα vβ
    hS hW hR hF hE hP (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.1,(hQ b hb).2.2.2⟩) hvα hvβ
  have hWs : ∀ a ∈ P, ∀ b ∈ Q, ‖Ws a b‖ ≤ H := by
    intro a ha b hb
    dsimp [Ws]
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*1*H := mul_le_mul (mul_le_mul (hvα a ha) (hvβ b hb)
        (_root_.norm_nonneg _) (by norm_num)) (hVbound () _) (_root_.norm_nonneg _) (by norm_num)
      _ = H := by ring
  have hm : ‖Ms‖ ≤ Km*X^(5/6-τm) := hModel (2*A) B ρ h2A hB1 hAX hBX
    hAs hBs hABs hρ hρ₂ j k h hboundary S W R F E U P Q remaining Ws
    hS hW hR hF hE
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,by linarith [(hP a ha).2.2.1],(hP a ha).2.2.2⟩)
    hQ hWs
  have he : (∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*centeredGauss (a*b)*
      V (norm (a*b)/X)) = Gs-(cStar:ℂ)*Ms := by
    dsimp only [Gs,Ms]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [centeredGauss,Ws]
    ring
  change ‖∑ a ∈ P, ∑ b ∈ Q, (α a*vα a)*(β b*vβ b)*centeredGauss (a*b)*
    V (norm (a*b)/X)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖Gs‖+‖(cStar:ℂ)*Ms‖ := norm_sub_le _ _
    _ ≤ Kg*X^(5/6-τg)+cStar*(Km*X^(5/6-τm)) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos]
      exact add_le_add hg (mul_le_mul_of_nonneg_left hm cStar_pos.le)
    _ ≤ Kg*X^(5/6-min τg τm)+cStar*(Km*X^(5/6-min τg τm)) := by
      gcongr
      · exact min_le_left τg τm
      · exact min_le_right τg τm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
