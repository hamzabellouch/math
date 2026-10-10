import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopParameters
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralRestrictedNoStopCentral

namespace OAI

/-! Uniform power saving for the literal no-stop term with the
first-stage predicate retained, including a growing finite norm partition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem restricted_noStop_patterson_bound_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {M : ℝ} (hM : 0 ≤ M) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ K : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (i : γ) (R : Finset Eisenstein) (v : Eisenstein → ℂ)
        (P : Eisenstein → Eisenstein → Prop) (ψ : ℝ → ℝ) (w H X₀ : ℝ),
      0 < H → (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ M) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      ‖restrictedNoStopCenteredValue R v ψ w ρ (X^(38/100:ℝ))
        (Real.exp hW.radius) ℓ (W i) H ((1+Real.log X)^Ct) X X₀ P‖ ≤
        K*(1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ) := by
  obtain ⟨ρ,K,hρ,hρ₂,hsmall,hK,hbound⟩ := restricted_noStop_central_bound_actual  hW ℓ hGamma
    (by norm_num : (0:ℝ) < 1/100) hM Ct hcap
  refine ⟨ρ,K,hρ,hρ₂,hsmall,hK,?_⟩
  filter_upwards [hbound,eventually_noStop_scales hW] with X hb hx
  intro i R v P ψ w H X₀ hH hR hv hψ
  have he := hb i R v ψ w (X^(38/100:ℝ)) (X^(2/5:ℝ)) H X₀ P
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2 hH hR hv hψ
  have hXp : 0 < X := by linarith [hx.1]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hx.1])
  have hlogs : 1+Real.log (X^(2/5:ℝ)) ≤ 1+Real.log X := by
    rw [Real.log_rpow hXp]
    linarith
  apply he.trans
  calc
    _ ≤ K*(1+Real.log X)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem distinguishedScaleNoStop_finite_isLittleO_actual (m : ℕ)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (ξ : ℝ) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ ∀ i < m, ∀ (H : ℝ → ℝ)
      (P : ℝ → Eisenstein → Eisenstein → Prop),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => distinguishedScaleNoStop i ρ ξ Ct (H X) X (P X))
        =o[atTop] firstMomentScale := by
  let M : ℝ := ∑ j ∈ Finset.range m, ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ)
  obtain ⟨ρ,K,hρ,hρ₂,hsmall,hK,hbound⟩ := restricted_noStop_patterson_bound_actual  primeProductWeights 0
    hGamma (show 0 ≤ M by dsimp [M]; positivity) Ct hcap
  refine ⟨ρ,hρ,hρ₂,hsmall,?_⟩
  intro i hi H P hH
  have hMi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => (1+Real.log X)^(Ct+1+i)*X^(5/6-1/100:ℝ)) ?_
    (log_power_powerSaving_isLittleO (Ct+1+i) (by norm_num))
  apply Asymptotics.IsBigO.of_bound (D*K)
  filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  let B := K*(1+Real.log X)^(Ct+1)*X^(5/6-1/100:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpiece (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
      ‖if distinguishedScaleLength k < X^(69/200:ℝ) then
        restrictedNoStopCenteredValue (centralPrimaryFactors X)
          (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
          (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) 0 primeProductEnvelope
          (H X) ((1+Real.log X)^Ct) X X (P X) else 0‖ ≤ B := by
    split_ifs
    · exact hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X k)
        (P X) primeDetectorCutoff (X^ξ) (H X) X hH
        (fun _ hr => (mem_primaryElementBall.mp hr).1)
        (fun r _ => (distinguishedScaleCoefficient_norm i ξ X k r).trans hMi)
        (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    · simpa only [norm_zero] using hB
  have hn : (Fintype.card (Fin i → Fin
      (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) ≤ D*(1+Real.log X)^i := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero]
      using hcount X hX
  rw [Real.norm_of_nonneg (by positivity)]
  unfold distinguishedScaleNoStop
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun k _ => hpiece k)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hn hB).trans_eq
  dsimp [B]
  rw [pow_add]
  ring

end CubicFirstMoment

end

end OAI
