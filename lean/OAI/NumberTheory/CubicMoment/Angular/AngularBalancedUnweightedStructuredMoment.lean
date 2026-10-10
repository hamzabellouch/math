import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedScaledStructuredMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularStructuredSupportBounds

namespace OAI

/-! The actual balanced structured moment without an auxiliary output cutoff. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ℓ : ℤ)

theorem angular_balanced_unweighted_structured_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity) {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (hR : 1 ≤ R) (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) → ∃ T : ℝ,
      ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P : Finset (Eisenstein × Eisenstein)),
      T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (L r)^(1/3+δ) ∧
        norm a.2 ≤ (L r)^(1/3+δ) ∧ (L r)^(1/3-δ) ≤ norm a.1) →
      (∑ a ∈ P, ‖structuredAngularPrimeSum ℓ a.1 a.2 v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤ (L r)^(7/3-ε) := by
  let σ : Fin J → ℝ := fun k => (4/3:ℝ)^k.val/2
  have hσ : ∀ k, 0 < σ k := fun k => div_pos (pow_pos (by norm_num) _) (by norm_num)
  obtain ⟨δ,hδ,hδhi,ε,hε,hraw⟩ := angular_balanced_scaled_structured_moment ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ σ hσ normPartitionWeight
    normPartitionWeight_compact normPartitionWeight_positive_support normPartitionWeight_smooth
    (fun _ => normPartitionWeight_low) (fun _ => normPartitionWeight_high)
    normPartitionWeight_norm hGI hGQ
  refine ⟨δ,hδ,hδhi,ε/2,by positivity,?_⟩
  intro L W hL hW hWlo hWhi
  obtain ⟨T₀,hbound⟩ := hraw L W hL hW hWlo
  obtain ⟨T₁,habs⟩ := eventually_atTop.mp (eventually_const_mul_rpow_le
    (by linarith : 7/3-ε < 7/3-ε/2) ((J:ℝ)^2))
  refine ⟨max T₀ T₁,?_⟩
  intro r X v e u P hT hprod hXlo hXhi hv he hvY heY hu hP
  have hYp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hX : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos (show 0 < 2*L r by positivity) c).trans (hXlo i)
  let Z := ((4/3:ℝ)^J/2)*L r
  have hpart (a b : Eisenstein) : structuredAngularPrimeSum ℓ a b v e u (W r) X Z =
      ∑ k : Fin J, structuredAngularPrimeMoment ℓ a b v e u (W r) X normPartitionWeight (σ k*L r) := by
    have hrange := fun z hz => coordinatePrimeProduct_norm_bounds (W r) X hX
      (show 0 ≤ R by linarith) (hWlo r) (hWhi r) Z z hz
    have hp := structuredAngularPrimeSum_partition_dyads ℓ a b v e u (W r) X Z hYp J hJ
      (fun z hz => by simpa only [hprod] using hrange z hz) (by
        intro k hk
        dsimp [Z]
        have hpow : (4/3:ℝ)^k ≤ (4/3:ℝ)^J :=
          pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hk).le
        nlinarith [mul_le_mul_of_nonneg_right hpow hYp.le])
    dsimp only [σ]
    rw [Fin.sum_univ_eq_sum_range (fun k => structuredAngularPrimeMoment ℓ a b v e u
      (W r) X normPartitionWeight ((4/3:ℝ)^k/2*L r))]
    simpa only [mul_comm] using hp
  have hb := hbound r X v e u P ((le_max_left _ _).trans hT)
    hXlo hXhi hv he hvY heY hu hP
  calc
    _ = ∑ z ∈ P, ‖∑ k : Fin J,
        structuredAngularPrimeMoment ℓ z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r)‖^2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hpart]
    _ ≤ (J:ℝ)*(∑ k : Fin J, ∑ z ∈ P,
        ‖structuredAngularPrimeMoment ℓ z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r)‖^2) := by
      simpa only [Fintype.card_fin] using finite_piece_moment_on P
        (fun k z => structuredAngularPrimeMoment ℓ z.1 z.2 v e u (W r) X normPartitionWeight (σ k*L r))
    _ ≤ (J:ℝ)*(∑ _k : Fin J, (L r)^(7/3-ε)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun k _ => hb k)
    _ = (J:ℝ)^2*(L r)^(7/3-ε) := by simp; ring
    _ ≤ _ := habs (L r) ((le_max_right _ _).trans hT)

end CubicFirstMoment

end

end OAI
