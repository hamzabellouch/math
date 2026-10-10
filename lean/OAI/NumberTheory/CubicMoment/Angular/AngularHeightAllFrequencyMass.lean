import OAI.NumberTheory.CubicMoment.Angular.AngularHeightNoncubeMass
import OAI.NumberTheory.CubicMoment.Estimates.HeightCubeMass

namespace OAI

/-! Every nonzero frequency in the height average, including cubes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_all_frequency_cutoff_mass
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      1+2*T+|u| ≤ (L r)^(9/25:ℝ) →
      dyadicHeightMean (fullStructuredHeightMass R H 1 e ℓ u (W r) X) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hnoncube⟩ := angular_height_noncube_cutoff_mass ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ k
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Kn,Ln,mn,hKn,hnoncube⟩ := hnoncube L W hL hW hlo hhi
  obtain ⟨Kc,Lc,mc,hKc,hcube⟩ := cube_height_log_saving hMV hC hR hW hlo hhi k
  refine ⟨Kc+Kn,max Lc Ln,max mc mn,by positivity,?_⟩
  intro r X B H e u T hL₀ hprod hX hB hBL hH he heN hT hu
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTc : (1+Real.log (L r))^mc ≤ T :=
    (pow_le_pow_right₀ hz (le_max_left mc mn)).trans hT
  have hTn : (1+Real.log (L r))^mn ≤ T :=
    (pow_le_pow_right₀ hz (le_max_right mc mn)).trans hT
  have hXone : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : 1 ≤ 2*L r) hc.le).trans (hX i).le
  let HC := H.filter (fun h => ∃ z : Eisenstein, z^3 = h)
  let HN := H.filter (fun h => ¬∃ z : Eisenstein, z^3 = h)
  have hHC : HC ⊆ nonzeroCubeNormBall B := by
    intro h hh
    obtain ⟨hhH,hhc⟩ := Finset.mem_filter.mp hh
    exact mem_nonzeroCubeNormBall (hH h hhH).1 (hH h hhH).2 hhc
  have hHN : ∀ h ∈ HN, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h := by
    intro h hh
    obtain ⟨hhH,hhn⟩ := Finset.mem_filter.mp hh
    exact ⟨(hH h hhH).1,(hH h hhH).2,hhn⟩
  have hmc := hcube r X B HC (hL r) ((le_max_left _ _).trans hL₀) hXone hprod
    (zero_le_one.trans hB) hHC 1 e ℓ u T hTc
  have hmn := hnoncube r X B HN e u T ((le_max_right _ _).trans hL₀)
    hprod hX hB hBL hHN he heN hTn hu
  have heq : fullStructuredHeightMass R H 1 e ℓ u (W r) X =
      fun t => fullStructuredHeightMass R HC 1 e ℓ u (W r) X t+
        fullStructuredHeightMass R HN 1 e ℓ u (W r) X t := by
    funext t
    exact (Finset.sum_filter_add_sum_filter_not H
      (fun h => ∃ z : Eisenstein, z^3 = h) _).symm
  rw [heq,dyadicHeightMean_add
    (continuous_fullStructuredHeightMass R HC 1 e ℓ u (W r) X)
    (continuous_fullStructuredHeightMass R HN 1 e ℓ u (W r) X)]
  exact (add_le_add hmc hmn).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
