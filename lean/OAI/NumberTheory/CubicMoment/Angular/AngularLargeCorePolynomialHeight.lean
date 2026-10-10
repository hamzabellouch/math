import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Angular.AngularPolynomialHeightCoreBlock
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeCutoffMass

namespace OAI

/-! The finite large-core contribution has every logarithmic saving
throughout the fixed polynomial height window required by Mellin truncation. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_core_cutoff_polynomial_height (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (C T₀ : ℝ) (a : ℕ), 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ (¬∃ z : Eisenstein, z^3 = h) ∧
        h ∉ lowNoncubeSupport ((Real.log (L r))^a) (B^(1/3:ℝ))) →
      e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hblock⟩ := angular_uniform_core_block_polynomial_height ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ (k+2)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨CB,TB,A,hCB,hblock⟩ := hblock L W hL hW hlo hhi
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop TB).and (low_core_log_threshold A))
  refine ⟨CI*CB,T₀,A+1,by positivity,?_⟩
  intro r X B H e u hT₀ hprod hX hB hBL hH he heN hu
  obtain ⟨hTB,hcut⟩ := hT (L r) hT₀
  have hB₂ : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  let V := (Real.log (L r))^(A+1)
  let F (h : Eisenstein) := ‖fullStructuredAngularPrimeSum ℓ R h 1 1 e u (W r) X‖^2
  have hlarge : (∑ z ∈ largeCoreDyadicIndices V B,
      ∑ h ∈ coreDyadicBlock B z.1 z.2, F h) ≤
      CI*CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
    have hrow : ∀ z ∈ largeCoreDyadicIndices V B,
        (∑ h ∈ coreDyadicBlock B z.1 z.2, F h) ≤
        CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) := by
      intro z hz
      have hm := (Finset.mem_filter.mp hz).2
      have hD := coreDyadicConductor_pos z.1 z.2
      have hthreshold : (1+Real.log (L r))^A ≤ 8*coreDyadicConductor z.1 z.2 := by
        dsimp [V] at hm
        nlinarith [hcut]
      exact hblock r X B z.1 z.2 e u _ hTB hprod hX (zero_le_one.trans hB) hBL hm.2
        hthreshold he heN hu (Finset.Subset.refl _)
    have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
    have hbase : 0 ≤ CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) :=
      div_nonneg (mul_nonneg (mul_nonneg hCB.le (sq_nonneg _)) (Real.rpow_nonneg (zero_le_one.trans hB) _))
        (pow_nonneg hz.le _)
    calc
      _ ≤ ∑ _z ∈ largeCoreDyadicIndices V B,
          CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2) := Finset.sum_le_sum hrow
      _ = ((largeCoreDyadicIndices V B).card:ℝ)*
          (CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) := by simp
      _ ≤ (CI*(1+Real.log (L r))^2)*
          (CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) :=
        mul_le_mul_of_nonneg_right (hcount V B (L r) hB (hL r) hB₂) hbase
      _ = _ := by rw [pow_add]; field_simp [hz.ne']
  have hsplit := noncube_frequency_mass_split H (V := V)
    (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1,(hH h hh).2.2.1⟩) F (fun _ => sq_nonneg _)
  have hempty : H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro h hh
    exact (hH h hh).2.2.2
  rw [hempty,Finset.sum_empty,zero_add] at hsplit
  exact hsplit.trans hlarge

end CubicFirstMoment

end

end OAI
