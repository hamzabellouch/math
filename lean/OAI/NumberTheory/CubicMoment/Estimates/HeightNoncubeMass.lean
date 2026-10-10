import OAI.NumberTheory.CubicMoment.Estimates.HeightAveraging
import OAI.NumberTheory.CubicMoment.Estimates.PolynomialHeightCoreBlock
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreHeightSaving
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeCutoffMass

namespace OAI

/-! The height-averaged noncube cutoff for the actual rough-prime
convolution. The small core uses the ordinary published mean value,
not a low-height prime estimate. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem height_noncube_cutoff_mass
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      1+2*T+|u| ≤ (L r)^(9/25:ℝ) →
      dyadicHeightMean (fullStructuredHeightMass R H 1 e 0 u (W r) X) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hblock⟩ := uniform_core_block_polynomial_height
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ (k+2)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨CB,TB,A,hCB,hblock⟩ := hblock L W hL hW hlo hhi
  obtain ⟨CL,TL,m,hCL,hlow⟩ := low_core_height_log_saving hMV hC hR hW hlo hhi (A+1) k
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((eventually_ge_atTop TB).and
    ((eventually_ge_atTop TL).and (low_core_log_threshold A)))
  refine ⟨CL+2*CI*CB,L₀,m,by positivity,?_⟩
  intro r X B H e u T hL₀' hprod hX hB hBL hH he heN hT hu
  obtain ⟨hTB,hTL,hcut⟩ := hL₀ (L r) hL₀'
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hXone : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : 1 ≤ 2*L r) hc.le).trans (hX i).le
  have hB₂ : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  let V := (Real.log (L r))^(A+1)
  let HS := H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ)))
  let I := largeCoreDyadicIndices V B
  let F := fun J : Finset Eisenstein => fullStructuredHeightMass R J 1 e 0 u (W r) X
  have hcont (J : Finset Eisenstein) : Continuous (F J) :=
    continuous_fullStructuredHeightMass R J 1 e 0 u (W r) X
  have hsmall : dyadicHeightMean (F HS) T ≤
      CL*B^(1/3:ℝ)*(L r)^2/(1+Real.log (L r))^k := by
    exact hlow r X (B^(1/3:ℝ)) HS (hL r) hTL hXone hprod
      (Real.rpow_nonneg (zero_le_one.trans hB) _)
      (fun h hh => (Finset.mem_filter.mp hh).2) 1 e 0 u T hT
  have hlarge : (∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T) ≤
      2*CI*CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
    have hrow : ∀ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*(CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) := by
      intro z hzI
      have hm := (Finset.mem_filter.mp hzI).2
      have hD := coreDyadicConductor_pos z.1 z.2
      have hthreshold : (1+Real.log (L r))^A ≤ 8*coreDyadicConductor z.1 z.2 := by
        dsimp [V] at hm
        nlinarith [hcut,hm.1]
      apply dyadicHeightMean_le_const (hcont _) hTp
      intro t ht
      have hb := hblock r X B z.1 z.2 e (t+u) (coreDyadicBlock B z.1 z.2)
        hTB hprod hX (zero_le_one.trans hB) hBL hm.2 hthreshold he heN
        (height_translation_window hu ht) (Finset.Subset.refl _)
      simpa only [F,fullStructuredHeightMass,fullStructuredAngularSum_zero] using hb
    have hbase : 0 ≤ 2*(CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) := by positivity
    calc
      _ ≤ ∑ _z ∈ I, 2*(CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2)) :=
        Finset.sum_le_sum hrow
      _ = (I.card:ℝ)*(2*(CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2))) := by simp
      _ ≤ (CI*(1+Real.log (L r))^2)*
          (2*(CB*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^(k+2))) :=
        mul_le_mul_of_nonneg_right (hcount V B (L r) hB (hL r) hB₂) hbase
      _ = _ := by rw [pow_add]; field_simp [hz.ne']
  have hsplit : dyadicHeightMean (F H) T ≤
      dyadicHeightMean (F HS) T+∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T := by
    have hc : Continuous (fun t => F HS t+∑ z ∈ I, F (coreDyadicBlock B z.1 z.2) t) :=
      (hcont HS).add (continuous_finsetSum I (fun z _ => hcont _))
    have hs := dyadicHeightMean_mono (hcont H) hc hTp (fun t _ =>
      noncube_frequency_mass_split H hH
        (fun h => ‖fullStructuredAngularSum R h 1 e 0 (t+u) (W r) X‖^2)
        (fun _ => sq_nonneg _))
    rw [dyadicHeightMean_add (hcont HS) (continuous_finsetSum I (fun z _ => hcont _)),
      dyadicHeightMean_sum I (fun z => F (coreDyadicBlock B z.1 z.2)) (fun z _ => hcont _)] at hs
    exact hs
  exact hsplit.trans ((add_le_add hsmall hlarge).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
