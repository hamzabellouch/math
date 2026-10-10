import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment
import OAI.NumberTheory.CubicMoment.Estimates.LowNoncubeMass
import OAI.NumberTheory.CubicMoment.Estimates.CoreIndexLogCount

namespace OAI

/-! The full finite noncube cutoff, with all arithmetic decompositions,
small conductors and exceptional conductor regions included. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma cube_cutoff_le_length {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hBL : B ≤ L^2) :
    B^(1/3:ℝ) ≤ L := by
  have hcube : B ≤ L^3 := hBL.trans (pow_le_pow_right₀ hL (by norm_num))
  have hr := Real.rpow_le_rpow hB hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (L^3)^(1/3:ℝ) = L := by
    rw [← Real.rpow_natCast L 3,← Real.rpow_mul (zero_le_one.trans hL)]
    norm_num
  rwa [he] at hr

theorem noncube_cutoff_mass (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ C T₀ : ℝ, 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hblock⟩ := uniform_core_block_log_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hc hc₁ hR hGI hGQ (k+2) U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨CB,TB,A,hCB,hblock⟩ := hblock L W hL hW hlo hhi
  obtain ⟨CL,TL,hCL,hlow⟩ := low_noncube_mass (d₁ := σ) (d₂ := 1)
    hSW hW hlo hc hσ.le (by norm_num) hR (A+1) k U (by omega)
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop TB).and
    ((eventually_ge_atTop TL).and (low_core_log_threshold A)))
  refine ⟨CL+CI*CB,T₀,by positivity,?_⟩
  intro r X B H e u hT₀ hprod hX hB hBL hH he heN hu
  obtain ⟨hTB,hTL,hcut⟩ := hT (L r) hT₀
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hB₂ : B ≤ (L r)^2 := by
    apply hBL.trans
    rw [← Real.rpow_natCast (L r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hL r) (by norm_num; linarith)
  have hroot : B^(1/3:ℝ) ≤ (L r)^(1:ℝ) := by
    simpa only [Real.rpow_one] using cube_cutoff_le_length (zero_le_one.trans hB) (hL r) hB₂
  let V := (Real.log (L r))^(A+1)
  let F (h : Eisenstein) := ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2
  have hsmall : (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), F h) ≤
      CL*B^(1/3:ℝ)*(L r)^2/(1+Real.log (L r))^k := by
    apply hlow r X (B^(1/3:ℝ)) _ hTL hprod
      (fun a => (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans (hX a).le)
      (Real.rpow_nonneg (zero_le_one.trans hB) _) hroot
      (fun h hh => (Finset.mem_filter.mp hh).2) e he heN u hu
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
  have hsplit := noncube_frequency_mass_split H (V := V) hH F (fun _ => sq_nonneg _)
  apply hsplit.trans
  apply (add_le_add hsmall hlarge).trans_eq
  ring

end CubicFirstMoment

end

end OAI
