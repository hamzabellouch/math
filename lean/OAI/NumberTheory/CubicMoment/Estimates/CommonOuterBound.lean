import OAI.NumberTheory.CubicMoment.Estimates.CommonGramRemainder
import OAI.NumberTheory.CubicMoment.Estimates.OuterCostMonotone
import OAI.NumberTheory.CubicMoment.Estimates.PrimeCommonRows

namespace OAI

/-! A uniform bound for the actual shortened common-factor rows. The
roughness threshold enters their lengths, rather than a new hypothesis
about character cancellation. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonOuterCost (W : ℝ → ℂ) (C ε B Q A L D : ℝ) : ℝ :=
  (‖normProfileFourier W 0‖/9)*A + C*(B*Q^2*L^3/A)^ε*
    (max 1 (L/D)+A^(1/3:ℝ)*max 1 (L/D)+A^(2/3:ℝ)*(max 1 (L/D))^(2/3:ℝ))

lemma commonOuterCost_nonneg (W : ℝ → ℂ) {C ε B Q A L D : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    0 ≤ commonOuterCost W C ε B Q A L D := by
  unfold commonOuterCost
  positivity

 theorem commonGramBlock_outer_bound {ε B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : 1 ≤ B) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Q A L D : ℝ),
      1 ≤ Q → 0 < A → 1 ≤ L → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ B*L) →
      ∀ k ∈ commonRowFactors S, D ≤ norm k →
      ‖commonGramBlock S u W (A/Q^2) k‖ ≤
        (2:ℝ)^(primaryPrimeFactors k).card*commonOuterCost W C ε B Q A L D*
          commonBlockEnergy S u k := by
  obtain ⟨C,hC,hbound⟩ := coprimeGramForm_outer_complete hε hε1 hB W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Q A L D hQ hA hL hD hS k hkS hkD
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hk := commonRowFactors_spec hS' hkS
  have hk0 := primary_ne_zero hk.1
  have hkN := norm_pos_of_ne_zero hk0
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hr := residualRows_primary hk.1 hS'
  have hkBL : norm k ≤ B*L := by
    obtain ⟨⟨a,b⟩,hab,hkab⟩ := Finset.mem_image.mp hkS
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    have hd : k ∣ a := hkab ▸
      (primaryCommonFactor_spec (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1).2.2.1
    exact (norm_le_of_dvd (primary_ne_zero (hS a ha).1) hd).trans (hS a ha).2.2.2
  have hrows : ∀ a ∈ residualRows S k,
      primary a ∧ Squarefree a ∧ max 1 (L/norm k) ≤ norm a ∧ norm a ≤ B*max 1 (L/norm k) := by
    intro a ha
    have hka := hS (k*a) ((mem_residualRows hk0).mp ha)
    have hlo : L/norm k ≤ norm a := (div_le_iff₀ hkN).mpr (by
      simpa only [norm_mul_eq,mul_comm] using hka.2.2.1)
    have hhi : norm a ≤ B*(L/norm k) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hkN).mpr
      simpa only [norm_mul_eq,mul_div_assoc,mul_comm] using hka.2.2.2
    exact ⟨(hr a ha).1,(hr a ha).2,
      max_le (one_le_norm (primary_ne_zero (hr a ha).1)) hlo,
      hhi.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans hB))⟩
  rw [commonGramBlock_moebius S hS' u W hW hW' (by positivity) hk.1 hk.2]
  have heach (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      ‖(idealMoebius (∏ p ∈ s,p):ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k (∏ p ∈ s,p)) W (A/Q^2/norm (∏ p ∈ s,p))‖ ≤
      commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := by
    let m := ∏ p ∈ s,p
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : m ∣ k := (primary_subsets_prod_dvd hk.1 (Finset.mem_powerset.mp hs) k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).2)
    have hscale := quotient_scale_bound hA hL hQ hD (one_le_norm hk0)
      (norm_le_of_dvd hk0 hmk) (one_le_norm (primary_ne_zero hm)) hkBL hB hkD
    have hh := hbound (residualRows S k) (commonBlockCoefficient u k m)
      (A/Q^2/norm m) (max 1 (L/norm k)) hscale.1 hscale.2.1 hrows
    have hcost := outer_cost_mono hε.le hC.le (by positivity : 0 ≤ ‖normProfileFourier W 0‖/9)
      hscale.1 hscale.2.2.1 (by positivity : 0 ≤ max 1 (L/norm k)) hscale.2.2.2.1 hscale.2.2.2.2
    calc
      _ ≤ ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m)
          W (A/Q^2/norm m)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)
      _ ≤ _ := hh.trans ((mul_le_mul_of_nonneg_right hcost
        (Finset.sum_nonneg (fun _ _ => by positivity))).trans
        (mul_le_mul_of_nonneg_left (commonBlockCoefficient_energy_le S hS' u hk.1 m)
          (commonOuterCost_nonneg W hC.le (zero_le_one.trans hB) hA.le (zero_le_one.trans hL))))
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s,p):ℂ)*coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s,p)) W (A/Q^2/norm (∏ p ∈ s,p))‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ (primaryPrimeFactors k).powerset,
        commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := Finset.sum_le_sum heach
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]; ring

end CubicFirstMoment

end

end OAI
