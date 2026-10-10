import OAI.NumberTheory.CubicMoment.Estimates.ProfileOuterBound
import OAI.NumberTheory.CubicMoment.Estimates.LargeCommonSaving

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem commonGramBlock_outer_nonzero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Q A L D : ℝ),
      1 ≤ Q → 0 < A → 1 ≤ L → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ (2:ℝ)*L) →
      ∀ k ∈ commonRowFactors S, D ≤ norm k →
      ‖commonGramBlock S u P.V (A/Q^2) k-commonGramZeroMode S u P.V (A/Q^2) k‖ ≤
        (2:ℝ)^(primaryPrimeFactors k).card*commonNonzeroCost (C*P.cost) ε (2:ℝ) Q A L D*
          commonBlockEnergy S u k := by
  obtain ⟨C₀,hC₀,hbound₀⟩ := coprimeGramForm_outer_nonzero hε hε1
  refine ⟨C₀,hC₀,?_⟩
  intro P S u Q A L D hQ hA hL hD hS k hkS hkD
  let C := C₀*P.cost
  have hC : 0 < C := mul_pos hC₀ P.cost_pos
  have hbound := hbound₀ P
  have hB : (1:ℝ) ≤ 2 := by norm_num
  have hS' : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hk := commonRowFactors_spec hS' hkS
  have hk0 := primary_ne_zero hk.1
  have hkN := norm_pos_of_ne_zero hk0
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hr := residualRows_primary hk.1 hS'
  have hkBL : norm k ≤ (2:ℝ)*L := by
    obtain ⟨⟨a,b⟩,hab,hkab⟩ := Finset.mem_image.mp hkS
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    have hd : k ∣ a := hkab ▸
      (primaryCommonFactor_spec (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1).2.2.1
    exact (norm_le_of_dvd (primary_ne_zero (hS a ha).1) hd).trans (hS a ha).2.2.2
  have hrows : ∀ a ∈ residualRows S k,
      primary a ∧ Squarefree a ∧ max 1 (L/norm k) ≤ norm a ∧ norm a ≤ (2:ℝ)*max 1 (L/norm k) := by
    intro a ha
    have hka := hS (k*a) ((mem_residualRows hk0).mp ha)
    have hlo : L/norm k ≤ norm a := (div_le_iff₀ hkN).mpr (by
      simpa only [norm_mul_eq,mul_comm] using hka.2.2.1)
    have hhi : norm a ≤ (2:ℝ)*(L/norm k) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hkN).mpr
      simpa only [norm_mul_eq,mul_div_assoc,mul_comm] using hka.2.2.2
    exact ⟨(hr a ha).1,(hr a ha).2,
      max_le (one_le_norm (primary_ne_zero (hr a ha).1)) hlo,
      hhi.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans hB))⟩
  rw [commonGramBlock_sub_zero_moebius S hS' u P.V P.compact P.smooth (by positivity) hk.1 hk.2]
  have heach (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      ‖(idealMoebius (∏ p ∈ s,p):ℂ)*(coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k (∏ p ∈ s,p)) P.V (A/Q^2/norm (∏ p ∈ s,p))-
          coprimePoissonDyad (residualRows S k) {0} (commonBlockCoefficient u k (∏ p ∈ s,p)) P.V (A/Q^2/norm (∏ p ∈ s,p)))‖ ≤
      commonNonzeroCost C ε (2:ℝ) Q A L D*commonBlockEnergy S u k := by
    let m := ∏ p ∈ s,p
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hmk : m ∣ k := (primary_subsets_prod_dvd hk.1 (Finset.mem_powerset.mp hs) k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).2)
    have hscale := quotient_scale_bound hA hL hQ hD (one_le_norm hk0)
      (norm_le_of_dvd hk0 hmk) (one_le_norm (primary_ne_zero hm)) hkBL hB hkD
    have hh := hbound (residualRows S k) (commonBlockCoefficient u k m)
      (A/Q^2/norm m) (max 1 (L/norm k)) hscale.1 hscale.2.1 hrows
    have hcost₀ := outer_cost_mono hε.le hC.le (by norm_num : (0:ℝ) ≤ 0)
      hscale.1 hscale.2.2.1 (by positivity : 0 ≤ max 1 (L/norm k)) hscale.2.2.2.1 hscale.2.2.2.2
    have hcost := hcost₀
    simp only [zero_mul,zero_add] at hcost
    calc
      _ ≤ ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m)
          P.V (A/Q^2/norm m)-coprimePoissonDyad (residualRows S k) {0}
          (commonBlockCoefficient u k m) P.V (A/Q^2/norm m)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)
      _ ≤ _ := hh.trans ((mul_le_mul_of_nonneg_right hcost
        (Finset.sum_nonneg (fun _ _ => by positivity))).trans
        (mul_le_mul_of_nonneg_left (commonBlockCoefficient_energy_le S hS' u hk.1 m)
          (commonNonzeroCost_nonneg hC.le (zero_le_one.trans hB) hA.le (zero_le_one.trans hL))))
  calc
    _ ≤ ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s,p):ℂ)*(coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s,p)) P.V (A/Q^2/norm (∏ p ∈ s,p))-
          coprimePoissonDyad (residualRows S k) {0} (commonBlockCoefficient u k (∏ p ∈ s,p)) P.V (A/Q^2/norm (∏ p ∈ s,p)))‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ (primaryPrimeFactors k).powerset,
        commonNonzeroCost C ε (2:ℝ) Q A L D*commonBlockEnergy S u k := Finset.sum_le_sum heach
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]; ring


theorem large_common_nonzero_bound {ε ζ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hζ : 0 < ζ)
    :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (A N D : ℝ), 0 < A → 1 ≤ N → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
        (commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)‖ ≤
      commonNonzeroCost (C*P.cost) ε 2 1 A N D * (E*(2*N)^ζ*∑ a ∈ S, ‖v a‖^2) := by
  obtain ⟨C₀,hC₀,hblock₀⟩ := commonGramBlock_outer_nonzero hε hε₁
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power ζ hζ
  refine ⟨C₀,E,hC₀,hE,?_⟩
  intro P S v A N D hA hN hD hS
  let C := C₀*P.cost
  have hC : 0 < C := mul_pos hC₀ P.cost_pos
  have hblock := hblock₀ P
  have hcost : 0 ≤ commonNonzeroCost C ε 2 1 A N D :=
    commonNonzeroCost_nonneg hC.le (by norm_num) hA.le (zero_le_one.trans hN)
  have hb (k : Eisenstein) (hk : k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k)) :
      ‖(commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)‖ ≤ commonNonzeroCost C ε 2 1 A N D *
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by
    have hh := hblock S v 1 A N D (by norm_num) hA hN hD hS k
      (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    simpa only [one_pow,div_one,mul_assoc,mul_comm,mul_left_comm] using hh
  calc
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
        commonNonzeroCost C ε 2 1 A N D *
          ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = commonNonzeroCost C ε 2 1 A N D *
        (∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
          (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by rw [Finset.mul_sum]
    _ ≤ commonNonzeroCost C ε 2 1 A N D *
        (∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by
      apply mul_le_mul_of_nonneg_left _ hcost
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k hk _
      unfold commonBlockEnergy
      positivity
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (henergy S v (2*N) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)) hcost


theorem large_common_nonzero_power {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (A N : ℝ), 0 < A → 1 ≤ N → N^(1-δ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => N^δ ≤ norm k),
        (commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)‖ ≤
      (K*P.cost)*A^(2/3:ℝ)*N^(2/3-δ/8)*∑ a ∈ S, ‖v a‖^2 := by
  obtain ⟨C₀,E,hC₀,hE,hbound₀⟩ := large_common_nonzero_bound
    (ε := δ/100) (ζ := δ/8) (by positivity) (by linarith) (by positivity)
  refine ⟨3*C₀*(2:ℝ)^(δ/100)*E*(2:ℝ)^(δ/8),by positivity,?_⟩
  intro P S v A N hA hN hAN hS
  let C := C₀*P.cost
  have hC : 0 < C := mul_pos hC₀ P.cost_pos
  have hbound := hbound₀ P
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hb := hbound S v A N (N^δ) hA hN (Real.one_le_rpow hN hδ.le) hS
  have hc := commonNonzeroCost_power_saving hC.le (by norm_num : (0:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) ≤ 1) hN hN hA hδ hδ₁ (le_refl δ) hAN
  apply hb.trans
  calc
    _ ≤ (3*C*(2:ℝ)^(δ/100)*A^(2/3:ℝ)*N^(2/3:ℝ)*N^(-δ/4))*
        (E*(2*N)^(δ/8)*∑ a ∈ S, ‖v a‖^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hNp.le]
      have he : N^(2/3:ℝ)*N^(-δ/4)*N^(δ/8) = N^(2/3-δ/8) := by
        rw [← Real.rpow_add hNp,← Real.rpow_add hNp]
        congr 1
        ring
      calc
        _ = (3*C*(2:ℝ)^(δ/100)*E*(2:ℝ)^(δ/8))*A^(2/3:ℝ)*
          (N^(2/3:ℝ)*N^(-δ/4)*N^(δ/8))*∑ a ∈ S, ‖v a‖^2 := by ring
        _ = _ := by rw [he]; dsimp [C]; ring


end CubicFirstMoment.ProfileControl

end

end OAI
