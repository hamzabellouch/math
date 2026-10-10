import Mathlib
import OAI.NumberTheory.CubicGram.SieveMajorant

namespace OAI

/-! Base bounds for thin smoothed cubic sieve families. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma thin_primary_card_le {S : Finset Eisenstein} {N : ℝ} (hN : 0 < N)
    (hS : ∀ a ∈ S, primary a) (hSN : ∀ a ∈ S, norm a ≤ Real.sqrt 2*N) :
    (S.card : ℝ) ≤ 36*N := by
  have hs : S ⊆ nonzeroNormBall (2*N) := by
    intro a ha
    have h2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_nonneg 2]
    exact mem_nonzeroNormBall.mpr ⟨(hSN a ha).trans (mul_le_mul_of_nonneg_right h2 hN.le),primary_ne_zero (hS a ha)⟩
  calc
    _ ≤ ((nonzeroNormBall (2*N)).card : ℝ) := by exact_mod_cast Finset.card_le_card hs
    _ ≤ 18*(2*N) := nonzeroNormBall_card_le (by positivity)
    _ = _ := by ring

theorem primarySmoothedSieveMass_base_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z N : ℝ), 0 < Z → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      ‖primarySmoothedSieveMass S u W Z‖ ≤ C*(Z+N^2)*
        ∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
  obtain ⟨C₀,hC₀,hrec⟩ := coprimeGramForm_base_bound W hW hW'
  obtain ⟨D,hD,hdiag⟩ := primaryCharacterGram_one_one_bound W hW hW'.continuous
  let C := max (36*C₀) D
  have hC : 0 < C := hD.trans_le (le_max_right _ _)
  have hC₀C : 36*C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro S hS u Z N hZ hN hSN
  have hblock (k : Eisenstein) (hkS : k ∈ commonRowFactors S)
      (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      let m := ∏ p ∈ s, p
      ‖(idealMoebius m : ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C*(Z+N^2)*commonBlockEnergy S u k := by
    dsimp only
    let m := ∏ p ∈ s, p
    have hk := commonRowFactors_spec hS hkS
    have hm : primary m := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk.1 (Finset.mem_powerset.mp hs hp)).1.1)
    have hnk : 0 < norm k := norm_pos_of_ne_zero (primary_ne_zero hk.1)
    have hnm : 0 < norm m := norm_pos_of_ne_zero (primary_ne_zero hm)
    have hnk1 : 1 ≤ norm k := one_le_norm (primary_ne_zero hk.1)
    have hnm1 : 1 ≤ norm m := one_le_norm (primary_ne_zero hm)
    have hrpos : 0 < N/norm k := div_pos hN hnk
    have hrle : N/norm k ≤ N := (div_le_self hN.le hnk1)
    have hzle : Z/norm m ≤ Z := (div_le_self hZ.le hnm1)
    have hre := residualRows_primary hk.1 hS
    have hh : ‖coprimeGramForm (residualRows S k) (commonBlockCoefficient u k m) W (Z/norm m)‖ ≤
        C*(Z+N^2)*commonBlockEnergy S u k := by
      by_cases hkN : norm k < N
      · have hb := hrec (residualRows S k)
          (fun a ha => ⟨(hre a ha).1,(hre a ha).2,
            residualRows_nonunit hk.1 hkN (fun p hp => (hSN p hp).1) a ha⟩)
          (commonBlockCoefficient u k m) (Z/norm m) (N/norm k)
          (div_pos hZ hnm) hrpos (residualRows_norm hk.1 hSN)
        have hc := thin_primary_card_le hrpos (fun a ha => (hre a ha).1)
          (fun a ha => (residualRows_norm hk.1 hSN a ha).2)
        have hbC : C₀*(N/norm k)*(residualRows S k).card ≤ C*(Z+N^2) := by
          calc
            _ ≤ C₀*N*(36*N) := by gcongr; exact hc.trans (by gcongr)
            _ = (36*C₀)*N^2 := by ring
            _ ≤ C*N^2 := mul_le_mul_of_nonneg_right hC₀C (sq_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC.le
        apply hb.trans
        exact mul_le_mul hbC (commonBlockCoefficient_energy_le S hS u hk.1 m)
          (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      · calc
          _ ≤ ‖primaryCharacterGram 1 1 W (Z/norm m)‖ *
              ∑ a ∈ residualRows S k, ‖commonBlockCoefficient u k m a‖^2 :=
            coprimeGramForm_subset_singleton _
              (residualRows_subset_one hk.1 (fun p hp => (hS p hp).1) (le_of_not_gt hkN)
                (fun p hp => (hSN p hp).2)) _ _ _
          _ ≤ (D*(Z/norm m))*commonBlockEnergy S u k :=
            mul_le_mul (hdiag _ (div_pos hZ hnm))
              (commonBlockCoefficient_unweighted_energy_le S hS u hk.1 m)
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by
            calc
              D*(Z/norm m) ≤ D*Z := mul_le_mul_of_nonneg_left hzle hD.le
              _ ≤ C*Z := mul_le_mul_of_nonneg_right hDC hZ.le
              _ ≤ C*(Z+N^2) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le)
            (commonBlockEnergy_nonneg S u k)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one m)).trans hh
  rw [primarySmoothedSieveMass_common_blocks S hS u W hW hW' hZ]
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        ‖(idealMoebius (∏ p ∈ s, p) : ℂ)*coprimeGramForm (residualRows S k)
          (commonBlockCoefficient u k (∏ p ∈ s, p)) W (Z/norm (∏ p ∈ s, p))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => norm_sum_le _ _))
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        C*(Z+N^2)*commonBlockEnergy S u k :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun s hs => hblock k hk s hs))
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                ring

theorem finiteCubicBound_base_thin (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      0 < M → 0 < N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C₀,hC₀,hrec⟩ := primarySmoothedSieveMass_base_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth
  obtain ⟨D,hD,henergy⟩ := common_energy_small_power ε hε
  refine ⟨C₀*D*(Real.sqrt 2)^ε,by positivity,?_⟩
  intro S H M N hM hN hS hH
  apply (finiteCubicBound_le_iff _ _ (by positivity)).mpr
  intro u
  calc
    _ ≤ ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ :=
      finiteCubicMass_le_smoothed S H (fun x hx => (hH x hx).1) u hM (fun x hx => (hH x hx).2)
    _ ≤ C₀*(M+N^2)*(D*(Real.sqrt 2*N)^ε *∑ a ∈ S, ‖u a‖^2) :=
      (hrec S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u M N hM hN
        (fun a ha => (hS a ha).2.2)).trans (mul_le_mul_of_nonneg_left
          (henergy S u (Real.sqrt 2*N) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩))
          (by positivity))
    _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg 2) hN.le]; ring

end CubicFirstMoment
end
end

end OAI
