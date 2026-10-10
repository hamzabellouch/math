import OAI.NumberTheory.CubicMoment.Angular.AngularSmallPairParts

namespace OAI

/-! Balanced full-factor estimates on the original, possibly ramified rows. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem balanced_angular_smalltwist_smooth_fiber_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (k : Eisenstein × Eisenstein)
        (v q : Eisenstein) (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1 ∧ pairSmallParts v p = k) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_pair_power hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨C,T,hC,hT,?_⟩
  intro S k v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht hS
  by_cases hne : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hne
    have hk : primary k.1 ∧ primary k.2 := by
      rw [← (hS p₀ hp₀).2.2.2.2]
      exact ⟨primarySmallPart_primary v (hS p₀ hp₀).1.1,
        primarySmallPart_primary v (hS p₀ hp₀).1.2.1⟩
    let r := (3*(k.1*k.2))*q
    let η' := productResidueChar (primaryMixedResidueChar k.1 k.2 hk.1 hk.2) η
    have hr : r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (mul_ne_zero (primary_ne_zero hk.1) (primary_ne_zero hk.2))) hq
    have hrN : norm r ≤ Y^(1/1000:ℝ) := by
      apply le_trans _ hsize
      dsimp [r]
      rw [← (hS p₀ hp₀).2.2.2.2]
      exact smallPartModulus_norm_le (hS p₀ hp₀).1.2.2.1 (hS p₀ hp₀).1.2.2.2.1 hv
    rw [angular_small_pair_fiber_smooth_moment ℓ v k S hk
      (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2.2.2.2⟩)]
    apply hbound (S.image (pairOutsideParts v)) r η' Y Z t hY hr
      (productResidueChar_angular_units _ _ (primaryMixedResidueChar_trivialInfinity hk.1 hk.2) hη)
      hZY hYZ hrN ht
    intro o ho
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ho
    have hsp := hS p hp
    have hpp := hsp.1
    refine ⟨primaryOutsidePart_primary v hpp.1,primaryOutsidePart_squarefree v hpp.1 hpp.2.2.1,
      primaryOutsidePart_primary v hpp.2.1,primaryOutsidePart_squarefree v hpp.2.1 hpp.2.2.2.1,
      (primaryOutsidePart_norm_le v hpp.1).trans hsp.2.1,
      (primaryOutsidePart_norm_le v hpp.2.1).trans hsp.2.2.1,
      outside_parts_coprime v hpp.1 hpp.2.1 hpp.2.2.2.2,?_,?_⟩
    · intro hu
      exact primaryOutsidePart_nonunit hpp.1 hpp.2.2.1 hv hsp.2.2.2.1
        (isUnit_of_mul_isUnit_left hu)
    · dsimp [r]
      rw [← hsp.2.2.2.2]
      exact outside_parts_coprime_local hpp.1 hpp.2.1 hpp.2.2.1 hpp.2.2.2.1 hv h3 hqv
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith [hT.trans hY]) _)

theorem balanced_angular_smalltwist_smooth_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein)
        (η : MulChar (Residues q) ℂ) (Y Z t : ℝ),
      Y₀ ≤ Y → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(17/50:ℝ) ∧
        norm p.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm p.1) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(221/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_smooth_fiber_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨D,hD,hcard⟩ := pair_small_parts_card (show (0:ℝ) < 1 by norm_num)
  refine ⟨D*C,T,mul_nonneg hD.le hC,hT,?_⟩
  intro S v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hv1 := one_le_norm hv
  have hq1 := one_le_norm hq
  have hvY : norm v ≤ Y^(1/1000:ℝ) := by
    have hcoef : norm v ≤ 9*norm v^2*norm q := by
      calc
        _ ≤ norm v^2 := by nlinarith
        _ ≤ norm v^2*norm q := by nlinarith [sq_nonneg (norm v)]
        _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (norm v)) (norm_nonneg q)]
    exact hcoef.trans hsize
  have hc := hcard S v hv (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.2.1,
    (hS p hp).1.2.1,(hS p hp).1.2.2.2.1⟩)
  norm_num only [mul_one] at hc
  have hp : norm v^(2:ℝ) ≤ Y^(1/500:ℝ) := by
    calc
      _ ≤ (Y^(1/1000:ℝ))^(2:ℝ) := Real.rpow_le_rpow (norm_nonneg v) hvY (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; norm_num
  have hf (k : Eisenstein × Eisenstein) (_hk : k ∈ S.image (pairSmallParts v)) :
      (∑ p ∈ S.filter (fun p => pairSmallParts v p = k),
        ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
    apply hbound _ k v q η Y Z t hY hv hq h3 hqv hη hZY hYZ hsize ht
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨(hS p hm.1).1,(hS p hm.1).2.1,(hS p hm.1).2.2.1,(hS p hm.1).2.2.2,hm.2⟩
  calc
    _ = ∑ k ∈ S.image (pairSmallParts v), ∑ p ∈ S.filter (fun p => pairSmallParts v p = k),
        ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2 :=
      (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem (pairSmallParts v) hp) _).symm
    _ ≤ ∑ _k ∈ S.image (pairSmallParts v), C*Y^(11/5:ℝ) := Finset.sum_le_sum hf
    _ = ((S.image (pairSmallParts v)).card:ℝ)*(C*Y^(11/5:ℝ)) := by simp
    _ ≤ (D*Y^(1/500:ℝ))*(C*Y^(11/5:ℝ)) :=
      mul_le_mul_of_nonneg_right (hc.trans (mul_le_mul_of_nonneg_left hp hD.le)) (by positivity)
    _ = (D*C)*Y^((1/500:ℝ)+11/5) := by rw [Real.rpow_add hY0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
