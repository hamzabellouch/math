import OAI.NumberTheory.CubicMoment.Estimates.SmallPartGeometry
import OAI.NumberTheory.CubicMoment.Angular.AngularSmallPartCharacter

namespace OAI

/-! Exact transfer from an original row fiber to its coprime outside parts. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularSmallTwistSmoothSum_factor (ℓ : ℤ) {a b s u d w q : Eisenstein}
    (hs : primary s) (hu : primary u) (hd : primary d) (hw : primary w)
    (ha : a = s*u) (hb : b = d*w) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t =
      primaryAngularSmallTwistSmoothSum ℓ u w ((3*(s*d))*q)
        (productResidueChar (primaryMixedResidueChar s d hs hd) η) W Z t := by
  unfold primaryAngularSmallTwistSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,productResidueChar_mk,primaryMixedResidueChar_primary hs hd hx]
    rw [ha,hb,mixedCubic_modulus_mul (primary_ne_zero hs) (primary_ne_zero hu)
      (primary_ne_zero hd) (primary_ne_zero hw)]
    ring
  · simp only [ite_eq_right hx]

lemma angular_small_part_fiber_smooth_moment (ℓ : ℤ) (v s : Eisenstein) (P : Finset Eisenstein)
    {b q : Eisenstein} (hs : primary s) (hb : primary b)
    (hP : ∀ a ∈ P, primary a ∧ primarySmallPart v a = s)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) =
      ∑ u ∈ P.image (primaryOutsidePart v),
        ‖primaryAngularSmallTwistSmoothSum ℓ u (primaryOutsidePart v b)
          ((3*(s*primarySmallPart v b))*q)
          (productResidueChar (primaryMixedResidueChar s (primarySmallPart v b)
            hs (primarySmallPart_primary v hb)) η) W Z t‖^2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [primaryAngularSmallTwistSmoothSum_factor ℓ hs (primaryOutsidePart_primary v (hP a ha).1)
      (primarySmallPart_primary v hb) (primaryOutsidePart_primary v hb)
      (by rw [← (hP a ha).2,primary_small_outside_mul v (hP a ha).1])
      (primary_small_outside_mul v hb).symm]
  · intro a ha c hc he
    have ha' := primary_small_outside_mul v (hP a ha).1
    have hc' := primary_small_outside_mul v (hP c hc).1
    rw [(hP a ha).2,he] at ha'
    rw [(hP c hc).2] at hc'
    exact ha'.symm.trans hc'

theorem first_angular_smalltwist_smooth_fiber_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (s v b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → v ≠ 0 → q ≠ 0 →
      (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      1 ≤ N → N ≤ Y^(1001/1000:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b*(9*norm v^2*norm q)^2 ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧
        norm v < norm a ∧ primarySmallPart v a = s) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(23/10:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := first_angular_smalltwist_smooth_power_at_height hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨C,T,hC,hT,?_⟩
  intro P s v b q η N Y Z t hY hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht hP
  by_cases hne : P.Nonempty
  · obtain ⟨a₀,ha₀⟩ := hne
    have hs : primary s := (hP a₀ ha₀).2.2.2.2.2 ▸ primarySmallPart_primary v (hP a₀ ha₀).1
    let r := (3*(s*primarySmallPart v b))*q
    let η' := productResidueChar (primaryMixedResidueChar s (primarySmallPart v b)
      hs (primarySmallPart_primary v hb)) η
    have hr : r ≠ 0 := by
      dsimp [r]
      rw [← (hP a₀ ha₀).2.2.2.2.2]
      exact smallPartModulus_ne_zero v (hP a₀ ha₀).1 hb hq
    have hrN : norm r ≤ 9*norm v^2*norm q := by
      dsimp [r]
      rw [← (hP a₀ ha₀).2.2.2.2.2]
      exact smallPartModulus_norm_le (hP a₀ ha₀).2.1 hsb hv
    rw [angular_small_part_fiber_smooth_moment ℓ v s P hs hb
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2.2.2.2⟩)]
    apply hbound (P.image (primaryOutsidePart v)) (primaryOutsidePart v b) r η' N Y Z t hY
      (primaryOutsidePart_primary v hb) (primaryOutsidePart_squarefree v hb hsb) hr
      (productResidueChar_angular_units _ _ (primaryMixedResidueChar_trivialInfinity hs (primarySmallPart_primary v hb)) hη)
    · intro u hu
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      dsimp [r]
      rw [← (hP a ha).2.2.2.2.2]
      exact outside_parts_coprime_local (hP a ha).1 hb (hP a ha).2.1 hsb hv h3 hqv
    · exact hN
    · exact hNY
    · exact hZY
    · exact hYZ
    · exact mul_le_mul (primaryOutsidePart_norm_le v hb)
        (pow_le_pow_left₀ (norm_nonneg r) hrN 2) (sq_nonneg _) (norm_nonneg b) |>.trans hsize
    · exact ht
    · intro u hu
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      refine ⟨primaryOutsidePart_primary v (hP a ha).1,
        primaryOutsidePart_squarefree v (hP a ha).1 (hP a ha).2.1,
        (primaryOutsidePart_norm_le v (hP a ha).1).trans (hP a ha).2.2.1,
        outside_parts_coprime v (hP a ha).1 hb (hP a ha).2.2.2.1,?_⟩
      intro hunit
      exact primaryOutsidePart_nonunit (hP a ha).1 (hP a ha).2.1 hv
        (hP a ha).2.2.2.2.1 (isUnit_of_mul_isUnit_left hunit)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith [hT.trans hY]) _)

/-- The small-prime parts are summed over an actual partition of the rows.
Their number is bounded arithmetically, so no partition cost is assumed. -/
theorem first_angular_smalltwist_smooth_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (v b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → v ≠ 0 → q ≠ 0 →
      (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      1 ≤ N → N ≤ Y^(1001/1000:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b*(9*norm v^2*norm q)^2 ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ norm v < norm a) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(231/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := first_angular_smalltwist_smooth_fiber_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨D,hD,hcount⟩ := smallPrimeParts_card (show (0:ℝ) < 1 by norm_num)
  refine ⟨C*D,T,mul_nonneg hC hD.le,hT,?_⟩
  intro P v b q η N Y Z t hY hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht hP
  have hY1 : 1 ≤ Y := hT.trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hv1 : 1 ≤ norm v := one_le_norm hv
  have hq1 : 1 ≤ norm q := one_le_norm hq
  have hb1 : 1 ≤ norm b := one_le_norm (primary_ne_zero hb)
  have hvY : norm v ≤ Y^(1/1000:ℝ) := by
    have hcoef : norm v ≤ 9*norm v^2*norm q := by
      calc
        _ ≤ norm v^2 := by nlinarith
        _ ≤ norm v^2*norm q := by nlinarith [sq_nonneg (norm v)]
        _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (norm v)) (norm_nonneg q)]
    have hp : 0 ≤ 9*norm v^2*norm q := by positivity [norm_nonneg q]
    have hlarge : norm v ≤ norm b*(9*norm v^2*norm q)^2 := by
      calc
        _ ≤ 9*norm v^2*norm q := hcoef
        _ ≤ (9*norm v^2*norm q)^2 := by nlinarith [hv1.trans hcoef]
        _ ≤ _ := by nlinarith [sq_nonneg (9*norm v^2*norm q)]
    exact hlarge.trans hsize
  have hc := hcount P v hv (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1⟩)
  rw [Real.rpow_one] at hc
  have hrow (s : Eisenstein) (_hs : s ∈ P.image (primarySmallPart v)) :
      (∑ a ∈ P.filter (fun a => primarySmallPart v a = s),
        ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(23/10:ℝ) := by
    apply hbound (P.filter (fun a => primarySmallPart v a = s)) s v b q η N Y Z t
      hY hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht
    intro a ha
    have hm := Finset.mem_filter.mp ha
    exact ⟨(hP a hm.1).1,(hP a hm.1).2.1,(hP a hm.1).2.2.1,
      (hP a hm.1).2.2.2.1,(hP a hm.1).2.2.2.2,hm.2⟩
  calc
    _ = ∑ s ∈ P.image (primarySmallPart v), ∑ a ∈ P.filter (fun a => primarySmallPart v a = s),
        ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2 :=
      (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem (primarySmallPart v) ha) _).symm
    _ ≤ ∑ _s ∈ P.image (primarySmallPart v), C*Y^(23/10:ℝ) := Finset.sum_le_sum hrow
    _ = ((P.image (primarySmallPart v)).card:ℝ)*(C*Y^(23/10:ℝ)) := by simp
    _ ≤ (D*Y^(1/1000:ℝ))*(C*Y^(23/10:ℝ)) :=
      mul_le_mul_of_nonneg_right (hc.trans (mul_le_mul_of_nonneg_left hvY hD.le)) (by positivity)
    _ = (C*D)*Y^((1/1000:ℝ)+23/10) := by rw [Real.rpow_add hY0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
