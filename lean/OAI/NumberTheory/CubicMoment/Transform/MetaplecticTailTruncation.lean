import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailScale

namespace OAI

/-! A fixed dyadic cutoff, larger than the natural dual length by a
small power, makes the actual metaplectic tail arbitrarily small. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma exists_metaplectic_tail_order {δ : ℝ} (hδ : 0 < δ) (B ε σ H : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ σ ≤ (m:ℝ)-1/2 ∧
      B*(ε+2+σ)-δ*((m:ℝ)-1/2-σ) ≤ -H := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 2 (max (σ+1/2)
    (σ+1/2+(B*(ε+2+σ)+H)/δ)))
  have hm2 : (2:ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hml : max (σ+1/2) (σ+1/2+(B*(ε+2+σ)+H)/δ) < m :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hs : σ+1/2 < m := lt_of_le_of_lt (le_max_left _ _) hml
  have hp : (B*(ε+2+σ)+H)/δ < (m:ℝ)-σ-1/2 := by
    linarith [lt_of_le_of_lt (le_max_right _ _) hml]
  have hmul := (div_lt_iff₀ hδ).mp hp
  refine ⟨m,?_,by linarith,by nlinarith⟩
  have : 2 < m := by exact_mod_cast hm2
  omega

lemma metaplectic_tail_power_absorption {Y R T D J B ε σ δ H A : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T) (hD : 0 < D) (hJ : 0 < J)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hA : 0 ≤ A)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hDB : D ≤ Y^B)
    (hcut : D/J ≤ Y^(-δ)) (horder : B*(ε+2+σ)-δ*A ≤ -H) :
    R^ε*T^2*D^σ*(D/J)^A ≤ Y^(-H) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hr : R^ε ≤ Y^(B*ε) := by
    calc
      _ ≤ (Y^B)^ε := Real.rpow_le_rpow hR.le hRB hε
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  have ht : T^2 ≤ Y^(2*B) := by
    calc
      _ ≤ (Y^B)^2 := pow_le_pow_left₀ hT.le hTB 2
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]; congr 1; ring
  have hd : D^σ ≤ Y^(B*σ) := by
    calc
      _ ≤ (Y^B)^σ := Real.rpow_le_rpow hD.le hDB hσ
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  have hc : (D/J)^A ≤ Y^(-δ*A) := by
    calc
      _ ≤ (Y^(-δ))^A := Real.rpow_le_rpow (div_nonneg hD.le hJ.le) hcut hA
      _ = _ := (Real.rpow_mul hYp.le _ _).symm
  calc
    _ ≤ Y^(B*ε)*Y^(2*B)*Y^(B*σ)*Y^(-δ*A) := by gcongr
    _ = Y^(B*(ε+2+σ)-δ*A) := by
      rw [←Real.rpow_add hYp,←Real.rpow_add hYp,←Real.rpow_add hYp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY horder

/-- No tail estimate is assumed: the raw theta support, actual transform
and polynomial scale bounds give every requested negative power. -/
theorem metaplectic_twisted_tail_arbitrary_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (B H : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ σ ≤ (m:ℝ)-1/2 ∧ 0 ≤ C ∧
      ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X J T : ℝ, 1 ≤ Y → 0 < X → 0 < J → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → norm r^2*T^4/X ≤ Y^B →
      (norm r^2*T^4/X)/J ≤ Y^(-δ) → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-H) := by
  obtain ⟨m,hm2,hms,horder⟩ := exists_metaplectic_tail_order hδ B 1 σ H
  obtain ⟨C,hC,hbound⟩ := metaplectic_twisted_tail_natural_cutoff ha ℓ m W hW hpos hsm
    (by norm_num : (0:ℝ) < 1) hσ hms
  refine ⟨m,C,hm2,hms,hC,?_⟩
  intro r hr hsr Y X J T hY hX hJ hT hRB hTB hDB hcut t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hD : 0 < norm r^2*T^4/X := by positivity
  have hs := metaplectic_tail_power_absorption hY hR hTp hD hJ
    (by norm_num : (0:ℝ) ≤ 1) hσ.le (sub_nonneg.mpr hms)
    hRB hTB hDB hcut horder
  calc
    _ ≤ C*norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := hbound r hr hsr X J T hX hJ hT t ht
    _ = C*(norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC

end CubicFirstMoment

end

end OAI
