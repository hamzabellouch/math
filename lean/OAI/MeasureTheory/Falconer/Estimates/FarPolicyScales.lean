import OAI.MeasureTheory.Falconer.Estimates.FarData
import OAI.MeasureTheory.Falconer.Estimates.DescriptorInverseRegime

namespace OAI

/-! # The recursive split supplies the far-branch scale conditions

The estimates use the actual largest remaining descriptor length. The
angular multiplier scale is one, which is preserved by the normalized
inverse construction. All constants are chosen before the terminal depth.
-/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)

noncomputable def descriptorListScale (B : ℝ) (N : ℕ) (σ : ℝ) (L : ℕ)
    (F : Finset PolicyDescriptor) : ℝ :=
  (F.card:ℝ)*B*(8*max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ)))

theorem eventual_descriptor_list_scale (P : ℕ) {B σ : ℝ}
    (hB : 1 ≤ B) (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ F : Finset PolicyDescriptor,
      F.card ≤ (N+1)^P →
      4 ≤ descriptorDerivativeScale N σ L ∧
      2*(descriptorListScale B N σ L F+1) ≤ descriptorDerivativeScale N σ L := by
  obtain ⟨N₁,hcount⟩ := descriptor_count_subpower P (half_pos hσ)
  obtain ⟨N₂,hconstant⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) (32*B)
  obtain ⟨N₃,hfour⟩ := Regularization.fixed_constant_absorbed hσ 4
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN L F hcard
  have h₁ := hcount N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) F hcard
  have h₂ := hconstant N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have h₃ := hfour N ((le_max_right _ _).trans hN)
  let W := max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))
  have hW : 1 ≤ W := le_max_left _ _
  have hprod : (F.card:ℝ)*(32*B) ≤ ((2:ℝ)^N)^σ := by
    calc
      _ ≤ ((2:ℝ)^N)^(σ/2)*((2:ℝ)^N)^(σ/2) :=
        mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hscale : 4 ≤ descriptorDerivativeScale N σ L := by
    exact h₃.trans (le_mul_of_one_le_right (by positivity) hW)
  have hlist : descriptorListScale B N σ L F ≤ descriptorDerivativeScale N σ L/4 := by
    have hh := mul_le_mul_of_nonneg_right hprod (show 0 ≤ W from zero_le_one.trans hW)
    change (F.card:ℝ)*B*(8*W) ≤ ((2:ℝ)^N)^σ*W/4
    nlinarith
  exact ⟨hscale,by linarith⟩

/-- Every geometric frequency condition in `JetStateFarData` follows from
the split gap and the largest descriptor length. -/
theorem eventual_far_split_scales (d : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L h t : ℕ, L ≤ N → h ≤ t →
      20*σ*(N:ℝ) ≤ (t:ℝ)-h → 2*(L:ℝ) ≤ (t:ℝ)-h →
      ∀ D : ℝ, 1 ≤ D → D ≤ descriptorDerivativeScale N σ L →
      h+6 ≤ t ∧ D ≤ ((2:ℝ)^N)^2 ∧
      D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ)) ∧
      D^2 ≤ (2:ℝ)^t*farMinimumLength d h ∧
      ((2:ℝ)^N)^(16*σ) ≤ (2:ℝ)^t*farMinimumLength d h ∧
      1 ≤ ((2:ℝ)^t/4)*farMinimumLength d h ∧
      D^2/(((2:ℝ)^t/4)*farMinimumLength d h) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₀,hlarge⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < 18*σ) 64
  refine ⟨N₀,?_⟩
  intro N hN L h t hLN hht hgap hlength D hD hDs
  let R := (2:ℝ)^N
  let gap : ℝ := (t:ℝ)-h
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hσN : 0 ≤ σ*(N:ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hrat := descriptorDerivativeScale_inverse_ratio N L hσ.le hgap
    (show (L:ℝ) ≤ gap/2+σ*(N:ℝ) by dsimp [gap]; linarith)
  have hratD : D^2/(2:ℝ)^gap ≤ R^(-18*σ) :=
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hD) hDs 2)
      (by positivity)).trans hrat
  have h64 : (64:ℝ) ≤ R^(18*σ) := hlarge N hN
  have h18 : R^(18*σ) ≤ (2:ℝ)^gap := by
    rw [show R^(18*σ) = (2:ℝ)^((N:ℝ)*(18*σ)) from
      (Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (18*σ)).symm]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [gap]
    nlinarith
  have hgap6 : (6:ℝ) ≤ gap := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
    convert h64.trans h18 using 1; norm_num
  have hht6 : h+6 ≤ t := by
    have hh : (h:ℝ)+6 ≤ t := by dsimp [gap] at hgap6; linarith
    exact_mod_cast hh
  have hsmall : R^(-18*σ) ≤ (64:ℝ)⁻¹ := by
    rw [show -18*σ = -(18*σ) by ring,Real.rpow_neg hRp.le]
    exact (inv_le_inv₀ (by positivity : 0 < R^(18*σ)) (by norm_num : (0:ℝ) < 64)).mpr h64
  have hband : D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ)) := by
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^gap)).mp (hratD.trans hsmall)
    have he : (2:ℝ)^((t:ℝ)-(h+6:ℕ)) = (2:ℝ)^gap/64 := by
      rw [Nat.cast_add,Nat.cast_ofNat,show (t:ℝ)-((h:ℝ)+6) = gap-6 by dsimp [gap]; ring,
        Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    nlinarith
  have hden : ((2:ℝ)^t/4)*farMinimumLength d h = ((d:ℝ)+1)*(2:ℝ)^gap := by
    unfold farMinimumLength
    rw [← Real.rpow_natCast (2:ℝ) t]
    calc
      _ = ((d:ℝ)+1)*((2:ℝ)^(t:ℝ)*(2:ℝ)^(-(h:ℝ))) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; rfl
  have hdenle : (2:ℝ)^gap ≤ ((2:ℝ)^t/4)*farMinimumLength d h := by
    rw [hden]
    exact le_mul_of_one_le_left (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hratioOne : R^(-18*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hDsquare : D^2 ≤ (2:ℝ)^gap :=
    (div_le_one (by positivity : 0 < (2:ℝ)^gap)).mp (hratD.trans hratioOne)
  have hlargeD : D^2 ≤ (2:ℝ)^t*farMinimumLength d h := by
    have hp : 0 ≤ (2:ℝ)^t*farMinimumLength d h := by unfold farMinimumLength; positivity
    exact (hDsquare.trans hdenle).trans (by linarith)
  have hfreq : R^(16*σ) ≤ (2:ℝ)^gap := by
    apply (Real.rpow_le_rpow_of_exponent_le hR (by linarith : 16*σ ≤ 18*σ)).trans h18
  have hfreqLarge : R^(16*σ) ≤ (2:ℝ)^t*farMinimumLength d h := by
    have hp : 0 ≤ (2:ℝ)^t*farMinimumLength d h := by unfold farMinimumLength; positivity
    exact (hfreq.trans hdenle).trans (by linarith)
  have hone : 1 ≤ ((2:ℝ)^t/4)*farMinimumLength d h :=
    (one_le_pow₀ hD).trans (hDsquare.trans hdenle)
  refine ⟨hht6,hDs.trans (descriptorDerivativeScale_le_square N L hσ.le hσ1 hLN),
    hband,hlargeD,hfreqLarge,hone,?_⟩
  exact ((div_le_div_of_nonneg_left (sq_nonneg D) (by positivity) hdenle).trans hratD).trans
    (Real.rpow_le_rpow_of_exponent_le hR (by linarith : -18*σ ≤ -16*σ))

end Falconer

end OAI
