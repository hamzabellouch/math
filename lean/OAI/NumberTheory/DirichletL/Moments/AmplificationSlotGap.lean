import OAI.NumberTheory.DirichletL.Moments.AmplificationEligibility

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

theorem eventually_scale_gap (b η ell : ℝ) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ b*Z^η < Z^ell := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually (eventually_gt_atTop b)
  filter_upwards [hg,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hh := mul_lt_mul_of_pos_right hz (Real.rpow_pos_of_pos hZ0 η)
  rwa [← Real.rpow_add hZ0,sub_add_cancel] at hh

theorem amplifier_not_dvd_slot (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell)
    (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ)) (hQN : (Ideal.absNorm Q:ℝ) ≤ b*Z^η) :
    ¬P∣Q := by
  intro hd
  have he := (prime_dvd_prime_iff_eq hP hQ).mp hd
  subst Q
  linarith

theorem amplifier_not_dvd_slot_product {ι : Type*} (S : Finset ι) (v : ι → Ideal O)
    (P : Ideal O) (hP : Prime P) (hv : ∀ i ∈ S,Prime (v i))
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell) (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ))
    (hN : ∀ i ∈ S,(Ideal.absNorm (v i):ℝ) ≤ b*Z^η) :
    ¬P∣∏ i ∈ S,v i := by
  apply hP.not_dvd_finsetProd
  intro i hi
  exact amplifier_not_dvd_slot P (v i) hP (hv i hi) Z ell η b hgap hPN (hN i hi)

theorem live_profile_norm_bound (W : ℝ → ℂ) (b Z z η : ℝ) (I : Ideal O)
    (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hz : z ≤ η)
    (hs : Function.support W ⊆ Set.Iic b)
    (hW : W ((Ideal.absNorm I:ℝ)/Z^z) ≠ 0) :
    (Ideal.absNorm I:ℝ) ≤ b*Z^η := by
  have hpow : 0 < Z^z := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have h := (div_le_iff₀ hpow).mp (hs hW)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hz) hb)

theorem eventually_live_slot_exclusion (b η ell : ℝ) (hb : 0 ≤ b) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ {ι : Type*} (S : Finset ι) (v : ι → Ideal O) (W : ι → ℝ → ℂ) (z : ι → ℝ),
      (∀ i ∈ S,Prime (v i)) → (∀ i ∈ S,z i ≤ η) →
      (∀ i ∈ S,Function.support (W i) ⊆ Set.Iic b) →
      (∀ i ∈ S,W i ((Ideal.absNorm (v i):ℝ)/Z^(z i)) ≠ 0) →
      ∀ P : Ideal O,Prime P → Z^ell ≤ (Ideal.absNorm P:ℝ) → ¬P∣∏ i ∈ S,v i := by
  filter_upwards [eventually_scale_gap b η ell hgap] with Z hZ
  intro ι S v W z hv hz hs hW P hP hPN
  exact amplifier_not_dvd_slot_product S v P hP hv Z ell η b hZ.2 hPN
    (fun i hi => live_profile_norm_bound (W i) b Z (z i) η (v i) hb hZ.1 (hz i hi) (hs i hi) (hW i hi))

end SevenEighths.CenteredMomentAmplificationSlotGap

end

end OAI
