import OAI.Combinatorics.BalancedRyser.Profiles.AnalyticDetection
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCoefficients
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetection
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileIdentifiability

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileIdentifiability

theorem power_series_ne_zero_ae {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw0 : ∀ i, 0 ≤ w i)
    (hw : Function.Injective w) (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), (∑' i, a i * z ^ w i) ≠ 0 := by
  have hn := exists_laplaceSeries_ne_zero a w ha hw hfinite hne
  have hz := Balanced.power_series_zero_null_of_laplace_nonzero a w ha hw0 hn
  simpa only [ae_iff, not_not] using hz

end Balanced.ProfileIdentifiability

namespace Balanced.ProfileDetectionBridge

noncomputable def planeTest (P : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)

noncomputable def dTest (x : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + Real.sqrt 2 * a.2)

noncomputable def cTest (x : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * ((a.2 : ℝ) - 1))

theorem d_visible_ae_ne (x P : ℕ × ℕ → ℝ)
    (hx : Summable x) (hP : Summable P) (hzero : ∀ j, x (0, j) = 0)
    (hvisible : ¬ ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), dTest x z ≠ planeTest P z := by
  have hc := ProfileCoefficients.summable_abs_shift_sub x P hx hP
    (fun a : ℕ × ℕ => (a.1 + 1, a.2)) ProfileCoefficients.shift_fst_injective
  have hne : ∃ a : ℕ × ℕ, x (a.1 + 1, a.2) - P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible ((ProfileCoefficients.d_invisibility_iff x P).mpr ⟨hzero, h⟩)
  have hdet := ProfileIdentifiability.power_series_ne_zero_ae
    (fun a : ℕ × ℕ => x (a.1 + 1, a.2) - P a) ProfileDetection.profileExponent
    hc ProfileDetection.profileExponent_nonneg ProfileDetection.profileExponent_injective
    ProfileDetection.profileExponent_finite_sublevel hne
  filter_upwards [hdet, ae_restrict_mem measurableSet_Ioo] with z hz hzone
  apply sub_ne_zero.mp
  change (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + Real.sqrt 2 * a.2)) -
    (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)) ≠ 0
  rw [ProfileCoefficients.original_d_transform_sub x P hx hP hzero
    (Real.sqrt_nonneg 2) hzone.1.le hzone.2.le]
  exact hz

theorem c_visible_ae_ne (x P : ℕ × ℕ → ℝ)
    (hx : Summable x) (hP : Summable P) (hzero : ∀ i, x (i, 0) = 0)
    (hvisible : ¬ ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)) :
    ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), cTest x z ≠ planeTest P z := by
  have hc := ProfileCoefficients.summable_abs_shift_sub x P hx hP
    (fun a : ℕ × ℕ => (a.1, a.2 + 1)) ProfileCoefficients.shift_snd_injective
  have hne : ∃ a : ℕ × ℕ, x (a.1, a.2 + 1) - P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible ((ProfileCoefficients.c_invisibility_iff x P).mpr ⟨hzero, h⟩)
  have hdet := ProfileIdentifiability.power_series_ne_zero_ae
    (fun a : ℕ × ℕ => x (a.1, a.2 + 1) - P a) ProfileDetection.profileExponent
    hc ProfileDetection.profileExponent_nonneg ProfileDetection.profileExponent_injective
    ProfileDetection.profileExponent_finite_sublevel hne
  filter_upwards [hdet, ae_restrict_mem measurableSet_Ioo] with z hz hzone
  apply sub_ne_zero.mp
  change (∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * ((a.2 : ℝ) - 1))) -
    (∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)) ≠ 0
  rw [ProfileCoefficients.original_c_transform_sub x P hx hP hzero
    (Real.sqrt_nonneg 2) hzone.1.le hzone.2.le]
  exact hz

theorem d_invisible_eq (x P : ℕ × ℕ → ℝ)
    (hinvisible : ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j))
    (z : ℝ) : dTest x z = planeTest P z := by
  obtain ⟨hzero, hc⟩ := (ProfileCoefficients.d_invisibility_iff x P).mp hinvisible
  unfold dTest planeTest
  rw [ProfileCoefficients.d_transform_reindex x hzero]
  apply tsum_congr
  intro a
  rw [sub_eq_zero.mp (hc a)]

theorem c_invisible_eq (x P : ℕ × ℕ → ℝ)
    (hinvisible : ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1))
    (z : ℝ) : cTest x z = planeTest P z := by
  obtain ⟨hzero, hc⟩ := (ProfileCoefficients.c_invisibility_iff x P).mp hinvisible
  unfold cTest planeTest
  rw [ProfileCoefficients.c_transform_reindex x hzero]
  apply tsum_congr
  intro a
  rw [sub_eq_zero.mp (hc a)]

end Balanced.ProfileDetectionBridge

end OAI
