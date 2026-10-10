import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel

noncomputable def interceptScale (R C0 : ℝ) : ℝ := |C0|/R
noncomputable def totalScale (R H C0 : ℝ) : ℝ := max H (interceptScale R C0)

noncomputable def primeWidth (R xi H C0 : ℝ) : ℝ :=
  min (xi*R) (R*H/totalScale R H C0)

noncomputable def modelLength (R xi H C0 : ℝ) : ℝ := H+xi*interceptScale R C0

theorem totalScale_pos (R H C0 : ℝ) (hH : 0 < H) : 0 < totalScale R H C0 :=
  hH.trans_le (le_max_left _ _)

theorem primeWidth_pos (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    0 < primeWidth R xi H C0 :=
  lt_min (mul_pos hxi hR) (div_pos (mul_pos hR hH) (totalScale_pos R H C0 hH))

theorem primeWidth_caps (R xi H C0 : ℝ) :
    primeWidth R xi H C0 ≤ xi*R ∧ primeWidth R xi H C0 ≤ R*H/totalScale R H C0 :=
  ⟨min_le_left _ _,min_le_right _ _⟩

theorem modelLength_bounds (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hxi1 : xi ≤ 1) (hH : 0 < H) :
    H ≤ modelLength R xi H C0 ∧ xi*totalScale R H C0 ≤ modelLength R xi H C0 := by
  have hc : 0 ≤ interceptScale R C0 := div_nonneg (abs_nonneg _) hR.le
  have hxiH := mul_le_mul_of_nonneg_right hxi1 hH.le
  constructor
  · dsimp [modelLength]
    nlinarith [mul_nonneg hxi hc]
  · rcases le_total H (interceptScale R C0) with h | h
    · rw [totalScale,max_eq_right h]
      dsimp [modelLength]
      linarith
    · rw [totalScale,max_eq_left h]
      dsimp [modelLength]
      nlinarith

theorem small_model_area (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) :
    primeWidth R xi H C0*modelLength R xi H C0 ≤ 2*xi*R*H := by
  have hT := totalScale_pos R H C0 hH
  have hc : 0 ≤ interceptScale R C0 := div_nonneg (abs_nonneg _) hR.le
  have hcT : interceptScale R C0 ≤ totalScale R H C0 := le_max_right _ _
  have hw0 := primeWidth_pos R xi H C0 hR hxi hH
  have hcap := primeWidth_caps R xi H C0
  have hfirst := mul_le_mul_of_nonneg_right hcap.1 hH.le
  have hsecond : primeWidth R xi H C0*interceptScale R C0 ≤ R*H := by
    have hmul := (le_div_iff₀ hT).mp hcap.2
    have hmono := mul_le_mul_of_nonneg_left hcT hw0.le
    linarith
  have hsecond' := mul_le_mul_of_nonneg_left hsecond hxi.le
  dsimp [modelLength]
  nlinarith

theorem primeWidth_lower (R xi H C0 : ℝ) (hR : 0 < R) (hxi : 0 < xi)
    (hxi1 : xi ≤ 1) (hH : 0 < H) :
    xi*R*H/totalScale R H C0 ≤ primeWidth R xi H C0 := by
  have hT := totalScale_pos R H C0 hH
  have hHT : H ≤ totalScale R H C0 := le_max_left _ _
  apply le_min
  · apply (div_le_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hHT (mul_pos hxi hR).le
    nlinarith
  · apply div_le_div_of_nonneg_right _ hT.le
    have hh := mul_le_mul_of_nonneg_right hxi1 (mul_pos hR hH).le
    nlinarith

theorem primeWidth_zero_intercept (R xi H : ℝ) (hR : 0 < R) (hxi1 : xi ≤ 1) (hH : 0 < H) :
    primeWidth R xi H 0 = xi*R := by
  have ht : totalScale R H 0 = H := by
    simp only [totalScale,interceptScale,abs_zero,zero_div,max_eq_left hH.le]
  rw [primeWidth,ht,mul_div_cancel_right₀ _ hH.ne']
  exact min_eq_left (by nlinarith)

theorem primeWidth_nonzero_intercept (R xi H C0 : ℝ) (hR : 0 < R) (hxi1 : xi ≤ 1)
    (hH : 0 < H) (hC : C0 ≠ 0) :
    primeWidth R xi H C0 = min (xi*R) (R^2*H/|C0|) := by
  have hc : 0 < interceptScale R C0 := div_pos (abs_pos.mpr hC) hR
  have he : R*H/interceptScale R C0 = R^2*H/|C0| := by
    dsimp [interceptScale]
    field_simp
  rcases le_total H (interceptScale R C0) with h | h
  · rw [primeWidth,totalScale,max_eq_right h,he]
  · have hRH : R ≤ R*H/interceptScale R C0 := (le_div_iff₀ hc).mpr (by nlinarith)
    have hxiR : xi*R ≤ R := by nlinarith
    rw [primeWidth,totalScale,max_eq_left h,mul_div_cancel_right₀ _ hH.ne',min_eq_left hxiR]
    exact (min_eq_left (hxiR.trans (hRH.trans_eq he))).symm

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel

noncomputable def modelLeft (R xi C0 : ℝ) : ℝ := min (C0/R) (C0/((1+xi)*R))
noncomputable def modelRight (R xi H C0 : ℝ) : ℝ := modelLeft R xi C0+modelLength R xi H C0

theorem reciprocal_bin_range (R xi C0 p : ℝ) (hR : 0 < R) (_hxi : 0 ≤ xi)
    (hp : R < p) (hpU : p ≤ (1+xi)*R) :
    min (C0/R) (C0/((1+xi)*R)) ≤ C0/p ∧ C0/p ≤ max (C0/R) (C0/((1+xi)*R)) := by
  have hpp : 0 < p := hR.trans hp
  have hu : 1/((1+xi)*R) ≤ 1/p := one_div_le_one_div_of_le hpp hpU
  have hl : 1/p ≤ 1/R := one_div_le_one_div_of_le hR hp.le
  rcases le_total 0 C0 with hC | hC
  · have h1 : C0/((1+xi)*R) ≤ C0/p := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu hC
    have h2 : C0/p ≤ C0/R := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hl hC
    exact ⟨(min_le_right _ _).trans h1,h2.trans (le_max_left _ _)⟩
  · have h1 : C0/p ≤ C0/((1+xi)*R) := by simpa only [mul_one_div] using mul_le_mul_of_nonpos_left hu hC
    have h2 : C0/R ≤ C0/p := by simpa only [mul_one_div] using mul_le_mul_of_nonpos_left hl hC
    exact ⟨(min_le_left _ _).trans h2,h1.trans (le_max_right _ _)⟩

theorem reciprocal_bin_spread (R xi C0 : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) :
    |C0/R-C0/((1+xi)*R)| ≤ xi*interceptScale R C0 := by
  have hden : 0 < (1+xi)*R := by positivity
  have he : C0/R-C0/((1+xi)*R) = C0*xi/((1+xi)*R) := by field_simp;ring
  rw [he,abs_div,abs_mul,abs_of_nonneg hxi,abs_of_pos hden]
  calc
    _ ≤ |C0| * xi/R := div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) hxi) hR (by nlinarith)
    _ = _ := by dsimp [interceptScale];ring

theorem moving_interval_enclosure (R xi H C0 p m : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hp : R < p) (hpU : p ≤ (1+xi)*R) (hm : C0/p ≤ m ∧ m < C0/p+H) :
    modelLeft R xi C0 ≤ m ∧ m < modelRight R xi H C0 := by
  have hr := reciprocal_bin_range R xi C0 p hR hxi hp hpU
  have hs := reciprocal_bin_spread R xi C0 hR hxi
  have hspread : max (C0/R) (C0/((1+xi)*R))-min (C0/R) (C0/((1+xi)*R)) ≤ xi*interceptScale R C0 := by
    rw [max_sub_min_eq_abs]
    simpa only [abs_sub_comm (C0/R) (C0/((1+xi)*R))] using hs
  refine ⟨hr.1.trans hm.1,?_⟩
  dsimp only [modelRight,modelLeft,modelLength]
  linarith [hm.2,hr.2]

noncomputable def modelIntegers (R xi H C0 : ℝ) : Finset ℤ :=
  Finset.Ico ⌈modelLeft R xi C0⌉ ⌈modelRight R xi H C0⌉

theorem mem_modelIntegers (R xi H C0 : ℝ) (m : ℤ) :
    m ∈ modelIntegers R xi H C0 ↔ modelLeft R xi C0 ≤ (m : ℝ) ∧ (m : ℝ) < modelRight R xi H C0 := by
  simp only [modelIntegers,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]

theorem moving_integer_mem (R xi H C0 p : ℝ) (m : ℤ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hp : R < p) (hpU : p ≤ (1+xi)*R) (hm : C0/p ≤ (m : ℝ) ∧ (m : ℝ) < C0/p+H) :
    m ∈ modelIntegers R xi H C0 :=
  (mem_modelIntegers R xi H C0 m).mpr (moving_interval_enclosure R xi H C0 p m hR hxi hp hpU hm)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
